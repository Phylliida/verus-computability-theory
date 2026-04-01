use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_induction_steps::*;
use crate::compspec_subst_step_compose::*;

verus! {

//  ====================================================================
//  State tracking spec functions
//  ====================================================================

pub open spec fn subst_term_state(term: Term, var: nat, t_enc: nat, te: nat, ts: nat) -> (nat, nat) {
    match term {
        Term::Var { index } => if index == var {
            if ts == 0 { (t_enc, 1nat) } else { (te, ts) }
        } else { (te, ts) }
    }
}

pub open spec fn subst_state(f: Formula, var: nat, t_enc: nat, te: nat, ts: nat) -> (nat, nat)
    decreases f,
{
    match f {
        Formula::Eq { left, right } | Formula::In { left, right } => {
            let (te1, ts1) = subst_term_state(left, var, t_enc, te, ts);
            subst_term_state(right, var, t_enc, te1, ts1)
        },
        Formula::Not { sub } => subst_state(*sub, var, t_enc, te, ts),
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            let (te1, ts1) = subst_state(*left, var, t_enc, te, ts);
            subst_state(*right, var, t_enc, te1, ts1)
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } =>
            if v == var { (te, ts) } else { subst_state(*sub, var, t_enc, te, ts) },
    }
}

proof fn lemma_subst_state_invariant(f: Formula, var: nat, t_enc: nat, te: nat, ts: nat)
    requires ts == 0 || te == t_enc,
    ensures ({ let (te_out, ts_out) = subst_state(f, var, t_enc, te, ts); ts_out == 0 || te_out == t_enc }),
    decreases f,
{
    match f {
        Formula::Eq { .. } | Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_subst_state_invariant(*sub, var, t_enc, te, ts); },
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            lemma_subst_state_invariant(*left, var, t_enc, te, ts);
            let (te1, ts1) = subst_state(*left, var, t_enc, te, ts);
            lemma_subst_state_invariant(*right, var, t_enc, te1, ts1);
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
            if v != var { lemma_subst_state_invariant(*sub, var, t_enc, te, ts); }
        },
    }
}

//  ====================================================================
//  Backward traversal: valid stays nonzero, state matches subst_state.
//
//  Uses new atomic compose helpers for Eq/In (strengthened check).
//  Uses existing compound step helpers (unchanged by strengthening).
//
//  NOTE: For Eq/In, we use the dispatch equality (step == atomic_terms)
//  from the compose helpers, then use csi_chain to unfold one iterate step.
//  The Eq/In step result preserves valid != 0 but changes (te, ts).
//  For compound, the existing helpers give exact chain with preserved (te, ts).
//  ====================================================================

///  Backward traversal with exact state tracking via subst_state.
#[verifier::rlimit(1500)]
pub proof fn lemma_subst_traversal2(
    f: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        fuel >= subst_traversal_cost(f, var),
        ts == 0 || te == encode_term(t),
    ensures ({
        let (te2, ts2) = subst_state(f, var, encode_term(t), te, ts);
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f), encode(subst(f, var, t))) + 1, rest),
                 pair(1nat, pair(te, ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel - subst_traversal_cost(f, var)) as nat,
            pair(rest, pair(1nat, pair(te2, ts2))),
            pair(pe, pair(re, var)))
    }),
    decreases f,
{
    assert(fuel > 0) by { lemma_subst_traversal_cost_pos(f, var); }
    lemma_encode_is_pair(f);
    lemma_encode_is_pair(subst(f, var, t));
    lemma_subst_preserves_tag(f, var, t);

    match f {
        Formula::Eq { left, right } => {
            //  Old step_eq had exact ensures with preserved (te, ts).
            //  But with strengthened check, (te, ts) changes.
            //  Use the old step_eq for the iterate chain (its ensures is the OLD result),
            //  but then show the actual state matches subst_state.
            //
            //  Actually, step_eq's ensures says:
            //  iterate == iterate(fuel-1, pair(rest, pair(1, pair(te, ts))), s)
            //  This was correct for the SIMPLIFIED check. With the strengthened check,
            //  the actual result has pair(rest, pair(v, pair(te2, ts2))).
            //  step_eq's ensures is WRONG for the strengthened check.
            //
            //  So I cannot use step_eq. I need to unfold directly.
            //  Use csi_chain + compose helper.

            let entry = pair(encode(f), encode(subst(f, var, t)));
            let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
            let s = pair(pe, pair(re, var));

            //  One step: iterate(fuel) = iterate(fuel-1, step_result, s)
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, s);
            let step_input = pair((fuel - 1) as nat, pair(acc, s));
            let step_result = eval_comp(check_subst_step(), step_input);

            //  Compose: step_result has rest + valid nonzero + step == atomic
            lemma_subst_atomic_eq_result(left, right, var, t, rest, 1, te, ts, pe, re);

            //  step_result == pair(rest, pair(v, state)) via pair surjectivity
            lemma_pair_surjective(step_result);
            lemma_pair_surjective(unpair2(step_result));

            //  For subst_traversal_cost(Eq, var) == 1, fuel-cost == fuel-1
            //  So ensures: iterate(fuel, acc, s) == iterate(fuel-1, step_result, s)
            //  And step_result == pair(rest, pair(v, state))
            //  Need: step_result == pair(rest, pair(1, pair(te2, ts2)))
            //  This requires v == 1 and state == pair(te2, ts2)
            //  For now, just assert the result equals what we need
        },
        Formula::In { left, right } => {
            let entry = pair(encode(f), encode(subst(f, var, t)));
            let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
            let s = pair(pe, pair(re, var));
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, s);
            lemma_subst_atomic_in_result(left, right, var, t, rest, 1, te, ts, pe, re);
            let step_result = eval_comp(check_subst_step(), pair((fuel - 1) as nat, pair(acc, s)));
            lemma_pair_surjective(step_result);
            lemma_pair_surjective(unpair2(step_result));
        },
        Formula::Not { sub } => {
            step_not(f, *sub, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal2(*sub, var, t, rest, te, ts, pe, re, (fuel - 1) as nat);
        },
        Formula::And { left, right } => {
            step_binary(f, *left, *right, 3, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_state_invariant(*left, var, encode_term(t), te, ts);
            let (te1, ts1) = subst_state(*left, var, encode_term(t), te, ts);
            lemma_subst_traversal2(*left, var, t,
                pair(pair(encode(*right), encode(subst(*right, var, t))) + 1, rest),
                te, ts, pe, re, (fuel - 1) as nat);
            lemma_subst_traversal2(*right, var, t, rest, te1, ts1, pe, re,
                (fuel - 1 - subst_traversal_cost(*left, var)) as nat);
        },
        Formula::Or { left, right } => {
            step_binary(f, *left, *right, 4, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_state_invariant(*left, var, encode_term(t), te, ts);
            let (te1, ts1) = subst_state(*left, var, encode_term(t), te, ts);
            lemma_subst_traversal2(*left, var, t,
                pair(pair(encode(*right), encode(subst(*right, var, t))) + 1, rest),
                te, ts, pe, re, (fuel - 1) as nat);
            lemma_subst_traversal2(*right, var, t, rest, te1, ts1, pe, re,
                (fuel - 1 - subst_traversal_cost(*left, var)) as nat);
        },
        Formula::Implies { left, right } => {
            step_binary(f, *left, *right, 5, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_state_invariant(*left, var, encode_term(t), te, ts);
            let (te1, ts1) = subst_state(*left, var, encode_term(t), te, ts);
            lemma_subst_traversal2(*left, var, t,
                pair(pair(encode(*right), encode(subst(*right, var, t))) + 1, rest),
                te, ts, pe, re, (fuel - 1) as nat);
            lemma_subst_traversal2(*right, var, t, rest, te1, ts1, pe, re,
                (fuel - 1 - subst_traversal_cost(*left, var)) as nat);
        },
        Formula::Iff { left, right } => {
            step_binary(f, *left, *right, 6, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_state_invariant(*left, var, encode_term(t), te, ts);
            let (te1, ts1) = subst_state(*left, var, encode_term(t), te, ts);
            lemma_subst_traversal2(*left, var, t,
                pair(pair(encode(*right), encode(subst(*right, var, t))) + 1, rest),
                te, ts, pe, re, (fuel - 1) as nat);
            lemma_subst_traversal2(*right, var, t, rest, te1, ts1, pe, re,
                (fuel - 1 - subst_traversal_cost(*left, var)) as nat);
        },
        Formula::Forall { var: v, sub } => {
            if v == var {
                step_forall_bound(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
            } else {
                step_forall_free(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal2(*sub, var, t, rest, te, ts, pe, re, (fuel - 1) as nat);
            }
        },
        Formula::Exists { var: v, sub } => {
            if v == var {
                step_exists_bound(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
            } else {
                step_exists_free(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal2(*sub, var, t, rest, te, ts, pe, re, (fuel - 1) as nat);
            }
        },
    }
}

} // verus!
