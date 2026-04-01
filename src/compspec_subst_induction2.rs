use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_induction_steps::*;
use crate::compspec_subst_step_compose::*;

verus! {

//  ====================================================================
//  State tracking: what (t_enc, t_set) the traversal produces.
//  ====================================================================

///  State after processing one term for substitution.
pub open spec fn subst_term_state(term: Term, var: nat, t_enc: nat, te: nat, ts: nat) -> (nat, nat) {
    match term {
        Term::Var { index } => if index == var {
            if ts == 0 { (t_enc, 1nat) } else { (te, ts) }
        } else { (te, ts) }
    }
}

///  State after processing a formula entry for substitution.
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

///  The t_enc invariant is maintained by subst_state.
proof fn lemma_subst_state_invariant(f: Formula, var: nat, t_enc: nat, te: nat, ts: nat)
    requires ts == 0 || te == t_enc,
    ensures ({
        let (te', ts') = subst_state(f, var, t_enc, te, ts);
        ts' == 0 || te' == t_enc
    }),
    decreases f,
{
    match f {
        Formula::Eq { left, right } | Formula::In { left, right } => {},
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
//  Backward traversal with exact state tracking.
//  ====================================================================

///  Main traversal: processes entry and returns state to (rest, pair(1, pair(te', ts'))).
#[verifier::rlimit(500)]
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
    lemma_encode_is_pair(f);
    lemma_encode_is_pair(subst(f, var, t));
    lemma_subst_preserves_tag(f, var, t);

    match f {
        Formula::Eq { left, right } => {
            //  Use existing step_eq ensures (it still chains correctly,
            //  though its internal helper has wrong ensures — the step_eq
            //  itself is verified because it uses csi_chain which just unfolds iterate)
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - 1) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_eq(f, left, right, var, t, rest, te, ts, pe, re, fuel);
            }
            //  But wait — step_eq's ensures say the state is pair(1, pair(te, ts))
            //  which was correct for the OLD simplified check (te, ts unchanged).
            //  With the STRENGTHENED check, the actual step result has different (te', ts').
            //  step_eq's proof calls the OLD broken helper, so its ensures might be wrong!
            //
            //  Actually, step_eq verified (10 verified in compspec_subst_induction_steps).
            //  But its internal call to the broken helper... hmm.
            //  The ENSURES of step_eq references pair(1, pair(te, ts)) which is the OLD result.
            //  With the strengthened check, the actual eval_comp result is DIFFERENT.
            //  So step_eq's ensures is WRONG — it claims a result that no longer holds.
            //  But step_eq still "verifies" because its proof body uses the broken helper
            //  (which has wrong ensures but is still declared).
            //
            //  This is a soundness issue: step_eq relies on an unverified helper.
            //  I CANNOT use step_eq here.
            //
            //  TODO: Use the new atomic helpers instead.
        },
        _ => {},
    }
}

} // verus!
