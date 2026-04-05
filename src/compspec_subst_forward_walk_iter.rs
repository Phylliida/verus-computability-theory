use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_induction2::*;
use crate::compspec_subst_forward_eq_iter_tag::*;
use crate::compspec_subst_forward_walk_atomic::lemma_forward_atomic_eq_iter;
use crate::compspec_subst_forward_walk_atomic_in::lemma_forward_atomic_in_iter;
use crate::compspec_subst_forward_step_not::lemma_forward_step_not;
use crate::compspec_subst_forward_step_binary::lemma_forward_step_binary;
use crate::compspec_subst_forward_step_quant::lemma_forward_step_quant;
use crate::compspec_subst_forward_binary_combine::lemma_binary_combine;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

#[verifier::rlimit(5000)]
pub proof fn lemma_forward_walk_iterate(
    phi: Formula, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
) -> (t: Term)
    requires
        fuel >= subst_traversal_cost(phi, var),
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(phi), result_enc) + 1, rest),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0,
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi,
{
    let phi_enc = encode(phi);
    let acc0 = pair(pair(pair(phi_enc, result_enc) + 1, rest), pair(1nat, pair(te, ts)));
    let input = pair(pe, pair(re, var));
    lemma_subst_traversal_cost_pos(phi, var);
    lemma_encode_is_pair(phi);

    match phi {
        Formula::Eq { left, right } => {
            lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_forward_eq_tag_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel);
            return lemma_forward_atomic_eq_iter(left, right, result_enc, var,
                rest, te, ts, pe, re, fuel);
        },
        Formula::In { left, right } => {
            lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_forward_in_tag_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel);
            return lemma_forward_atomic_in_iter(left, right, result_enc, var,
                rest, te, ts, pe, re, fuel);
        },
        Formula::Not { sub } => {
            lemma_unpair1_pair(2nat, encode(*sub));
            lemma_unpair2_pair(2nat, encode(*sub));
            lemma_forward_step_not((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
            if unpair1(result_enc) != 2 {
                let se = pair(encode(*sub), unpair2(result_enc));
                lemma_subst_valid_zero_stable((fuel-1) as nat, pair(se+1, rest), te, ts, pe, re, var);
                lemma_unpair2_pair(pair(se+1, rest), pair(0nat, pair(te, ts)));
                lemma_unpair1_pair(0nat, pair(te, ts));
            }
            let t = lemma_forward_walk_iterate(*sub, unpair2(result_enc), var,
                rest, te, ts, pe, re, (fuel-1) as nat);
            lemma_pair_surjective(result_enc);
            return t;
        },
        //  Binary: or-pattern to share code for And/Or/Implies/Iff
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            let tag = formula_tag(phi);
            lemma_unpair1_pair(tag, pair(encode(*left), encode(*right)));
            lemma_unpair2_pair(tag, pair(encode(*left), encode(*right)));
            lemma_forward_step_binary((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
            //  Tag contradiction
            if unpair1(result_enc) != tag {
                let pc = unpair2(phi_enc); let rc = unpair2(result_enc);
                let ns = pair(pair(unpair1(pc),unpair1(rc))+1, pair(pair(unpair2(pc),unpair2(rc))+1, rest));
                lemma_subst_valid_zero_stable((fuel-1) as nat, ns, te, ts, pe, re, var);
                lemma_unpair2_pair(ns, pair(0nat, pair(te, ts)));
                lemma_unpair1_pair(0nat, pair(te, ts));
            }
            lemma_pair_surjective(result_enc);
            lemma_pair_surjective(unpair2(result_enc));
            let rl = unpair1(unpair2(result_enc));
            let rr = unpair2(unpair2(result_enc));
            let rest_r = pair(pair(encode(*right), rr)+1, rest);
            //  IH left
            let t_l = lemma_forward_walk_iterate(*left, rl, var,
                rest_r, te, ts, pe, re, (fuel-1) as nat);
            //  Backward decomposition
            lemma_subst_state_invariant(*left, var, encode_term(t_l), te, ts);
            let (te_l, ts_l) = subst_state(*left, var, encode_term(t_l), te, ts);
            lemma_subst_traversal2(*left, var, t_l, rest_r, te, ts, pe, re, (fuel-1) as nat);
            //  IH right
            let fuel_r = ((fuel-1) as nat - subst_traversal_cost(*left, var)) as nat;
            let t_r = lemma_forward_walk_iterate(*right, rr, var,
                rest, te_l, ts_l, pe, re, fuel_r);
            //  Combine
            lemma_subst_preserves_tag(phi, var, t_l);
            lemma_subst_preserves_tag(phi, var, t_r);
            return lemma_binary_combine(phi, *left, *right, tag, result_enc, var, te, ts,
                t_l, t_r, rl, rr, te_l, ts_l);
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
            let tag = formula_tag(phi);
            lemma_unpair1_pair(tag, pair(v, encode(*sub)));
            lemma_unpair2_pair(tag, pair(v, encode(*sub)));
            lemma_unpair1_pair(v, encode(*sub));
            lemma_unpair2_pair(v, encode(*sub));
            lemma_forward_step_quant((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
            if v == var {
                let tag_eq: nat = if unpair1(result_enc) == tag { 1nat } else { 0nat };
                let node_eq: nat = if phi_enc == result_enc { 1nat } else { 0nat };
                if tag_eq * node_eq == 0nat {
                    lemma_subst_valid_zero_stable((fuel-1) as nat, rest, te, ts, pe, re, var);
                    lemma_unpair2_pair(rest, pair(0nat, pair(te, ts)));
                    lemma_unpair1_pair(0nat, pair(te, ts));
                }
                return if ts != 0 { Term::Var { index: te } } else { Term::Var { index: 0 } };
            } else {
                let tag_eq: nat = if unpair1(result_enc) == tag { 1nat } else { 0nat };
                let bound_eq: nat = if v == unpair1(unpair2(result_enc)) { 1nat } else { 0nat };
                let rse = unpair2(unpair2(result_enc));
                let se = pair(encode(*sub), rse);
                if tag_eq * bound_eq == 0nat {
                    lemma_subst_valid_zero_stable((fuel-1) as nat, pair(se+1, rest), te, ts, pe, re, var);
                    lemma_unpair2_pair(pair(se+1, rest), pair(0nat, pair(te, ts)));
                    lemma_unpair1_pair(0nat, pair(te, ts));
                }
                let t = lemma_forward_walk_iterate(*sub, rse, var,
                    rest, te, ts, pe, re, (fuel-1) as nat);
                lemma_pair_surjective(result_enc);
                lemma_pair_surjective(unpair2(result_enc));
                return t;
            }
        },
    }
}

} // verus!
