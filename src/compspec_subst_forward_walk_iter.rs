use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_forward_eq_iter_tag::{lemma_forward_eq_tag_iter, lemma_forward_in_tag_iter};
use crate::compspec_subst_forward_walk_atomic::lemma_forward_atomic_eq_iter;
use crate::compspec_subst_forward_walk_atomic_in::lemma_forward_atomic_in_iter;
use crate::compspec_subst_forward_step_not::lemma_forward_step_not;
use crate::compspec_subst_forward_step_quant::lemma_forward_step_quant;
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;
use crate::compspec_subst_forward_binary_unfold::lemma_binary_step_unfold;

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
    decreases phi, 1nat,
{
    hide(compspec_iterate);
    let phi_enc = encode(phi);
    let acc0 = pair(pair(pair(phi_enc, result_enc) + 1, rest), pair(1nat, pair(te, ts)));
    let input = pair(pe, pair(re, var));

    match phi {
        Formula::Eq { left, right } => {
            lemma_subst_traversal_cost_pos(phi, var);
            lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_forward_eq_tag_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel);
            return lemma_forward_atomic_eq_iter(left, right, result_enc, var,
                rest, te, ts, pe, re, fuel);
        },
        Formula::In { left, right } => {
            lemma_subst_traversal_cost_pos(phi, var);
            lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_forward_in_tag_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel);
            return lemma_forward_atomic_in_iter(left, right, result_enc, var,
                rest, te, ts, pe, re, fuel);
        },
        Formula::Not { sub } => {
            lemma_unpair1_pair(2nat, encode(*sub));
            lemma_unpair2_pair(2nat, encode(*sub));
            assert(unpair1(unpair2(
                compspec_iterate(check_subst_step(), (fuel - 1) as nat,
                    pair(pair(pair(encode(*sub), unpair2(result_enc)) + 1, rest),
                         pair(if unpair1(result_enc) == 2 { 1nat } else { 0nat }, pair(te, ts))),
                    input)
            )) != 0) by {
                reveal(compspec_iterate);
                lemma_forward_step_not((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
                lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
            };
            if unpair1(result_enc) != 2 {
                lemma_iterate_valid_zero_contradiction(
                    (fuel-1) as nat, pair(pair(encode(*sub), unpair2(result_enc))+1, rest),
                    te, ts, pe, re, var);
            }
            let t = lemma_forward_walk_iterate(*sub, unpair2(result_enc), var,
                rest, te, ts, pe, re, (fuel-1) as nat);
            lemma_pair_surjective(result_enc);
            return t;
        },
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            let tag = formula_tag(phi);
            lemma_encode_is_pair(phi);
            lemma_unpair1_pair(tag, pair(encode(*left), encode(*right)));
            lemma_unpair2_pair(tag, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(encode(*left), encode(*right));
            lemma_unpair2_pair(encode(*left), encode(*right));
            lemma_subst_traversal_cost_pos(phi, var);

            //  Step + unfold + tag (isolated Z3 context)
            lemma_binary_step_unfold(phi, result_enc, var, rest, te, ts, pe, re, fuel);

            lemma_pair_surjective(result_enc);
            lemma_pair_surjective(unpair2(result_enc));
            let rl = unpair1(unpair2(result_enc));
            let rr = unpair2(unpair2(result_enc));

            //  Left IH
            let t_l = lemma_forward_walk_iterate(*left, rl, var,
                pair(pair(encode(*right), rr)+1, rest), te, ts, pe, re, (fuel-1) as nat);

            return crate::compspec_subst_forward_walk_binary::lemma_forward_walk_binary(
                phi, t_l, result_enc, var,
                rest, te, ts, pe, re, (fuel-1) as nat,
                tag, rl, rr);
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
            let tag = formula_tag(phi);
            lemma_encode_is_pair(phi);
            lemma_unpair1_pair(tag, pair(v, encode(*sub)));
            lemma_unpair2_pair(tag, pair(v, encode(*sub)));
            lemma_unpair1_pair(v, encode(*sub));
            lemma_unpair2_pair(v, encode(*sub));
            assert(eval_comp(check_subst_step(), pair((fuel - 1) as nat, pair(acc0, input)))
                == ({
                    let tag_eq: nat = if unpair1(result_enc) == tag { 1nat } else { 0nat };
                    if v == var {
                        let node_eq: nat = if phi_enc == result_enc { 1nat } else { 0nat };
                        pair(rest, pair(if tag_eq != 0 && node_eq != 0 { 1nat } else { 0nat }, pair(te, ts)))
                    } else {
                        let bound_eq: nat = if v == unpair1(unpair2(result_enc)) { 1nat } else { 0nat };
                        pair(
                            pair(pair(encode(*sub), unpair2(unpair2(result_enc))) + 1, rest),
                            pair(if tag_eq != 0 && bound_eq != 0 { 1nat } else { 0nat }, pair(te, ts)))
                    }
                })) by {
                reveal(compspec_iterate);
                lemma_forward_step_quant((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
            };
            assert(unpair1(unpair2(
                compspec_iterate(check_subst_step(), (fuel - 1) as nat,
                    eval_comp(check_subst_step(), pair((fuel - 1) as nat, pair(acc0, input))),
                    input)
            )) != 0) by {
                reveal(compspec_iterate);
                lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
            };
            if v == var {
                if unpair1(result_enc) != tag || phi_enc != result_enc {
                    lemma_iterate_valid_zero_contradiction(
                        (fuel-1) as nat, rest, te, ts, pe, re, var);
                }
                return if ts != 0 { Term::Var { index: te } } else { Term::Var { index: 0 } };
            } else {
                let rse = unpair2(unpair2(result_enc));
                if unpair1(result_enc) != tag || v != unpair1(unpair2(result_enc)) {
                    lemma_iterate_valid_zero_contradiction(
                        (fuel-1) as nat, pair(pair(encode(*sub), rse)+1, rest),
                        te, ts, pe, re, var);
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
