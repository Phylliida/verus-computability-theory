use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;
use crate::compspec_subst_forward_walk_binary_right::lemma_forward_binary_right_and_combine;

verus! {

///  Binary walk: matches on phi to get structural sub-terms for termination.
#[verifier::rlimit(5000)]
pub proof fn lemma_forward_walk_binary(
    phi: Formula,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
    tag: nat, el: nat, er: nat,
) -> (t: Term)
    requires
        tag >= 3, tag <= 6,
        el == encode(decode_formula(el)), er == encode(decode_formula(er)),
        encode(phi) == pair(tag, pair(el, er)),
        fuel >= subst_traversal_cost(decode_formula(el), var) + subst_traversal_cost(decode_formula(er), var),
        ({
            let tag_eq: nat = if unpair1(result_enc) == tag { 1nat } else { 0nat };
            let rl = unpair1(unpair2(result_enc));
            let rr = unpair2(unpair2(result_enc));
            unpair1(unpair2(
                compspec_iterate(check_subst_step(), fuel,
                    pair(pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)), pair(tag_eq, pair(te, ts))),
                    pair(pe, pair(re, var)))
            )) != 0
        }),
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi, 0nat,
{
    //  Match to get structural sub-terms for termination checker
    match phi {
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            //  Tag check
            if unpair1(result_enc) != tag {
                lemma_pair_surjective(result_enc);
                lemma_pair_surjective(unpair2(result_enc));
                let rl = unpair1(unpair2(result_enc));
                let rr = unpair2(unpair2(result_enc));
                lemma_iterate_valid_zero_contradiction(fuel,
                    pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)),
                    te, ts, pe, re, var);
            }

            lemma_pair_surjective(result_enc);
            lemma_pair_surjective(unpair2(result_enc));
            let rl = unpair1(unpair2(result_enc));
            let rr = unpair2(unpair2(result_enc));
            let rest_r = pair(pair(er, rr)+1, rest);

            //  IH on left (*left < phi — syntactic sub-term)
            lemma_decode_encode_formula(*left);
            lemma_decode_encode_formula(*right);
            let t_l = lemma_forward_walk_iterate(*left, rl, var,
                rest_r, te, ts, pe, re, fuel);

            //  Right IH + combine
            return lemma_forward_binary_right_and_combine(
                phi, *left, *right, tag, result_enc, var,
                rest, te, ts, pe, re, fuel,
                t_l, rl, rr);
        },
        //  Unreachable (phi must be a binary formula)
        _ => { return Term::Var { index: 0 }; },
    }
}

} // verus!
