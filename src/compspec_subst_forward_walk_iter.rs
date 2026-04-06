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

verus! {

///  Iterate-level forward walk — simple cases only (Eq/In/Not/Quantifier).
///  Binary cases are in a separate file to reduce Z3 context.
///  Uses `decreases (phi, 1nat)` so the binary helper can use `decreases (phi, 0nat)`.
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
            lemma_forward_step_not((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
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
            let el = encode(*left);
            let er = encode(*right);
            lemma_encode_is_pair(phi);
            lemma_unpair1_pair(tag, pair(el, er));
            lemma_unpair2_pair(tag, pair(el, er));
            //  Step + unfold to get post-step iterate
            crate::compspec_subst_forward_step_binary::lemma_forward_step_binary(
                (fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
            //  Delegate tag check + left IH + right IH + combine
            return crate::compspec_subst_forward_walk_binary::lemma_forward_walk_binary(
                phi, result_enc, var,
                rest, te, ts, pe, re, (fuel - 1) as nat,
                tag, el, er);
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
            let tag = formula_tag(phi);
            lemma_encode_is_pair(phi);
            lemma_unpair1_pair(tag, pair(v, encode(*sub)));
            lemma_unpair2_pair(tag, pair(v, encode(*sub)));
            lemma_unpair1_pair(v, encode(*sub));
            lemma_unpair2_pair(v, encode(*sub));
            lemma_forward_step_quant((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);
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
