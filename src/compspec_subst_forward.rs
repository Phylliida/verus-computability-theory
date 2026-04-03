use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_atomic::*;

verus! {

///  Forward soundness entry point.
///  If check_subst_comp accepts, result_enc encodes subst(phi, var, t) for some t.
pub proof fn lemma_check_subst_comp_forward(phi_enc: nat, result_enc: nat, var: nat)
    requires
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
        exists|f: Formula| encode(f) == phi_enc,
        exists|f: Formula| encode(f) == result_enc,
    ensures
        exists|t: Term| decode_formula(result_enc) == subst(decode_formula(phi_enc), var, t),
{
    let phi: Formula = choose|f: Formula| encode(f) == phi_enc;
    let result: Formula = choose|f: Formula| encode(f) == result_enc;
    lemma_decode_encode_formula(phi);
    lemma_decode_encode_formula(result);

    let t = lemma_forward_walk(phi, result, var, phi_enc, result_enc);
    assert(decode_formula(result_enc) == subst(decode_formula(phi_enc), var, t));
}

///  Forward walk: structural induction on phi.
proof fn lemma_forward_walk(
    phi: Formula, result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
) -> (t: Term)
    requires
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        result == subst(phi, var, t),
    decreases phi,
{
    match phi {
        Formula::Eq { left, right } => {
            lemma_forward_atomic_eq(phi, left, right, result, var, phi_enc, result_enc)
        },
        Formula::In { left, right } => {
            lemma_forward_atomic_in(phi, left, right, result, var, phi_enc, result_enc)
        },
        //  Compound cases: structural induction via checker's push/recurse pattern.
        //  TODO: implement these cases (checker pushes sub-pairs, by IH subs satisfy property)
        Formula::Not { sub } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
        Formula::And { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t
        },
        Formula::Or { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t
        },
        Formula::Implies { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t
        },
        Formula::Iff { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t
        },
        Formula::Forall { var: v, sub } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t
        },
        Formula::Exists { var: v, sub } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t
        },
    }
}

} // verus!
