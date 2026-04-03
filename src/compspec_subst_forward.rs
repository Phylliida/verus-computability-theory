use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_eq::lemma_forward_eq_constraints;
use crate::compspec_subst_forward_in::lemma_forward_in_constraints;

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
            lemma_forward_atomic(phi, left, right, 0nat, result, var, phi_enc, result_enc)
        },
        Formula::In { left, right } => {
            lemma_forward_atomic(phi, left, right, 1nat, result, var, phi_enc, result_enc)
        },
        //  Compound cases: TODO (not needed for atomic-only forward soundness)
        //  For compound formulas, the checker pushes sub-pairs and recurses.
        //  By induction on sub-formulas, each satisfies the property.
        //  The compound forward walk will be built in a future session.
        Formula::Not { sub } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
        Formula::And { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
        Formula::Or { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
        Formula::Implies { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
        Formula::Iff { left, right } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
        Formula::Forall { var: v, sub } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
        Formula::Exists { var: v, sub } => {
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t  //  PLACEHOLDER
        },
    }
}

///  Forward proof for atomic formulas (Eq or In).
///  Uses lemma_forward_eq/in_constraints for the checker-level constraints,
///  then constructs t at the Formula level.
proof fn lemma_forward_atomic(
    phi: Formula, left: Term, right: Term, tag: nat,
    result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
) -> (t: Term)
    requires
        tag <= 1,
        (tag == 0 ==> phi == (Formula::Eq { left, right })),
        (tag == 1 ==> phi == (Formula::In { left, right })),
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        result == subst(phi, var, t),
{
    match left { Term::Var { index: a } => {
    match right { Term::Var { index: b } => {

    //  phi_enc = pair(tag, pair(a, b))
    lemma_encode_is_pair(phi);
    lemma_encode_is_pair(result);

    //  result has same tag (from checker's tag match check)
    //  result_enc = pair(result_tag, pair(ra, rb))
    let result_tag = unpair1(result_enc);
    let ra = unpair1(unpair2(result_enc));
    let rb = unpair2(unpair2(result_enc));
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));

    //  Get constraints from the checker
    if tag == 0 {
        lemma_unpair1_pair(0nat, pair(a, b));
        //  For Eq: need result_enc == pair(0, pair(ra, rb))
        //  Tag match: result_tag == 0
        //  TODO: derive result_tag == 0 from checker acceptance
        //  For now, match on result to get the Eq structure
        match result {
            Formula::Eq { left: rl, right: rr } => {
                match rl { Term::Var { index: ra2 } => {
                match rr { Term::Var { index: rb2 } => {
                    lemma_unpair1_pair(0nat, pair(ra2, rb2));
                    lemma_unpair2_pair(0nat, pair(ra2, rb2));
                    lemma_unpair1_pair(ra2, rb2);
                    lemma_unpair2_pair(ra2, rb2);
                    lemma_forward_eq_constraints(a, b, ra2, rb2, var, phi_enc, result_enc);
                    //  Constraints: (a!=var → ra2==a), (b!=var → rb2==b), (both var → rb2==ra2)
                    let te = if a == var { ra2 } else { if b == var { rb2 } else { 0nat } };
                    let t = Term::Var { index: te };
                    //  Verify: result == subst(phi, var, t)
                    assert(result == subst(phi, var, t));
                    t
                }}
                }}
            },
            _ => {
                //  Tag mismatch: result is not Eq but phi is Eq
                //  The checker's tag check would reject this (TODO: formal contradiction)
                //  For now, backward proof serves as placeholder
                let t = Term::Var { index: 0 };
                lemma_check_subst_comp_backward(phi, var, t);
                t  //  PLACEHOLDER: tag mismatch contradiction needed
            }
        }
    } else {
        //  tag == 1 (In)
        match result {
            Formula::In { left: rl, right: rr } => {
                match rl { Term::Var { index: ra2 } => {
                match rr { Term::Var { index: rb2 } => {
                    lemma_unpair1_pair(1nat, pair(a, b));
                    lemma_unpair1_pair(1nat, pair(ra2, rb2));
                    lemma_unpair2_pair(1nat, pair(ra2, rb2));
                    lemma_unpair1_pair(ra2, rb2);
                    lemma_unpair2_pair(ra2, rb2);
                    lemma_forward_in_constraints(a, b, ra2, rb2, var, phi_enc, result_enc);
                    let te = if a == var { ra2 } else { if b == var { rb2 } else { 0nat } };
                    let t = Term::Var { index: te };
                    assert(result == subst(phi, var, t));
                    t
                }}
                }}
            },
            _ => {
                let t = Term::Var { index: 0 };
                lemma_check_subst_comp_backward(phi, var, t);
                t  //  PLACEHOLDER: tag mismatch contradiction needed
            }
        }
    }

    }}
    }}
}

} // verus!
