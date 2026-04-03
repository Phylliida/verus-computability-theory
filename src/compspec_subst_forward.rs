use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_induction2::{subst_state, subst_term_state};

verus! {

//  ====================================================================
//  Forward soundness: check_subst_comp accepts → result is valid subst.
//
//  Strategy: structural induction on phi. At each node, the checker's
//  acceptance constrains result_enc. We construct t = Var{te_final}
//  from the checker's discovered state and show
//  result_enc == encode(subst(phi, var, t)).
//  ====================================================================

///  Forward soundness entry point.
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

    //  Unfold check_subst_comp to iterate (fuel = phi_enc + 1)
    lemma_check_subst_unfold(phi_enc, result_enc, var);

    //  Forward walk by structural induction
    let t = lemma_forward_walk(phi, result, var, phi_enc, result_enc);
    assert(result == subst(phi, var, t));
    //  Since decode(phi_enc) == phi and decode(result_enc) == result:
    assert(decode_formula(result_enc) == subst(decode_formula(phi_enc), var, t));
}

///  Forward walk: structural induction on phi.
///  Returns the witness t such that result == subst(phi, var, t).
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
    //  The checker does phi_enc + 1 iterations of check_subst_step.
    //  For each formula variant, we analyze the checks.

    //  Use backward proof: for any t, the checker accepts (phi, subst(phi, var, t)).
    //  The backward traversal gives the exact iterate behavior.
    //  For the forward proof, we use the backward result as a TEMPLATE:
    //  the checker's acceptance constrains result to be a valid substitution.

    match phi {
        Formula::Eq { left, right } => {
            lemma_forward_atomic_eq(phi, left, right, result, var, phi_enc, result_enc)
        },
        Formula::In { left, right } => {
            lemma_forward_atomic_in(phi, left, right, result, var, phi_enc, result_enc)
        },
        Formula::Not { sub } => {
            //  The checker pushes (sub, result_sub).
            //  By induction: sub_result == subst(sub, var, t).
            //  result == Not(sub_result) == subst(Not(sub), var, t).
            //  TODO: implement compound case
            let t = Term::Var { index: 0 };
            //  PLACEHOLDER: use backward + forward walk for Not
            lemma_check_subst_comp_backward(phi, var, t);
            t
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

///  Forward proof for Eq(left, right).
///  The checker does 1 step checking tags + terms, then empty-stack stability.
///  If accepted: result has Eq structure with compatible terms.
proof fn lemma_forward_atomic_eq(
    phi: Formula, left: Term, right: Term,
    result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
) -> (t: Term)
    requires
        phi == (Formula::Eq { left, right }),
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        result == subst(phi, var, t),
{
    //  The checker accepted. By the backward proof, for the RIGHT t,
    //  the checker also accepts (phi, subst(phi, var, t)).
    //  For Eq, the checker does exactly 1 meaningful step that checks
    //  tag match + term compatibility.
    //
    //  Key insight: match on left and right to determine var occurrences.
    //  The checker's acceptance constrains result's terms.

    match left { Term::Var { index: a } => {
    match right { Term::Var { index: b } => {

    //  result must be Eq (from tag match):
    //  The checker checks unpair1(phi_enc) == unpair1(result_enc).
    //  phi has tag 0 (Eq). If checker accepts, result_enc has tag 0.
    //  Since result is a valid Formula encoding with tag 0, result = Eq(Var(a'), Var(b')).

    match result {
        Formula::Eq { left: rl, right: rr } => {
            match rl { Term::Var { index: ra } => {
            match rr { Term::Var { index: rb } => {

            //  Now construct t based on which terms are var:
            if a == var {
                //  left is the substituted variable
                let t = Term::Var { index: ra };  //  t comes from result's left term
                //  Need: result == subst(Eq(Var(a), Var(b)), var, t)
                //  subst gives: Eq(t, if b == var then t else Var(b))
                //  So need: Var(rb) == if b == var then t else Var(b)

                if b == var {
                    //  Both positions have var → both should map to same t
                    //  Checker verifies rb == ra (second term verify against discovered te)
                    //  Use backward proof as witness that this is correct
                    lemma_check_subst_comp_backward(phi, var, t);
                    //  Now: check_subst_comp(phi_enc, encode(subst(phi,var,t)), var) != 0
                    //  subst(phi, var, t) = Eq(Var(ra), Var(ra))
                    //  If result != subst(phi, var, t), the checker would need to produce
                    //  the same valid for two different result_encs, which we show below.
                    //  For now, we verify with backward + result structure.
                    assert(subst(phi, var, t) == Formula::Eq {
                        left: Term::Var { index: ra },
                        right: Term::Var { index: ra },
                    });
                    //  TODO: show rb == ra from checker constraint
                    //  This requires analyzing the per-term check
                    t
                } else {
                    //  Only left has var
                    //  Checker verifies rb == b (non-var term must match)
                    //  Use backward proof
                    lemma_check_subst_comp_backward(phi, var, t);
                    assert(subst(phi, var, t) == Formula::Eq {
                        left: t,
                        right: Term::Var { index: b },
                    });
                    //  TODO: show rb == b from checker constraint
                    t
                }
            } else if b == var {
                //  Only right has var
                let t = Term::Var { index: rb };
                lemma_check_subst_comp_backward(phi, var, t);
                assert(subst(phi, var, t) == Formula::Eq {
                    left: Term::Var { index: a },
                    right: t,
                });
                //  TODO: show ra == a from checker constraint
                t
            } else {
                //  Neither position has var → result must equal phi
                let t = Term::Var { index: 0 };
                //  Checker verifies: ra == a and rb == b
                //  Use backward proof
                lemma_check_subst_comp_backward(phi, var, t);
                //  subst(phi, var, Var(0)) == phi (since var not in phi)
                assert(subst(phi, var, t) == phi);
                //  TODO: show ra == a and rb == b from checker constraint
                t
            }

            }}  //  match rr
            }}  //  match rl
        },
        //  result has non-Eq structure: contradiction with checker acceptance
        //  (checker requires tag match, phi has tag 0 = Eq)
        _ => {
            //  TODO: derive contradiction from tag mismatch
            let t = Term::Var { index: 0 };
            lemma_check_subst_comp_backward(phi, var, t);
            t
        }
    }

    }}  //  match right
    }}  //  match left
}

///  Forward proof for In(left, right). Mirror of Eq with tag 1.
proof fn lemma_forward_atomic_in(
    phi: Formula, left: Term, right: Term,
    result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
) -> (t: Term)
    requires
        phi == (Formula::In { left, right }),
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        result == subst(phi, var, t),
{
    //  TODO: mirror of Eq case
    let t = Term::Var { index: 0 };
    lemma_check_subst_comp_backward(phi, var, t);
    t
}

} // verus!
