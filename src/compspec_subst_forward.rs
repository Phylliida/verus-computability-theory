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
//  Strategy: structural induction on phi.
//  At each node, the checker's acceptance constrains result_enc.
//  We extract t = Var{te_final} from the iterate state and show
//  result_enc == encode(subst(phi, var, t)).
//
//  For t_set == 0 (var not found): result == phi, any t works.
//  For t_set != 0: te is the discovered t value.
//  ====================================================================

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
    //  Get concrete formulas from encodings
    let phi_f: Formula = choose|f: Formula| encode(f) == phi_enc;
    let result_f: Formula = choose|f: Formula| encode(f) == result_enc;
    lemma_decode_encode_formula(phi_f);
    lemma_decode_encode_formula(result_f);
    //  decode(phi_enc) == phi_f, decode(result_enc) == result_f
    //  encode(phi_f) == phi_enc, encode(result_f) == result_enc

    let phi = decode_formula(phi_enc);
    let result = decode_formula(result_enc);

    //  Use backward proof: for ANY t, check_subst_comp accepts (phi, subst(phi, var, t), var).
    //  The forward proof shows the checker ONLY accepts valid substitutions.
    //  We construct t from the checker's discovered state.

    //  Key insight: the backward proof shows check_subst_comp_backward(phi, var, t) for all t.
    //  For the forward direction, we show result == subst(phi, var, t) for a specific t.

    //  Strategy: use the backward proof with t = result's first var-position term.
    //  If var doesn't appear in phi, result == phi and any t works.
    //  If var appears, extract t from the first var position in result.

    //  Simple case: var not free in phi
    //  In this case, the checker verifies all terms match (no var positions).
    //  So result must structurally equal phi.

    //  For now, construct t based on phi structure and show the property.
    //  We use induction on phi_f (= phi).

    //  The checker processes (phi_enc, result_enc) and if it accepts with state (te, ts):
    //  - If ts == 0: all terms in phi had phi_term != var, so result == phi
    //    → choose t = Var{0} (or any), subst(phi, var, t) == phi
    //  - If ts != 0: te is the discovered substitution term
    //    → choose t = Var{te}, then result == subst(phi, var, t)

    //  The core proof: structural induction on phi showing the iterate constrains result.
    //  We use the backward walk as a COMPARISON: the iterate on (phi, result) must produce
    //  the same state transitions as the iterate on (phi, subst(phi, var, t)) for the right t.

    //  For now, use the inductive witness construction:
    let t = extract_subst_witness(phi_f, result_f, var);
    assert(result_f == subst(phi_f, var, t)) by {
        lemma_extract_witness_correct(phi_f, result_f, var, phi_enc, result_enc);
    }
}

//  ====================================================================
//  Witness extraction: given phi and result, find t such that
//  result == subst(phi, var, t).
//  ====================================================================

///  Extract the substitution term from a (phi, result) pair.
///  Walks phi looking for first occurrence of Var(var).
///  At that position in result, the term is t.
///  If var doesn't occur, returns Var{0} (arbitrary).
pub open spec fn extract_subst_witness(phi: Formula, result: Formula, var: nat) -> Term
    decreases phi,
{
    match phi {
        Formula::Eq { left, right } | Formula::In { left, right } => {
            match left {
                Term::Var { index } => if index == var {
                    //  Found var at left position — extract t from result
                    match result {
                        Formula::Eq { left: rl, .. } | Formula::In { left: rl, .. } => rl,
                        _ => Term::Var { index: 0 },
                    }
                } else {
                    //  Check right position
                    match right {
                        Term::Var { index: ri } => if ri == var {
                            match result {
                                Formula::Eq { right: rr, .. } | Formula::In { right: rr, .. } => rr,
                                _ => Term::Var { index: 0 },
                            }
                        } else {
                            Term::Var { index: 0 }  //  var not here
                        }
                    }
                }
            }
        },
        Formula::Not { sub } => extract_subst_witness(*sub, match result {
            Formula::Not { sub: rs } => *rs,
            _ => result,
        }, var),
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            let rl = match result {
                Formula::And { left: rl, .. } | Formula::Or { left: rl, .. }
                | Formula::Implies { left: rl, .. } | Formula::Iff { left: rl, .. } => *rl,
                _ => result,
            };
            let rr = match result {
                Formula::And { right: rr, .. } | Formula::Or { right: rr, .. }
                | Formula::Implies { right: rr, .. } | Formula::Iff { right: rr, .. } => *rr,
                _ => result,
            };
            let t_left = extract_subst_witness(*left, rl, var);
            let t_right = extract_subst_witness(*right, rr, var);
            //  Use left's witness if it found var, else right's
            if has_free_var(*left, var) { t_left } else { t_right }
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
            if v == var {
                Term::Var { index: 0 }  //  var is bound here, no substitution
            } else {
                let rs = match result {
                    Formula::Forall { sub: rs, .. } | Formula::Exists { sub: rs, .. } => *rs,
                    _ => result,
                };
                extract_subst_witness(*sub, rs, var)
            }
        },
    }
}

///  The extracted witness is correct: result == subst(phi, var, t).
///  Requires: the checker accepted (phi_enc, result_enc, var).
proof fn lemma_extract_witness_correct(
    phi: Formula, result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
)
    requires
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures ({
        let t = extract_subst_witness(phi, result, var);
        result == subst(phi, var, t)
    }),
    decreases phi,
{
    let t = extract_subst_witness(phi, result, var);

    //  Use backward proof: check_subst_comp accepts (phi, subst(phi, var, t), var)
    lemma_check_subst_comp_backward(phi, var, t);

    //  Both (phi, result) and (phi, subst(phi, var, t)) are accepted by the checker.
    //  Since the checker is a deterministic parallel walk that verifies structural
    //  equality up to substitution, and there's only one valid substitution result
    //  for a given (phi, var, t_enc), the results must be identical.

    //  This requires showing the checker is INJECTIVE on the second argument:
    //  for fixed (phi_enc, var), if check_subst_comp accepts both (phi_enc, r1, var)
    //  and (phi_enc, r2, var) with the same discovered t, then r1 == r2.

    //  TODO: Complete inductive proof
    //  For now, match on phi and prove each case
    match phi {
        Formula::Eq { left, right } => {
            lemma_forward_eq(phi, left, right, result, var, phi_enc, result_enc);
        },
        Formula::In { left, right } => {
            lemma_forward_in(phi, left, right, result, var, phi_enc, result_enc);
        },
        Formula::Not { sub } => {
            //  TODO
        },
        Formula::And { left, right } => {
            //  TODO
        },
        Formula::Or { left, right } => {
            //  TODO
        },
        Formula::Implies { left, right } => {
            //  TODO
        },
        Formula::Iff { left, right } => {
            //  TODO
        },
        Formula::Forall { var: v, sub } => {
            //  TODO
        },
        Formula::Exists { var: v, sub } => {
            //  TODO
        },
    }
}

///  Forward proof for Eq: if checker accepts (Eq(l,r), result, var),
///  then result == subst(Eq(l,r), var, t) for the extracted t.
proof fn lemma_forward_eq(
    phi: Formula, left: Term, right: Term,
    result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
)
    requires
        phi == (Formula::Eq { left, right }),
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures ({
        let t = extract_subst_witness(phi, result, var);
        result == subst(phi, var, t)
    }),
{
    //  TODO: implement
    //  1. Unfold check_subst_comp to iterate
    //  2. Show one step processes (phi, result)
    //  3. From acceptance: tags match → result has Eq tag
    //  4. From term checks: terms satisfy substitution property
    //  5. Reconstruct: result == Eq(subst_term(left, var, t), subst_term(right, var, t))
}

///  Forward proof for In: same as Eq but tag 1.
proof fn lemma_forward_in(
    phi: Formula, left: Term, right: Term,
    result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
)
    requires
        phi == (Formula::In { left, right }),
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures ({
        let t = extract_subst_witness(phi, result, var);
        result == subst(phi, var, t)
    }),
{
    //  TODO: implement (mirror of Eq)
}

} // verus!
