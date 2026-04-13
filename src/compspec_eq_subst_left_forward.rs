use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::proof_system::*;
use crate::compspec_eq_subst_axiom_forward::eq_subst_left_structure;
use crate::compspec_eq_subst_pair_forward::lemma_check_eq_subst_pair_forward;
use crate::compspec_eq_subst_forward::{
    extract_phi, lemma_extract_phi_subst_left, lemma_extract_phi_subst_right, max_var,
};

verus! {

///  Forward soundness for eq_subst_left checker.
#[verifier::rlimit(5000)]
pub proof fn lemma_check_eq_subst_left_forward(enc: nat)
    requires
        eval_comp(check_axiom_eq_subst_left(), enc) != 0,
        exists|f: Formula| encode(f) == enc,
    ensures is_axiom_eq_subst_left(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);

    let outer_f: Formula = choose|f: Formula| encode(f) == enc;
    lemma_decode_encode_formula(outer_f);

    eq_subst_left_structure(enc);

    //  Extract components from encoding
    let eq_part_enc = unpair1(unpair2(enc));
    let impl_part_enc = unpair2(unpair2(enc));
    let x_enc = unpair1(unpair2(eq_part_enc));
    let y_enc = unpair2(unpair2(eq_part_enc));
    let left_subst_enc = unpair1(unpair2(impl_part_enc));
    let right_subst_enc = unpair2(unpair2(impl_part_enc));

    //  outer_f is Implies (tag 5)
    lemma_encode_is_pair(outer_f);
    lemma_unpair1_pair(formula_tag(outer_f), formula_content(outer_f));

    //  outer_f's right is Implies (tag 5) — established below in match
    let (left_subst_f, right_subst_f) = extract_left_right_subst(outer_f, enc);
    lemma_decode_encode_formula(left_subst_f);
    lemma_decode_encode_formula(right_subst_f);

    //  outer_f's left is Eq with terms x_enc, y_enc
    let (x_idx, y_idx) = extract_eq_terms(outer_f, enc);
    assert(x_idx == x_enc);
    assert(y_idx == y_enc);

    //  Forward walk: derive eq_subst_compatible
    lemma_check_eq_subst_pair_forward(left_subst_f, right_subst_f, x_enc, y_enc);

    //  Construct phi using extract_phi with a fresh variable
    let var_fresh = max_var(left_subst_f) + max_var(right_subst_f) + 1;
    let phi = extract_phi(left_subst_f, right_subst_f,
        Term::Var { index: x_enc }, Term::Var { index: y_enc }, var_fresh);

    //  Derive subst correspondence
    lemma_extract_phi_subst_left(left_subst_f, right_subst_f,
        Term::Var { index: x_enc }, Term::Var { index: y_enc }, var_fresh);
    lemma_extract_phi_subst_right(left_subst_f, right_subst_f,
        Term::Var { index: x_enc }, Term::Var { index: y_enc }, var_fresh);

    //  outer_f == Implies(Eq(Var(x_enc), Var(y_enc)), Implies(left_subst_f, right_subst_f))
    //           == Implies(Eq(Var(x_enc), Var(y_enc)), Implies(subst(phi, var_fresh, Var(x_enc)),
    //                                                          subst(phi, var_fresh, Var(y_enc))))
    //  This is the witness for is_axiom_eq_subst_left
    assert(decode_formula(enc) == outer_f);
    assert(outer_f == mk_implies(
        mk_eq(Term::Var { index: x_enc }, Term::Var { index: y_enc }),
        mk_implies(
            subst(phi, var_fresh, Term::Var { index: x_enc }),
            subst(phi, var_fresh, Term::Var { index: y_enc }))
    ));
}

///  Helper: extract the left and right sub-formulas from outer_f's Implies(Eq, Implies(l, r)) shape.
proof fn extract_left_right_subst(outer_f: Formula, enc: nat) -> (r: (Formula, Formula))
    requires
        encode(outer_f) == enc,
        unpair1(enc) == 5,
        unpair1(unpair2(unpair2(enc))) == 5,
    ensures ({
        let impl_part_enc = unpair2(unpair2(enc));
        let left_subst_enc = unpair1(unpair2(impl_part_enc));
        let right_subst_enc = unpair2(unpair2(impl_part_enc));
        encode(r.0) == left_subst_enc && encode(r.1) == right_subst_enc
    }),
{
    lemma_encode_is_pair(outer_f);
    lemma_unpair1_pair(formula_tag(outer_f), formula_content(outer_f));
    match outer_f {
        Formula::Implies { left, right } => {
            lemma_unpair2_pair(5nat, pair(encode(*left), encode(*right)));
            lemma_unpair2_pair(encode(*left), encode(*right));
            lemma_encode_is_pair(*right);
            lemma_unpair1_pair(formula_tag(*right), formula_content(*right));
            match *right {
                Formula::Implies { left: l, right: r } => {
                    lemma_unpair2_pair(5nat, pair(encode(*l), encode(*r)));
                    lemma_unpair1_pair(encode(*l), encode(*r));
                    lemma_unpair2_pair(encode(*l), encode(*r));
                    (*l, *r)
                },
                _ => (outer_f, outer_f),  //  unreachable: tag must be 5
            }
        },
        _ => (outer_f, outer_f),  //  unreachable: tag must be 5
    }
}

///  Helper: extract the term indices x, y from outer_f's Eq(x, y) part.
proof fn extract_eq_terms(outer_f: Formula, enc: nat) -> (r: (nat, nat))
    requires
        encode(outer_f) == enc,
        unpair1(enc) == 5,
        unpair1(unpair1(unpair2(enc))) == 0,
    ensures ({
        let eq_part_enc = unpair1(unpair2(enc));
        let x_enc = unpair1(unpair2(eq_part_enc));
        let y_enc = unpair2(unpair2(eq_part_enc));
        r.0 == x_enc && r.1 == y_enc
    }),
{
    lemma_encode_is_pair(outer_f);
    lemma_unpair1_pair(formula_tag(outer_f), formula_content(outer_f));
    match outer_f {
        Formula::Implies { left, right } => {
            lemma_unpair2_pair(5nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(encode(*left), encode(*right));
            lemma_encode_is_pair(*left);
            lemma_unpair1_pair(formula_tag(*left), formula_content(*left));
            match *left {
                Formula::Eq { left: lt, right: rt } => {
                    lemma_unpair2_pair(0nat, pair(encode_term(lt), encode_term(rt)));
                    lemma_unpair1_pair(encode_term(lt), encode_term(rt));
                    lemma_unpair2_pair(encode_term(lt), encode_term(rt));
                    match lt {
                        Term::Var { index: x_idx } => match rt {
                            Term::Var { index: y_idx } => (x_idx, y_idx),
                        },
                    }
                },
                _ => (0, 0),  //  unreachable
            }
        },
        _ => (0, 0),  //  unreachable
    }
}

} // verus!
