use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_forward_step::lemma_eq_subst_forward_step_atomic;
use crate::compspec_eq_subst_forward_walk::lemma_esb_valid_zero_stable;

verus! {

///  Forward walk for atomic formulas (Eq/In).
#[verifier::rlimit(3000)]
pub proof fn lemma_eq_subst_forward_walk_atomic(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        formula_tag(f1) <= 1,
        fuel >= formula_size(f1),
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(encode(f1), encode(f2)) + 1, rest), valid),
                pair(pe, pair(re, pair(x_enc, y_enc))))
        ) != 0,
    ensures
        eq_subst_compatible(f1, f2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
{
    hide(compspec_iterate);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let acc0 = pair(pair(pair(f1_enc, f2_enc) + 1, rest), valid);
    let s = pair(pe, pair(re, pair(x_enc, y_enc)));

    lemma_formula_size_pos(f1);

    //  Unfold + step valid != 0
    assert(unpair2(eval_comp(check_eq_subst_step(),
        pair((fuel - 1) as nat, pair(acc0, s)))) != 0) by {
        reveal(compspec_iterate);
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
        let sr = eval_comp(check_eq_subst_step(), pair((fuel - 1) as nat, pair(acc0, s)));
        if unpair2(sr) == 0 {
            lemma_pair_surjective(sr);
            lemma_esb_valid_zero_stable((fuel - 1) as nat, unpair1(sr), s);
            lemma_unpair2_pair(unpair1(sr), 0nat);
        }
    };

    lemma_encode_is_pair(f1);
    //  Establish unpair1(f1_enc) <= 1 for step helper precondition
    lemma_unpair1_pair(formula_tag(f1), formula_content(f1));

    lemma_eq_subst_forward_step_atomic(f1_enc, f2_enc,
        rest, valid, (fuel - 1) as nat, pe, re, x_enc, y_enc);

    match f1 {
        Formula::Eq { left: l1, right: r1 } => {
            lemma_unpair1_pair(0nat, pair(encode_term(l1), encode_term(r1)));
            match f2 {
                Formula::Eq { left: l2, right: r2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(0nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair2_pair(0nat, pair(encode_term(l1), encode_term(r1)));
                    lemma_unpair2_pair(0nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair1_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair2_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair1_pair(encode_term(l2), encode_term(r2));
                    lemma_unpair2_pair(encode_term(l2), encode_term(r2));
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                },
            }
        },
        Formula::In { left: l1, right: r1 } => {
            lemma_unpair1_pair(1nat, pair(encode_term(l1), encode_term(r1)));
            match f2 {
                Formula::In { left: l2, right: r2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(1nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair2_pair(1nat, pair(encode_term(l1), encode_term(r1)));
                    lemma_unpair2_pair(1nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair1_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair2_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair1_pair(encode_term(l2), encode_term(r2));
                    lemma_unpair2_pair(encode_term(l2), encode_term(r2));
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                },
            }
        },
        _ => {},
    }
}

} // verus!
