use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_forward_step2::lemma_eq_subst_forward_step_quant;
use crate::compspec_eq_subst_forward_walk::{lemma_esb_valid_zero_stable, lemma_eq_subst_forward_walk};

verus! {

///  Forward walk for quantifier formulas (Forall/Exists).
#[verifier::rlimit(3000)]
pub proof fn lemma_eq_subst_forward_walk_quant(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, fuel: nat,
)
    requires
        formula_tag(f1) >= 7,
        fuel >= formula_size(f1),
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(encode(f1), encode(f2)) + 1, rest), 1nat),
                pair(encode(f1), pair(encode(f2), pair(x_enc, y_enc))))
        ) != 0,
    ensures
        eq_subst_compatible(f1, f2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1, 0nat,
{
    hide(compspec_iterate);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let acc0 = pair(pair(pair(f1_enc, f2_enc) + 1, rest), 1nat);
    let s = pair(f1_enc, pair(f2_enc, pair(x_enc, y_enc)));
    let tag = formula_tag(f1);

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

    match f1 {
        Formula::Forall { var: v1, sub: s1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair2_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair1_pair(v1, encode(*s1));
            lemma_unpair2_pair(v1, encode(*s1));
            match f2 {
                Formula::Forall { var: v2, sub: s2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(tag, pair(v2, encode(*s2)));
                    lemma_unpair2_pair(tag, pair(v2, encode(*s2)));
                    lemma_unpair1_pair(v2, encode(*s2));
                    lemma_unpair2_pair(v2, encode(*s2));
                    lemma_eq_subst_forward_step_quant(f1_enc, f2_enc, tag,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    let sub_entry = pair(encode(*s1), encode(*s2));
                    if v1 != v2 {
                        assert(false) by {
                            reveal(compspec_iterate);
                            lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                            lemma_esb_valid_zero_stable((fuel - 1) as nat,
                                pair(sub_entry + 1, rest), s);
                            lemma_unpair2_pair(pair(sub_entry + 1, rest), 0nat);
                        };
                    }
                    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                        pair(pair(sub_entry + 1, rest), 1nat), s)) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*s1, *s2, x_enc, y_enc, rest, (fuel - 1) as nat);
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                },
            }
        },
        Formula::Exists { var: v1, sub: s1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair2_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair1_pair(v1, encode(*s1));
            lemma_unpair2_pair(v1, encode(*s1));
            match f2 {
                Formula::Exists { var: v2, sub: s2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(tag, pair(v2, encode(*s2)));
                    lemma_unpair2_pair(tag, pair(v2, encode(*s2)));
                    lemma_unpair1_pair(v2, encode(*s2));
                    lemma_unpair2_pair(v2, encode(*s2));
                    lemma_eq_subst_forward_step_quant(f1_enc, f2_enc, tag,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    let sub_entry = pair(encode(*s1), encode(*s2));
                    if v1 != v2 {
                        assert(false) by {
                            reveal(compspec_iterate);
                            lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                            lemma_esb_valid_zero_stable((fuel - 1) as nat,
                                pair(sub_entry + 1, rest), s);
                            lemma_unpair2_pair(pair(sub_entry + 1, rest), 0nat);
                        };
                    }
                    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                        pair(pair(sub_entry + 1, rest), 1nat), s)) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*s1, *s2, x_enc, y_enc, rest, (fuel - 1) as nat);
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
