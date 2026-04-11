use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_forward_step2::{
    lemma_eq_subst_forward_step_quant,
    lemma_esb_forward_quant_tags_match,
};
use crate::compspec_eq_subst_forward_walk::{lemma_esb_valid_zero_stable, lemma_eq_subst_forward_walk};

verus! {

#[verifier::rlimit(3000)]
pub proof fn lemma_eq_subst_forward_walk_quant(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        f1 matches Formula::Forall{..} || f1 matches Formula::Exists{..},
        ({
            match f1 {
                Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
                    fuel >= formula_size(f1) &&
                    unpair2(
                        compspec_iterate(check_eq_subst_step(), fuel,
                            pair(pair(pair(encode(f1), encode(f2)) + 1, rest), valid),
                            pair(pe, pair(re, pair(x_enc, y_enc))))
                    ) != 0
                },
                _ => false,
            }
        }),
    ensures
        eq_subst_compatible(f1, f2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1, 1nat,
{
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let tag = formula_tag(f1);
    lemma_formula_size_pos(f1);
    lemma_encode_is_pair(f1);

    match f1 {
        Formula::Forall { var: v1, sub: s1 } => {
            lemma_unpair1_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair2_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair1_pair(v1, encode(*s1));
            lemma_unpair2_pair(v1, encode(*s1));
            match f2 {
                Formula::Forall { var: v2, sub: s2 } => {
                    quant_joiner_inline(f1, v1, *s1, v2, *s2, tag, f1_enc, f2_enc,
                        x_enc, y_enc, rest, valid, pe, re, fuel);
                    assert(eq_subst_compatible(f1, f2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc }));
                },
                _ => {
                    quant_tag_mismatch_contradiction(f1, f2, tag, x_enc, y_enc,
                        rest, valid, pe, re, fuel);
                },
            }
        },
        Formula::Exists { var: v1, sub: s1 } => {
            lemma_unpair1_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair2_pair(tag, pair(v1, encode(*s1)));
            lemma_unpair1_pair(v1, encode(*s1));
            lemma_unpair2_pair(v1, encode(*s1));
            match f2 {
                Formula::Exists { var: v2, sub: s2 } => {
                    quant_joiner_inline(f1, v1, *s1, v2, *s2, tag, f1_enc, f2_enc,
                        x_enc, y_enc, rest, valid, pe, re, fuel);
                    assert(eq_subst_compatible(f1, f2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc }));
                },
                _ => {
                    quant_tag_mismatch_contradiction(f1, f2, tag, x_enc, y_enc,
                        rest, valid, pe, re, fuel);
                },
            }
        },
        _ => {},
    }
}

///  Tag mismatch helper for quantifier case.
proof fn quant_tag_mismatch_contradiction(
    f1: Formula, f2: Formula, tag: nat, x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        tag >= 7,
        unpair1(encode(f1)) == tag,
        formula_tag(f2) != tag,
        fuel >= 1,
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(encode(f1), encode(f2)) + 1, rest), valid),
                pair(pe, pair(re, pair(x_enc, y_enc))))
        ) != 0,
    ensures false,
{
    hide(compspec_iterate);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let acc0 = pair(pair(pair(f1_enc, f2_enc) + 1, rest), valid);
    let s = pair(pe, pair(re, pair(x_enc, y_enc)));

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

    lemma_esb_forward_quant_tags_match(f1_enc, f2_enc, tag,
        rest, valid, (fuel - 1) as nat, pe, re, x_enc, y_enc);
    lemma_encode_is_pair(f2);
    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
}

///  Inline joiner: step + IH on sub.
proof fn quant_joiner_inline(
    f1_parent: Formula,
    v1: nat, s1: Formula, v2: nat, s2: Formula,
    tag: nat, f1_enc: nat, f2_enc: nat,
    x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        tag >= 7, tag <= 8,
        f1_enc == pair(tag, pair(v1, encode(s1))),
        f2_enc == pair(tag, pair(v2, encode(s2))),
        ({
            match f1_parent {
                Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } =>
                    v == v1 && *sub == s1,
                _ => false,
            }
        }),
        fuel >= 1 + formula_size(s1),
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(f1_enc, f2_enc) + 1, rest), valid),
                pair(pe, pair(re, pair(x_enc, y_enc))))
        ) != 0,
    ensures
        v1 == v2,
        eq_subst_compatible(s1, s2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1_parent, 0nat,
{
    hide(compspec_iterate);
    lemma_unpair1_pair(tag, pair(v1, encode(s1)));
    lemma_unpair2_pair(tag, pair(v1, encode(s1)));
    lemma_unpair1_pair(v1, encode(s1));
    lemma_unpair2_pair(v1, encode(s1));
    lemma_unpair1_pair(tag, pair(v2, encode(s2)));
    lemma_unpair2_pair(tag, pair(v2, encode(s2)));
    lemma_unpair1_pair(v2, encode(s2));
    lemma_unpair2_pair(v2, encode(s2));

    let acc0 = pair(pair(pair(f1_enc, f2_enc) + 1, rest), valid);
    let s = pair(pe, pair(re, pair(x_enc, y_enc)));

    //  Step valid != 0
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

    //  Compute step result
    lemma_eq_subst_forward_step_quant(f1_enc, f2_enc, tag,
        rest, valid, (fuel - 1) as nat, pe, re, x_enc, y_enc);
    let sub_entry = pair(encode(s1), encode(s2));

    //  If v1 != v2, bound_match = 0, step result valid = 0, contradicts step valid != 0
    if v1 != v2 {
        assert(false) by {
            reveal(compspec_iterate);
            lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
            lemma_esb_valid_zero_stable((fuel - 1) as nat,
                pair(sub_entry + 1, rest), s);
            lemma_unpair2_pair(pair(sub_entry + 1, rest), 0nat);
        };
    }

    //  v1 == v2, step result valid = 1, unfold to get sub-iterate
    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
        pair(pair(sub_entry + 1, rest), 1nat), s)) != 0) by {
        reveal(compspec_iterate);
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
    };

    //  Recursive walk on sub
    lemma_eq_subst_forward_walk(s1, s2, x_enc, y_enc, rest, 1nat, pe, re, (fuel - 1) as nat);
}

} // verus!
