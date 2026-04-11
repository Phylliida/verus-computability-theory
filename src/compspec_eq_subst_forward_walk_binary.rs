use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_forward_binary_step_unfold::lemma_eq_subst_binary_step_unfold;
use crate::compspec_eq_subst_forward_binary_pieces::lemma_eq_subst_binary_consume_left;
use crate::compspec_eq_subst_forward_walk::{lemma_eq_subst_forward_walk, lemma_esb_valid_zero_stable};
use crate::compspec_eq_subst_forward_step2::lemma_esb_forward_binary_tags_match;

verus! {

#[verifier::rlimit(5000)]
pub proof fn lemma_eq_subst_forward_walk_binary(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        f1 matches Formula::And{..} || f1 matches Formula::Or{..}
            || f1 matches Formula::Implies{..} || f1 matches Formula::Iff{..},
        ({
            match f1 {
                Formula::And { left, right } | Formula::Or { left, right }
                | Formula::Implies { left, right } | Formula::Iff { left, right } => {
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
        Formula::And { left: l1, right: r1 } => {
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair1_pair(encode(*l1), encode(*r1));
            lemma_unpair2_pair(encode(*l1), encode(*r1));
            match f2 {
                Formula::And { left: l2, right: r2 } => {
                    binary_joiner_inline(f1, *l1, *r1, *l2, *r2, tag, f1_enc, f2_enc,
                        x_enc, y_enc, rest, valid, pe, re, fuel);
                    assert(eq_subst_compatible(f1, f2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc }));
                },
                _ => {
                    binary_tag_mismatch_contradiction(f1, f2, tag, x_enc, y_enc,
                        rest, valid, pe, re, fuel);
                },
            }
        },
        Formula::Or { left: l1, right: r1 } => {
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair1_pair(encode(*l1), encode(*r1));
            lemma_unpair2_pair(encode(*l1), encode(*r1));
            match f2 {
                Formula::Or { left: l2, right: r2 } => {
                    binary_joiner_inline(f1, *l1, *r1, *l2, *r2, tag, f1_enc, f2_enc,
                        x_enc, y_enc, rest, valid, pe, re, fuel);
                    assert(eq_subst_compatible(f1, f2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc }));
                },
                _ => {
                    binary_tag_mismatch_contradiction(f1, f2, tag, x_enc, y_enc,
                        rest, valid, pe, re, fuel);
                },
            }
        },
        Formula::Implies { left: l1, right: r1 } => {
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair1_pair(encode(*l1), encode(*r1));
            lemma_unpair2_pair(encode(*l1), encode(*r1));
            match f2 {
                Formula::Implies { left: l2, right: r2 } => {
                    binary_joiner_inline(f1, *l1, *r1, *l2, *r2, tag, f1_enc, f2_enc,
                        x_enc, y_enc, rest, valid, pe, re, fuel);
                    assert(eq_subst_compatible(f1, f2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc }));
                },
                _ => {
                    binary_tag_mismatch_contradiction(f1, f2, tag, x_enc, y_enc,
                        rest, valid, pe, re, fuel);
                },
            }
        },
        Formula::Iff { left: l1, right: r1 } => {
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair1_pair(encode(*l1), encode(*r1));
            lemma_unpair2_pair(encode(*l1), encode(*r1));
            match f2 {
                Formula::Iff { left: l2, right: r2 } => {
                    binary_joiner_inline(f1, *l1, *r1, *l2, *r2, tag, f1_enc, f2_enc,
                        x_enc, y_enc, rest, valid, pe, re, fuel);
                    assert(eq_subst_compatible(f1, f2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc }));
                },
                _ => {
                    binary_tag_mismatch_contradiction(f1, f2, tag, x_enc, y_enc,
                        rest, valid, pe, re, fuel);
                },
            }
        },
        _ => {},
    }
}

///  Tag mismatch contradiction helper for binary case.
///  When f1 has a binary tag and f2 doesn't have the same tag, the iterate
///  precondition cannot hold — derive false.
proof fn binary_tag_mismatch_contradiction(
    f1: Formula, f2: Formula, tag: nat, x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        tag >= 3, tag <= 6,
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

    //  Step valid != 0 (else iterate stays 0 → contradiction)
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

    //  Tags must match (from helper)
    lemma_esb_forward_binary_tags_match(f1_enc, f2_enc, tag,
        rest, valid, (fuel - 1) as nat, pe, re, x_enc, y_enc);
    //  Now: unpair1(f2_enc) == tag
    //  But formula_tag(f2) != tag and unpair1(encode(f2)) == formula_tag(f2)
    lemma_encode_is_pair(f2);
    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
    //  Contradiction: unpair1(f2_enc) == tag AND unpair1(f2_enc) == formula_tag(f2) != tag
}

///  Inline joiner: composes the 4 cached binary pieces.
///  Takes parent f1 for the decreases — both children are strictly smaller.
proof fn binary_joiner_inline(
    f1_parent: Formula,
    l1: Formula, r1: Formula, l2: Formula, r2: Formula,
    tag: nat, f1_enc: nat, f2_enc: nat,
    x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        tag >= 3, tag <= 6,
        f1_enc == pair(tag, pair(encode(l1), encode(r1))),
        f2_enc == pair(tag, pair(encode(l2), encode(r2))),
        //  Parent connection — l1 and r1 are children of f1_parent
        ({
            match f1_parent {
                Formula::And { left, right } | Formula::Or { left, right }
                | Formula::Implies { left, right } | Formula::Iff { left, right } =>
                    *left == l1 && *right == r1,
                _ => false,
            }
        }),
        fuel >= 1 + formula_size(l1) + formula_size(r1),
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(f1_enc, f2_enc) + 1, rest), valid),
                pair(pe, pair(re, pair(x_enc, y_enc))))
        ) != 0,
    ensures
        eq_subst_compatible(l1, l2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
        eq_subst_compatible(r1, r2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1_parent, 0nat,
{
    hide(compspec_iterate);
    lemma_unpair1_pair(tag, pair(encode(l1), encode(r1)));
    lemma_unpair2_pair(tag, pair(encode(l1), encode(r1)));
    lemma_unpair1_pair(tag, pair(encode(l2), encode(r2)));
    lemma_unpair2_pair(tag, pair(encode(l2), encode(r2)));
    lemma_unpair1_pair(encode(l1), encode(r1));
    lemma_unpair2_pair(encode(l1), encode(r1));
    lemma_unpair1_pair(encode(l2), encode(r2));
    lemma_unpair2_pair(encode(l2), encode(r2));

    let el = pair(encode(l1), encode(l2));
    let er = pair(encode(r1), encode(r2));

    //  Piece 1: step + unfold (cached)
    lemma_eq_subst_binary_step_unfold(
        f1_enc, f2_enc, tag, el, er, rest, valid, pe, re, x_enc, y_enc, fuel);

    //  Piece 2: left IH — direct call to walk (recursive)
    lemma_eq_subst_forward_walk(l1, l2, x_enc, y_enc,
        pair(er + 1, rest), 1nat, pe, re, (fuel - 1) as nat);

    //  Piece 3: backward consume left (cached) — produces witness v != 0
    lemma_eq_subst_binary_consume_left(l1, l2, x_enc, y_enc,
        pair(er + 1, rest), 1nat, pe, re, (fuel - 1) as nat);

    //  Extract the witness v
    let v = choose|v: nat| v != 0 &&
        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
            pair(pair(pair(encode(l1), encode(l2)) + 1, pair(er + 1, rest)), 1nat),
            pair(pe, pair(re, pair(x_enc, y_enc))))
        == #[trigger] compspec_iterate(check_eq_subst_step(),
            ((fuel - 1) as nat - formula_size(l1)) as nat,
            pair(pair(er + 1, rest), v),
            pair(pe, pair(re, pair(x_enc, y_enc))));

    //  Piece 4: right IH — direct call to walk with the extracted witness v
    lemma_eq_subst_forward_walk(r1, r2, x_enc, y_enc,
        rest, v, pe, re, ((fuel - 1) as nat - formula_size(l1)) as nat);
}

} // verus!
