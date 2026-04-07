use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_forward_step2::lemma_eq_subst_forward_step_binary;
use crate::compspec_eq_subst_forward_walk::lemma_eq_subst_forward_walk;

verus! {

///  Forward walk for binary formulas (And/Or/Implies/Iff).
///  Matches f1 and f2 variants, calls walk recursively on children.
#[verifier::rlimit(5000)]
pub proof fn lemma_eq_subst_forward_walk_binary(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, fuel: nat,
)
    requires
        formula_tag(f1) >= 3, formula_tag(f1) <= 6,
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
    let entry = pair(f1_enc, f2_enc);
    let acc0 = pair(pair(entry + 1, rest), 1nat);
    let s = pair(f1_enc, pair(f2_enc, pair(x_enc, y_enc)));
    let tag = formula_tag(f1);

    lemma_formula_size_pos(f1);

    //  Unfold + derive step valid != 0
    assert(unpair2(eval_comp(check_eq_subst_step(),
        pair((fuel - 1) as nat, pair(acc0, s)))) != 0) by {
        reveal(compspec_iterate);
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
        let step_result = eval_comp(check_eq_subst_step(),
            pair((fuel - 1) as nat, pair(acc0, s)));
        if unpair2(step_result) == 0 {
            lemma_pair_surjective(step_result);
            crate::compspec_eq_subst_forward_walk::lemma_esb_valid_zero_stable(
                (fuel - 1) as nat, unpair1(step_result), s);
            lemma_unpair2_pair(unpair1(step_result), 0nat);
        }
    };

    match f1 {
        Formula::And { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            match f2 {
                Formula::And { left: l2, right: r2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair2_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair1_pair(encode(*l1), encode(*r1));
                    lemma_unpair2_pair(encode(*l1), encode(*r1));
                    lemma_unpair1_pair(encode(*l2), encode(*r2));
                    lemma_unpair2_pair(encode(*l2), encode(*r2));
                    lemma_eq_subst_forward_step_binary(f1_enc, f2_enc, tag,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    let el = pair(encode(*l1), encode(*l2));
                    let er = pair(encode(*r1), encode(*r2));
                    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                        pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*l1, *l2, x_enc, y_enc,
                        pair(er + 1, rest), (fuel - 1) as nat);
                    crate::compspec_eq_subst_backward::lemma_eq_subst_walk(
                        *l1, *l2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc },
                        pair(er + 1, rest), 1, (fuel - 1) as nat, f1_enc, f2_enc);
                    lemma_eq_subst_forward_walk(*r1, *r2, x_enc, y_enc,
                        rest, ((fuel - 1) as nat - formula_size(*l1)) as nat);
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        Formula::Or { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            match f2 {
                Formula::Or { left: l2, right: r2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair2_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair1_pair(encode(*l1), encode(*r1));
                    lemma_unpair2_pair(encode(*l1), encode(*r1));
                    lemma_unpair1_pair(encode(*l2), encode(*r2));
                    lemma_unpair2_pair(encode(*l2), encode(*r2));
                    lemma_eq_subst_forward_step_binary(f1_enc, f2_enc, tag,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    let el = pair(encode(*l1), encode(*l2));
                    let er = pair(encode(*r1), encode(*r2));
                    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                        pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*l1, *l2, x_enc, y_enc,
                        pair(er + 1, rest), (fuel - 1) as nat);
                    crate::compspec_eq_subst_backward::lemma_eq_subst_walk(
                        *l1, *l2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc },
                        pair(er + 1, rest), 1, (fuel - 1) as nat, f1_enc, f2_enc);
                    lemma_eq_subst_forward_walk(*r1, *r2, x_enc, y_enc,
                        rest, ((fuel - 1) as nat - formula_size(*l1)) as nat);
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        Formula::Implies { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            match f2 {
                Formula::Implies { left: l2, right: r2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair2_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair1_pair(encode(*l1), encode(*r1));
                    lemma_unpair2_pair(encode(*l1), encode(*r1));
                    lemma_unpair1_pair(encode(*l2), encode(*r2));
                    lemma_unpair2_pair(encode(*l2), encode(*r2));
                    lemma_eq_subst_forward_step_binary(f1_enc, f2_enc, tag,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    let el = pair(encode(*l1), encode(*l2));
                    let er = pair(encode(*r1), encode(*r2));
                    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                        pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*l1, *l2, x_enc, y_enc,
                        pair(er + 1, rest), (fuel - 1) as nat);
                    crate::compspec_eq_subst_backward::lemma_eq_subst_walk(
                        *l1, *l2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc },
                        pair(er + 1, rest), 1, (fuel - 1) as nat, f1_enc, f2_enc);
                    lemma_eq_subst_forward_walk(*r1, *r2, x_enc, y_enc,
                        rest, ((fuel - 1) as nat - formula_size(*l1)) as nat);
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        Formula::Iff { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(tag, pair(encode(*l1), encode(*r1)));
            lemma_unpair2_pair(tag, pair(encode(*l1), encode(*r1)));
            match f2 {
                Formula::Iff { left: l2, right: r2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair2_pair(tag, pair(encode(*l2), encode(*r2)));
                    lemma_unpair1_pair(encode(*l1), encode(*r1));
                    lemma_unpair2_pair(encode(*l1), encode(*r1));
                    lemma_unpair1_pair(encode(*l2), encode(*r2));
                    lemma_unpair2_pair(encode(*l2), encode(*r2));
                    lemma_eq_subst_forward_step_binary(f1_enc, f2_enc, tag,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    let el = pair(encode(*l1), encode(*l2));
                    let er = pair(encode(*r1), encode(*r2));
                    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                        pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*l1, *l2, x_enc, y_enc,
                        pair(er + 1, rest), (fuel - 1) as nat);
                    crate::compspec_eq_subst_backward::lemma_eq_subst_walk(
                        *l1, *l2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc },
                        pair(er + 1, rest), 1, (fuel - 1) as nat, f1_enc, f2_enc);
                    lemma_eq_subst_forward_walk(*r1, *r2, x_enc, y_enc,
                        rest, ((fuel - 1) as nat - formula_size(*l1)) as nat);
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        _ => { return; }, // impossible by precondition
    }
}

} // verus!
