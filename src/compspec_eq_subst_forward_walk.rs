use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_eq_subst_forward_step::lemma_eq_subst_forward_step_atomic;
use crate::compspec_eq_subst_forward_step2::*;

verus! {

///  Step with valid=0 returns acc unchanged.
proof fn lemma_esb_step_valid_zero(counter: nat, stack: nat, s: nat)
    ensures
        eval_comp(check_eq_subst_step(), pair(counter, pair(pair(stack, 0nat), s)))
            == pair(stack, 0nat),
{
    let acc = pair(stack, 0nat);
    let n = pair(counter, pair(acc, s));
    crate::compspec_free_var_helpers::lemma_eval_br_acc(counter, acc, s);
    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(stack, 0nat);
    lemma_eval_ifzero_then(cs_snd(br_acc()), br_acc(),
        CompSpec::IfZero {
            cond: Box::new(cs_fst(cs_fst(br_acc()))),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_eq_subst_process()),
        }, n);
}

///  Iterating with valid=0 keeps acc unchanged.
proof fn lemma_esb_valid_zero_stable(fuel: nat, stack: nat, s: nat)
    ensures
        compspec_iterate(check_eq_subst_step(), fuel, pair(stack, 0nat), s)
            == pair(stack, 0nat),
    decreases fuel,
{
    if fuel > 0 {
        lemma_esb_step_valid_zero((fuel - 1) as nat, stack, s);
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, pair(stack, 0nat), s);
        lemma_esb_valid_zero_stable((fuel - 1) as nat, stack, s);
    }
}

///  Forward walk: if check_eq_subst parallel iterate accepts, formulas are eq_subst_compatible.
#[verifier::rlimit(5000)]
pub proof fn lemma_eq_subst_forward_walk(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, fuel: nat,
)
    requires
        fuel >= formula_size(f1),
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(encode(f1), encode(f2)) + 1, rest), 1nat),
                pair(encode(f1), pair(encode(f2), pair(x_enc, y_enc))))
        ) != 0,
    ensures
        eq_subst_compatible(f1, f2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1,
{
    hide(compspec_iterate);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let entry = pair(f1_enc, f2_enc);
    let acc0 = pair(pair(entry + 1, rest), 1nat);
    let s = pair(f1_enc, pair(f2_enc, pair(x_enc, y_enc)));

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
            lemma_esb_valid_zero_stable((fuel - 1) as nat, unpair1(step_result), s);
            lemma_unpair2_pair(unpair1(step_result), 0nat);
        }
    };

    match f1 {
        Formula::Eq { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(0nat, pair(encode_term(l1), encode_term(r1)));
            lemma_eq_subst_forward_step_atomic(f1_enc, f2_enc,
                rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
            //  Tags match → f2 must be Eq
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
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        Formula::In { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(1nat, pair(encode_term(l1), encode_term(r1)));
            lemma_eq_subst_forward_step_atomic(f1_enc, f2_enc,
                rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
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
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        Formula::Not { sub: s1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(2nat, encode(*s1));
            lemma_unpair2_pair(2nat, encode(*s1));
            match f2 {
                Formula::Not { sub: s2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(2nat, encode(*s2));
                    lemma_unpair2_pair(2nat, encode(*s2));
                    lemma_eq_subst_forward_step_unary(f1_enc, f2_enc,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    //  Step gives pair(pair(sub_entry+1, rest), 1)
                    //  Unfold iterate to get sub-iterate valid
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(pair(encode(*s1), encode(*s2)) + 1, rest), 1nat), s)
                    ) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*s1, *s2, x_enc, y_enc, rest, (fuel - 1) as nat);
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        Formula::And { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            let tag: nat = 3;
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
                    //  Step gives pair(pair(el+1, pair(er+1, rest)), 1)
                    let el = pair(encode(*l1), encode(*l2));
                    let er = pair(encode(*r1), encode(*r2));
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)
                    ) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    //  IH on left, then right
                    lemma_eq_subst_forward_walk(*l1, *l2, x_enc, y_enc,
                        pair(er + 1, rest), (fuel - 1) as nat);
                    //  Need remaining iterate for right — use backward traversal
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
            let tag: nat = 4;
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
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)
                    ) != 0) by {
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
            let tag: nat = 5;
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
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)
                    ) != 0) by {
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
            let tag: nat = 6;
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
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)
                    ) != 0) by {
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
        Formula::Forall { var: v1, sub: s1 } => {
            lemma_encode_is_pair(f1);
            let tag = formula_tag(f1);
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
                    //  Step gives pair(pair(sub_entry+1, rest), bound_match)
                    //  bound_match != 0 (from iterate acceptance) → v1 == v2
                    let sub_entry = pair(encode(*s1), encode(*s2));
                    let bound_match: nat = if v1 == v2 { 1nat } else { 0nat };
                    if v1 != v2 {
                        //  bound_match = 0 → step valid = 0 → iterate stays 0 → contradiction
                        assert(false) by {
                            reveal(compspec_iterate);
                            lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                            lemma_esb_valid_zero_stable((fuel - 1) as nat,
                                pair(sub_entry + 1, rest), s);
                            lemma_unpair2_pair(pair(sub_entry + 1, rest), 0nat);
                        };
                    }
                    //  v1 == v2, so step valid = 1
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(sub_entry + 1, rest), 1nat), s)
                    ) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*s1, *s2, x_enc, y_enc, rest, (fuel - 1) as nat);
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
        Formula::Exists { var: v1, sub: s1 } => {
            lemma_encode_is_pair(f1);
            let tag = formula_tag(f1);
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
                    let bound_match: nat = if v1 == v2 { 1nat } else { 0nat };
                    if v1 != v2 {
                        assert(false) by {
                            reveal(compspec_iterate);
                            lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                            lemma_esb_valid_zero_stable((fuel - 1) as nat,
                                pair(sub_entry + 1, rest), s);
                            lemma_unpair2_pair(pair(sub_entry + 1, rest), 0nat);
                        };
                    }
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(sub_entry + 1, rest), 1nat), s)
                    ) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*s1, *s2, x_enc, y_enc, rest, (fuel - 1) as nat);
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(formula_tag(f2), formula_content(f2));
                    return;
                },
            }
        },
    }
}

} // verus!
