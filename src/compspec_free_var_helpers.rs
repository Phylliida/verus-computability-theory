use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;

verus! {

///  Helper: br_acc() evaluates to the accumulator.
///  br_acc() = CantorFst(CantorSnd(Id))
///  On input pair(i, pair(acc, rest)): returns acc.
proof fn lemma_eval_br_acc(i: nat, acc: nat, rest: nat)
    ensures
        eval_comp(br_acc(), pair(i, pair(acc, rest))) == acc,
{
    let input = pair(i, pair(acc, rest));
    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, rest));
    lemma_unpair1_pair(acc, rest);
}

///  Helper: extract v from the BoundedRec input.
///  v = cs_snd(cs_snd(cs_snd(Id)))
///  On input pair(i, pair(acc, pair(f_enc, v))): returns v.
proof fn lemma_eval_v_extract(i: nat, acc: nat, f_enc: nat, v: nat)
    ensures
        eval_comp(
            cs_snd(cs_snd(cs_snd(CompSpec::Id))),
            pair(i, pair(acc, pair(f_enc, v)))
        ) == v,
{
    let input = pair(i, pair(acc, pair(f_enc, v)));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, pair(f_enc, v)));
    lemma_unpair2_pair(acc, pair(f_enc, v));
    lemma_unpair2_pair(f_enc, v);
}

///  Helper: when found != 0, the step function returns acc unchanged.
proof fn lemma_step_found_nonzero(
    i: nat, stack: nat, found: nat, f_enc: nat, v: nat,
)
    requires
        found != 0,
    ensures ({
        let acc = pair(stack, found);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input) == acc
    }),
{
    let acc = pair(stack, found);
    let input = pair(i, pair(acc, pair(f_enc, v)));
    //  has_free_var_step() = IfZero { cond: found_expr, then: ..., else: acc }
    //  found != 0 → else branch → returns acc
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let found_expr = cs_snd(br_acc());
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(stack, found);
    assert(eval_comp(found_expr, input) == found);
    assert(found != 0);
    //  IfZero with nonzero cond → else branch = br_acc()
    lemma_eval_ifzero_else(found_expr,
        CompSpec::IfZero {
            cond: Box::new(cs_fst(cs_fst(br_acc()))),
            then_br: Box::new(br_acc()),
            else_br: Box::new(has_free_var_process_top()),
        },
        br_acc(),
        input);
}

///  Helper: when found == 0 and stack is empty, step returns acc unchanged.
pub proof fn lemma_step_empty_stack(
    i: nat, f_enc: nat, v: nat,
)
    ensures ({
        let acc = pair(0nat, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input) == acc
    }),
{
    let acc = pair(0nat, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let found_expr = cs_snd(br_acc());
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(0nat, 0nat);
    assert(eval_comp(found_expr, input) == 0);
    //  found == 0 → then branch (inner IfZero checking stack)
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(0nat, 0nat);
    //  stack = pair(0, 0) = 0, unpair1(0) = unpair1(pair(0,0)) = 0
    //  pair(0, 0) = triangular(0) + 0 = 0*1/2 + 0 = 0
    assert(pair(0nat, 0nat) == 0nat) by {
        assert(0nat * 1nat == 0nat) by(nonlinear_arith);
    }
    lemma_unpair1_pair(0nat, 0nat);
    assert(eval_comp(stack_expr, input) == 0nat);
    //  cs_fst(stack) = unpair1(stack) = unpair1(0) = 0
    let stack_top = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    assert(eval_comp(stack_top, input) == unpair1(0nat));
    assert(unpair1(0nat) == 0nat);
    //  IfZero(0): then branch → acc
    lemma_eval_ifzero_then(stack_top, br_acc(), has_free_var_process_top(), input);
    lemma_eval_ifzero_then(found_expr,
        CompSpec::IfZero {
            cond: Box::new(stack_top),
            then_br: Box::new(br_acc()),
            else_br: Box::new(has_free_var_process_top()),
        },
        br_acc(),
        input);
}

///  Helper: when found==0 and stack non-empty, step == process_top.
proof fn lemma_step_to_process_top(
    i: nat, enc_plus_1: nat, rest: nat, f_enc: nat, v: nat,
)
    requires
        enc_plus_1 > 0,
    ensures ({
        let stack = pair(enc_plus_1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input)
            == eval_comp(has_free_var_process_top(), input)
    }),
{
    let stack = pair(enc_plus_1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));
    //  found == 0 → then branch
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let found_expr = cs_snd(br_acc());
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(stack, 0nat);
    assert(eval_comp(found_expr, input) == 0nat);
    //  stack non-empty: unpair1(stack) = enc_plus_1 > 0
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    //  unpair1(unpair1(pair(stack, 0))) = unpair1(stack) = enc_plus_1
    let stack_top_expr = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc_plus_1, rest);
    assert(eval_comp(stack_top_expr, input) == enc_plus_1);
    assert(enc_plus_1 != 0);
    //  IfZero(enc_plus_1): nonzero → else branch → process_top
    lemma_eval_ifzero_else(stack_top_expr, br_acc(), has_free_var_process_top(), input);
    //  Outer IfZero(found==0): then branch → inner IfZero result
    lemma_eval_ifzero_then(found_expr,
        CompSpec::IfZero {
            cond: Box::new(stack_top_expr),
            then_br: Box::new(br_acc()),
            else_br: Box::new(has_free_var_process_top()),
        },
        br_acc(),
        input);
}

///  Helper: process_top for tag 0 (Eq). Returns pair(rest, or(eq(left,v), eq(right,v))).
///  When left_idx != v and right_idx != v, found = 0.
proof fn lemma_process_top_tag0(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        left_idx != v,
        right_idx != v,
    ensures ({
        let enc = pair(0nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_process_top(), input) == pair(rest, 0nat)
    }),
{
    let enc = pair(0nat, pair(left_idx, right_idx));
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));
    //  process_top extracts: top_enc = Pred(unpair1(stack)) = enc
    //  tag = unpair1(enc) = 0, content = unpair2(enc) = pair(left_idx, right_idx)
    //  Dispatch: IfZero(tag==0) → then branch → pair(rest, or(eq(left,v), eq(right,v)))

    //  Extract stack components
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);

    //  top_enc = Pred(unpair1(stack)) = Pred(enc + 1) = enc
    let fst_stack = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc + 1, rest);
    assert(eval_comp(fst_stack, input) == enc + 1);
    let top_enc_expr = cs_comp(CompSpec::Pred, fst_stack);
    lemma_eval_comp(CompSpec::Pred, fst_stack, input);
    lemma_eval_pred(enc + 1);
    assert(eval_comp(top_enc_expr, input) == enc);

    //  tag = unpair1(enc) = 0
    let tag_expr = cs_fst(top_enc_expr);
    lemma_eval_fst(top_enc_expr, input);
    lemma_unpair1_pair(0nat, pair(left_idx, right_idx));
    assert(eval_comp(tag_expr, input) == 0nat);

    //  rest_expr = unpair2(stack)
    let rest_expr = cs_snd(stack_expr);
    lemma_eval_snd(stack_expr, input);
    lemma_unpair2_pair(enc + 1, rest);
    assert(eval_comp(rest_expr, input) == rest);

    //  content = unpair2(enc) = pair(left_idx, right_idx)
    let content_expr = cs_snd(top_enc_expr);
    lemma_eval_snd(top_enc_expr, input);
    lemma_unpair2_pair(0nat, pair(left_idx, right_idx));

    //  fst(content) = left_idx, snd(content) = right_idx
    let left_expr = cs_fst(content_expr);
    let right_expr = cs_snd(content_expr);
    lemma_eval_fst(content_expr, input);
    lemma_eval_snd(content_expr, input);
    lemma_unpair1_pair(left_idx, right_idx);
    lemma_unpair2_pair(left_idx, right_idx);

    //  v expression
    let v_expr = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_v_extract(i, acc, f_enc, v);

    //  cs_eq(left, v) = 0, cs_eq(right, v) = 0
    lemma_eval_eq(left_expr, v_expr, input);
    lemma_eval_eq(right_expr, v_expr, input);
    //  cs_or(0, 0) = 0 + 0 = 0
    let eq_left = cs_eq(left_expr, v_expr);
    let eq_right = cs_eq(right_expr, v_expr);
    lemma_eval_add(eq_left, eq_right, input);

    //  Tag == 0 → then branch of first IfZero in process_top
    //  Result: pair(rest, cs_or(eq_left, eq_right)) = pair(rest, 0)
    let result_expr = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_or(
            cs_eq(cs_fst(content_expr), v_expr),
            cs_eq(cs_snd(content_expr), v_expr),
        )),
    };
    lemma_eval_pair(rest_expr, cs_or(
        cs_eq(cs_fst(content_expr), v_expr),
        cs_eq(cs_snd(content_expr), v_expr),
    ), input);

    //  IfZero(tag==0): then branch
    lemma_eval_ifzero_then(tag_expr, result_expr,
        CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, tag_expr)),
            then_br: Box::new(CompSpec::CantorPair {
                left: Box::new(rest_expr),
                right: Box::new(cs_or(
                    cs_eq(cs_fst(content_expr), v_expr),
                    cs_eq(cs_snd(content_expr), v_expr),
                )),
            }),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr))),
                then_br: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::CantorPair {
                        left: Box::new(CompSpec::Add {
                            left: Box::new(content_expr),
                            right: Box::new(cs_const(1)),
                        }),
                        right: Box::new(rest_expr),
                    }),
                    right: Box::new(cs_const(0)),
                }),
                else_br: Box::new(has_free_var_binary_or_quantifier()),
            }),
        },
        input);
}

///  Combined: one step of has_free_var on Eq formula returns pair(rest, 0).
pub proof fn lemma_step_eq(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        left_idx != v,
        right_idx != v,
    ensures ({
        let enc = pair(0nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input) == pair(rest, 0nat)
    }),
{
    let enc = pair(0nat, pair(left_idx, right_idx));
    assert(enc + 1 > 0nat);
    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    lemma_process_top_tag0(left_idx, right_idx, v, rest, f_enc, i);
}

///  process_top for tag 1 (In) — same structure as Eq.
proof fn lemma_process_top_tag1(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        left_idx != v,
        right_idx != v,
    ensures ({
        let enc = pair(1nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_process_top(), input) == pair(rest, 0nat)
    }),
{
    let enc = pair(1nat, pair(left_idx, right_idx));
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    //  Same extraction as tag 0
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    let fst_stack = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc + 1, rest);
    let top_enc_expr = cs_comp(CompSpec::Pred, fst_stack);
    lemma_eval_comp(CompSpec::Pred, fst_stack, input);
    lemma_eval_pred(enc + 1);
    let tag_expr = cs_fst(top_enc_expr);
    lemma_eval_fst(top_enc_expr, input);
    lemma_unpair1_pair(1nat, pair(left_idx, right_idx));
    assert(eval_comp(tag_expr, input) == 1nat);

    let rest_expr = cs_snd(stack_expr);
    lemma_eval_snd(stack_expr, input);
    lemma_unpair2_pair(enc + 1, rest);

    let content_expr = cs_snd(top_enc_expr);
    lemma_eval_snd(top_enc_expr, input);
    lemma_unpair2_pair(1nat, pair(left_idx, right_idx));
    let left_expr = cs_fst(content_expr);
    let right_expr = cs_snd(content_expr);
    lemma_eval_fst(content_expr, input);
    lemma_eval_snd(content_expr, input);
    lemma_unpair1_pair(left_idx, right_idx);
    lemma_unpair2_pair(left_idx, right_idx);

    let v_expr = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_v_extract(i, acc, f_enc, v);
    lemma_eval_eq(left_expr, v_expr, input);
    lemma_eval_eq(right_expr, v_expr, input);
    let eq_left = cs_eq(left_expr, v_expr);
    let eq_right = cs_eq(right_expr, v_expr);
    lemma_eval_add(eq_left, eq_right, input);

    //  tag == 1 ≠ 0 → else branch, then Pred(tag)==0 → then branch (In case)
    let pred_tag = cs_comp(CompSpec::Pred, tag_expr);
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(1nat);
    assert(eval_comp(pred_tag, input) == 0nat);

    //  Build the In result expression
    let in_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_or(
            cs_eq(cs_fst(content_expr), v_expr),
            cs_eq(cs_snd(content_expr), v_expr),
        )),
    };
    lemma_eval_pair(rest_expr, cs_or(
        cs_eq(cs_fst(content_expr), v_expr),
        cs_eq(cs_snd(content_expr), v_expr),
    ), input);

    //  Inner IfZero(Pred(tag)==0): then → In result
    lemma_eval_ifzero_then(pred_tag, in_result,
        CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr))),
            then_br: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::Add {
                        left: Box::new(content_expr),
                        right: Box::new(cs_const(1)),
                    }),
                    right: Box::new(rest_expr),
                }),
                right: Box::new(cs_const(0)),
            }),
            else_br: Box::new(has_free_var_binary_or_quantifier()),
        },
        input);

    //  Outer IfZero(tag!=0): else branch
    let eq_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_or(
            cs_eq(cs_fst(content_expr), v_expr),
            cs_eq(cs_snd(content_expr), v_expr),
        )),
    };
    lemma_eval_ifzero_else(tag_expr, eq_result,
        CompSpec::IfZero {
            cond: Box::new(pred_tag),
            then_br: Box::new(in_result),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr))),
                then_br: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::CantorPair {
                        left: Box::new(CompSpec::Add {
                            left: Box::new(content_expr),
                            right: Box::new(cs_const(1)),
                        }),
                        right: Box::new(rest_expr),
                    }),
                    right: Box::new(cs_const(0)),
                }),
                else_br: Box::new(has_free_var_binary_or_quantifier()),
            }),
        },
        input);
}

///  Combined: one step on In formula returns pair(rest, 0).
pub proof fn lemma_step_in(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        left_idx != v,
        right_idx != v,
    ensures ({
        let enc = pair(1nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input) == pair(rest, 0nat)
    }),
{
    let enc = pair(1nat, pair(left_idx, right_idx));
    assert(enc + 1 > 0nat) by { lemma_pair_gt_components(1nat, pair(left_idx, right_idx)); }
    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    lemma_process_top_tag1(left_idx, right_idx, v, rest, f_enc, i);
}

///  process_top for tag 2 (Not): pushes sub_enc onto stack.
proof fn lemma_process_top_tag2(
    sub_enc: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    ensures ({
        let enc = pair(2nat, sub_enc);
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_process_top(), input)
            == pair(pair(sub_enc + 1, rest), 0nat)
    }),
{
    let enc = pair(2nat, sub_enc);
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    //  Extract stack components
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    let fst_stack = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc + 1, rest);
    let top_enc_expr = cs_comp(CompSpec::Pred, fst_stack);
    lemma_eval_comp(CompSpec::Pred, fst_stack, input);
    lemma_eval_pred(enc + 1);
    let tag_expr = cs_fst(top_enc_expr);
    lemma_eval_fst(top_enc_expr, input);
    lemma_unpair1_pair(2nat, sub_enc);
    assert(eval_comp(tag_expr, input) == 2nat);

    let rest_expr = cs_snd(stack_expr);
    lemma_eval_snd(stack_expr, input);
    lemma_unpair2_pair(enc + 1, rest);

    let content_expr = cs_snd(top_enc_expr);
    lemma_eval_snd(top_enc_expr, input);
    lemma_unpair2_pair(2nat, sub_enc);
    //  content = sub_enc

    let v_expr = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_v_extract(i, acc, f_enc, v);

    //  tag == 2 ≠ 0 → else, Pred(tag)==1 ≠ 0 → else, Pred(Pred(tag))==0 → then (Not case)
    let pred_tag = cs_comp(CompSpec::Pred, tag_expr);
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(2nat);
    assert(eval_comp(pred_tag, input) == 1nat);

    let pred_pred_tag = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr));
    lemma_eval_comp(CompSpec::Pred, pred_tag, input);
    lemma_eval_pred(1nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr), input);
    assert(eval_comp(pred_pred_tag, input) == 0nat);

    //  Not result: pair(pair(content + 1, rest), 0)
    let not_result = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::Add {
                left: Box::new(content_expr),
                right: Box::new(cs_const(1)),
            }),
            right: Box::new(rest_expr),
        }),
        right: Box::new(cs_const(0)),
    };

    //  Evaluate the result
    lemma_eval_add(content_expr, cs_const(1), input);
    assert(eval_comp(content_expr, input) == sub_enc);
    let inner_pair = CompSpec::CantorPair {
        left: Box::new(CompSpec::Add {
            left: Box::new(content_expr),
            right: Box::new(cs_const(1)),
        }),
        right: Box::new(rest_expr),
    };
    lemma_eval_pair(CompSpec::Add {
        left: Box::new(content_expr),
        right: Box::new(cs_const(1)),
    }, rest_expr, input);
    lemma_eval_pair(inner_pair, cs_const(0), input);

    //  IfZero chain: tag!=0 → else, pred(tag)!=0 → else, pred(pred(tag))==0 → then
    lemma_eval_ifzero_then(pred_pred_tag, not_result,
        has_free_var_binary_or_quantifier(), input);

    //  Build the In-case result expr (needed for the else branch at tag==1 level)
    let in_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_or(
            cs_eq(cs_fst(content_expr), v_expr),
            cs_eq(cs_snd(content_expr), v_expr),
        )),
    };

    lemma_eval_ifzero_else(pred_tag, in_result,
        CompSpec::IfZero {
            cond: Box::new(pred_pred_tag),
            then_br: Box::new(not_result),
            else_br: Box::new(has_free_var_binary_or_quantifier()),
        }, input);

    let eq_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_or(
            cs_eq(cs_fst(content_expr), v_expr),
            cs_eq(cs_snd(content_expr), v_expr),
        )),
    };
    lemma_eval_ifzero_else(tag_expr, eq_result,
        CompSpec::IfZero {
            cond: Box::new(pred_tag),
            then_br: Box::new(in_result),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(pred_pred_tag),
                then_br: Box::new(not_result),
                else_br: Box::new(has_free_var_binary_or_quantifier()),
            }),
        }, input);
}

///  Combined: one step on Not formula pushes sub onto stack.
pub proof fn lemma_step_not(
    sub_enc: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    ensures ({
        let enc = pair(2nat, sub_enc);
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input)
            == pair(pair(sub_enc + 1, rest), 0nat)
    }),
{
    let enc = pair(2nat, sub_enc);
    assert(enc + 1 > 0nat) by { lemma_pair_gt_components(2nat, sub_enc); }
    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    lemma_process_top_tag2(sub_enc, v, rest, f_enc, i);
}

///  Helper: process_top dispatches to binary_or_quantifier for tags >= 3.
///  When tag >= 3, process_top passes through the IfZero chain to binary_or_quantifier.
proof fn lemma_process_top_to_binary_or_quantifier(
    tag: nat, content_val: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        tag >= 3,
    ensures ({
        let enc = pair(tag, content_val);
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_process_top(), input)
            == eval_comp(has_free_var_binary_or_quantifier(), input)
    }),
{
    let enc = pair(tag, content_val);
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    //  Same extraction as other tag cases
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    let fst_stack = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc + 1, rest);
    let top_enc_expr = cs_comp(CompSpec::Pred, fst_stack);
    lemma_eval_comp(CompSpec::Pred, fst_stack, input);
    lemma_eval_pred(enc + 1);
    let tag_expr = cs_fst(top_enc_expr);
    lemma_eval_fst(top_enc_expr, input);
    lemma_unpair1_pair(tag, content_val);
    assert(eval_comp(tag_expr, input) == tag);

    let rest_expr = cs_snd(stack_expr);
    lemma_eval_snd(stack_expr, input);
    lemma_unpair2_pair(enc + 1, rest);
    let content_expr = cs_snd(top_enc_expr);
    lemma_eval_snd(top_enc_expr, input);
    lemma_unpair2_pair(tag, content_val);
    let v_expr = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_v_extract(i, acc, f_enc, v);

    //  tag >= 3: all IfZero checks fail → reaches binary_or_quantifier
    //  tag != 0 → else
    assert(eval_comp(tag_expr, input) != 0nat);
    let pred_tag = cs_comp(CompSpec::Pred, tag_expr);
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(tag);
    assert(eval_comp(pred_tag, input) == (tag - 1) as nat);
    assert(tag - 1 >= 2);
    //  Pred(tag) != 0 → else
    let pred_pred_tag = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr));
    lemma_eval_comp(CompSpec::Pred, pred_tag, input);
    lemma_eval_pred((tag - 1) as nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr), input);
    assert(eval_comp(pred_pred_tag, input) == (tag - 2) as nat);
    assert(tag - 2 >= 1);
    //  Pred(Pred(tag)) != 0 → else → binary_or_quantifier

    //  Build result expressions for the IfZero chain
    let not_result = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::Add {
                left: Box::new(content_expr),
                right: Box::new(cs_const(1)),
            }),
            right: Box::new(rest_expr),
        }),
        right: Box::new(cs_const(0)),
    };
    let in_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_or(
            cs_eq(cs_fst(content_expr), v_expr),
            cs_eq(cs_snd(content_expr), v_expr),
        )),
    };
    let eq_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_or(
            cs_eq(cs_fst(content_expr), v_expr),
            cs_eq(cs_snd(content_expr), v_expr),
        )),
    };

    //  Chain: tag!=0 → else, pred(tag)!=0 → else, pred(pred(tag))!=0 → else → b_or_q
    lemma_eval_ifzero_else(pred_pred_tag, not_result,
        has_free_var_binary_or_quantifier(), input);
    lemma_eval_ifzero_else(pred_tag, in_result,
        CompSpec::IfZero {
            cond: Box::new(pred_pred_tag),
            then_br: Box::new(not_result),
            else_br: Box::new(has_free_var_binary_or_quantifier()),
        }, input);
    lemma_eval_ifzero_else(tag_expr, eq_result,
        CompSpec::IfZero {
            cond: Box::new(pred_tag),
            then_br: Box::new(in_result),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(pred_pred_tag),
                then_br: Box::new(not_result),
                else_br: Box::new(has_free_var_binary_or_quantifier()),
            }),
        }, input);
}

///  Combined: one step on binary formula (tags 3-6) pushes both sub-formulas.
pub proof fn lemma_step_binary(
    tag: nat, left_enc: nat, right_enc: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        3 <= tag <= 6,
    ensures ({
        let enc = pair(tag, pair(left_enc, right_enc));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input)
            == pair(pair(left_enc + 1, pair(right_enc + 1, rest)), 0nat)
    }),
{
    let content_val = pair(left_enc, right_enc);
    let enc = pair(tag, content_val);
    assert(enc + 1 > 0nat) by { lemma_pair_gt_components(tag, content_val); }
    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    lemma_process_top_to_binary_or_quantifier(tag, content_val, v, rest, f_enc, i);

    //  Now evaluate binary_or_quantifier for tags 3-6
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    //  Re-extract tag for binary_or_quantifier context
    //  binary_or_quantifier uses same extraction logic
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    let fst_stack = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc + 1, rest);
    let top_enc_expr = cs_comp(CompSpec::Pred, fst_stack);
    lemma_eval_comp(CompSpec::Pred, fst_stack, input);
    lemma_eval_pred(enc + 1);
    let tag_expr = cs_fst(top_enc_expr);
    lemma_eval_fst(top_enc_expr, input);
    lemma_unpair1_pair(tag, content_val);
    let rest_expr = cs_snd(stack_expr);
    lemma_eval_snd(stack_expr, input);
    lemma_unpair2_pair(enc + 1, rest);
    let content_expr = cs_snd(top_enc_expr);
    lemma_eval_snd(top_enc_expr, input);
    lemma_unpair2_pair(tag, content_val);

    //  tag_minus_3 = Pred(Pred(Pred(tag)))
    let pred1 = cs_comp(CompSpec::Pred, tag_expr);
    let pred2 = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr));
    let tag_minus_3 = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr)));
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(tag);
    lemma_eval_comp(CompSpec::Pred, pred1, input);
    lemma_eval_pred((tag - 1) as nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr), input);
    lemma_eval_comp(CompSpec::Pred, pred2, input);
    lemma_eval_pred((tag - 2) as nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr)), input);
    assert(eval_comp(tag_minus_3, input) == (tag - 3) as nat);

    //  cs_lt(tag_minus_3, 4): tag-3 < 4 ↔ tag <= 6 — TRUE for binary
    lemma_eval_lt(tag_minus_3, cs_const(4), input);
    assert(eval_comp(cs_lt(tag_minus_3, cs_const(4)), input) == 1nat);

    //  IfZero(lt==1): lt != 0 → else branch → binary case
    //  Binary: pair(pair(fst(content)+1, pair(snd(content)+1, rest)), 0)
    lemma_eval_fst(content_expr, input);
    lemma_eval_snd(content_expr, input);
    lemma_unpair1_pair(left_enc, right_enc);
    lemma_unpair2_pair(left_enc, right_enc);

    let left_plus_1 = CompSpec::Add { left: Box::new(cs_fst(content_expr)), right: Box::new(cs_const(1)) };
    let right_plus_1 = CompSpec::Add { left: Box::new(cs_snd(content_expr)), right: Box::new(cs_const(1)) };
    lemma_eval_add(cs_fst(content_expr), cs_const(1), input);
    lemma_eval_add(cs_snd(content_expr), cs_const(1), input);

    let binary_result = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(left_plus_1),
            right: Box::new(CompSpec::CantorPair {
                left: Box::new(right_plus_1),
                right: Box::new(rest_expr),
            }),
        }),
        right: Box::new(cs_const(0)),
    };
    lemma_eval_pair(right_plus_1, rest_expr, input);
    lemma_eval_pair(left_plus_1, CompSpec::CantorPair {
        left: Box::new(right_plus_1), right: Box::new(rest_expr),
    }, input);
    lemma_eval_pair(CompSpec::CantorPair {
        left: Box::new(left_plus_1),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(right_plus_1),
            right: Box::new(rest_expr),
        }),
    }, cs_const(0), input);

    //  IfZero(lt): nonzero → else → binary_result
    let v_expr = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_v_extract(i, acc, f_enc, v);
    let quantifier_branch = CompSpec::IfZero {
        cond: Box::new(cs_eq(cs_fst(content_expr), v_expr)),
        then_br: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::Add {
                    left: Box::new(cs_snd(content_expr)),
                    right: Box::new(cs_const(1)),
                }),
                right: Box::new(rest_expr),
            }),
            right: Box::new(cs_const(0)),
        }),
        else_br: Box::new(CompSpec::CantorPair {
            left: Box::new(rest_expr),
            right: Box::new(cs_const(0)),
        }),
    };
    lemma_eval_ifzero_else(
        cs_lt(tag_minus_3, cs_const(4)),
        quantifier_branch,
        binary_result,
        input);
}

///  Combined: one step on quantifier (tags 7-8) with var == v: skip (returns pair(rest, 0)).
pub proof fn lemma_step_quantifier_bound(
    tag: nat, var: nat, sub_enc: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        7 <= tag <= 8,
        var == v,
    ensures ({
        let enc = pair(tag, pair(var, sub_enc));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input) == pair(rest, 0nat)
    }),
{
    let content_val = pair(var, sub_enc);
    let enc = pair(tag, content_val);
    assert(enc + 1 > 0nat) by { lemma_pair_gt_components(tag, content_val); }
    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    lemma_process_top_to_binary_or_quantifier(tag, content_val, v, rest, f_enc, i);

    //  Evaluate binary_or_quantifier for tags 7-8
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    let fst_stack = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc + 1, rest);
    let top_enc_expr = cs_comp(CompSpec::Pred, fst_stack);
    lemma_eval_comp(CompSpec::Pred, fst_stack, input);
    lemma_eval_pred(enc + 1);
    let tag_expr = cs_fst(top_enc_expr);
    lemma_eval_fst(top_enc_expr, input);
    lemma_unpair1_pair(tag, content_val);
    let rest_expr = cs_snd(stack_expr);
    lemma_eval_snd(stack_expr, input);
    lemma_unpair2_pair(enc + 1, rest);
    let content_expr = cs_snd(top_enc_expr);
    lemma_eval_snd(top_enc_expr, input);
    lemma_unpair2_pair(tag, content_val);

    //  tag_minus_3 >= 4 → lt returns 0 → IfZero takes then branch (quantifier)
    let pred1 = cs_comp(CompSpec::Pred, tag_expr);
    let pred2 = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr));
    let tag_minus_3 = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr)));
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(tag);
    lemma_eval_comp(CompSpec::Pred, pred1, input);
    lemma_eval_pred((tag - 1) as nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr), input);
    lemma_eval_comp(CompSpec::Pred, pred2, input);
    lemma_eval_pred((tag - 2) as nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr)), input);
    assert(eval_comp(tag_minus_3, input) == (tag - 3) as nat);
    assert((tag - 3) as nat >= 4);

    lemma_eval_lt(tag_minus_3, cs_const(4), input);
    assert(eval_comp(cs_lt(tag_minus_3, cs_const(4)), input) == 0nat);

    //  Quantifier branch: IfZero(cs_eq(fst(content), v))
    let v_expr = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_v_extract(i, acc, f_enc, v);
    lemma_eval_fst(content_expr, input);
    lemma_unpair1_pair(var, sub_enc);
    //  fst(content) = var = v → cs_eq returns 1
    lemma_eval_eq(cs_fst(content_expr), v_expr, input);
    assert(eval_comp(cs_eq(cs_fst(content_expr), v_expr), input) == 1nat);

    //  IfZero(1): nonzero → else branch → pair(rest, 0) (skip)
    let push_sub = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::Add {
                left: Box::new(cs_snd(content_expr)),
                right: Box::new(cs_const(1)),
            }),
            right: Box::new(rest_expr),
        }),
        right: Box::new(cs_const(0)),
    };
    let skip_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_const(0)),
    };
    lemma_eval_pair(rest_expr, cs_const(0), input);
    lemma_eval_ifzero_else(
        cs_eq(cs_fst(content_expr), v_expr),
        push_sub, skip_result, input);

    //  Outer IfZero(lt==0): then branch → quantifier case
    let binary_result = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::Add { left: Box::new(cs_fst(content_expr)), right: Box::new(cs_const(1)) }),
            right: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::Add { left: Box::new(cs_snd(content_expr)), right: Box::new(cs_const(1)) }),
                right: Box::new(rest_expr),
            }),
        }),
        right: Box::new(cs_const(0)),
    };
    let quantifier_branch = CompSpec::IfZero {
        cond: Box::new(cs_eq(cs_fst(content_expr), v_expr)),
        then_br: Box::new(push_sub),
        else_br: Box::new(skip_result),
    };
    lemma_eval_ifzero_then(
        cs_lt(tag_minus_3, cs_const(4)),
        quantifier_branch, binary_result, input);
}

///  Combined: one step on quantifier (tags 7-8) with var != v: push sub.
pub proof fn lemma_step_quantifier_free(
    tag: nat, var: nat, sub_enc: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires
        7 <= tag <= 8,
        var != v,
    ensures ({
        let enc = pair(tag, pair(var, sub_enc));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        eval_comp(has_free_var_step(), input)
            == pair(pair(sub_enc + 1, rest), 0nat)
    }),
{
    let content_val = pair(var, sub_enc);
    let enc = pair(tag, content_val);
    assert(enc + 1 > 0nat) by { lemma_pair_gt_components(tag, content_val); }
    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    lemma_process_top_to_binary_or_quantifier(tag, content_val, v, rest, f_enc, i);

    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    //  Same tag extraction as bound case
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    let stack_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    let fst_stack = cs_fst(stack_expr);
    lemma_eval_fst(stack_expr, input);
    lemma_unpair1_pair(enc + 1, rest);
    let top_enc_expr = cs_comp(CompSpec::Pred, fst_stack);
    lemma_eval_comp(CompSpec::Pred, fst_stack, input);
    lemma_eval_pred(enc + 1);
    let tag_expr = cs_fst(top_enc_expr);
    lemma_eval_fst(top_enc_expr, input);
    lemma_unpair1_pair(tag, content_val);
    let rest_expr = cs_snd(stack_expr);
    lemma_eval_snd(stack_expr, input);
    lemma_unpair2_pair(enc + 1, rest);
    let content_expr = cs_snd(top_enc_expr);
    lemma_eval_snd(top_enc_expr, input);
    lemma_unpair2_pair(tag, content_val);

    //  tag_minus_3 >= 4 → lt returns 0 → quantifier branch
    let pred1 = cs_comp(CompSpec::Pred, tag_expr);
    let pred2 = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr));
    let tag_minus_3 = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr)));
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(tag);
    lemma_eval_comp(CompSpec::Pred, pred1, input);
    lemma_eval_pred((tag - 1) as nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr), input);
    lemma_eval_comp(CompSpec::Pred, pred2, input);
    lemma_eval_pred((tag - 2) as nat);
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr)), input);
    assert(eval_comp(tag_minus_3, input) == (tag - 3) as nat);
    assert((tag - 3) as nat >= 4);

    lemma_eval_lt(tag_minus_3, cs_const(4), input);
    assert(eval_comp(cs_lt(tag_minus_3, cs_const(4)), input) == 0nat);

    //  Quantifier: IfZero(cs_eq(fst(content), v))
    let v_expr = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_v_extract(i, acc, f_enc, v);
    lemma_eval_fst(content_expr, input);
    lemma_unpair1_pair(var, sub_enc);
    //  fst(content) = var != v → cs_eq returns 0
    lemma_eval_eq(cs_fst(content_expr), v_expr, input);
    assert(eval_comp(cs_eq(cs_fst(content_expr), v_expr), input) == 0nat);

    //  IfZero(0): zero → then branch → push sub
    lemma_eval_snd(content_expr, input);
    lemma_unpair2_pair(var, sub_enc);
    lemma_eval_add(cs_snd(content_expr), cs_const(1), input);
    let push_sub = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::Add {
                left: Box::new(cs_snd(content_expr)),
                right: Box::new(cs_const(1)),
            }),
            right: Box::new(rest_expr),
        }),
        right: Box::new(cs_const(0)),
    };
    let skip_result = CompSpec::CantorPair {
        left: Box::new(rest_expr),
        right: Box::new(cs_const(0)),
    };
    let inner_pair = CompSpec::CantorPair {
        left: Box::new(CompSpec::Add {
            left: Box::new(cs_snd(content_expr)),
            right: Box::new(cs_const(1)),
        }),
        right: Box::new(rest_expr),
    };
    lemma_eval_pair(CompSpec::Add {
        left: Box::new(cs_snd(content_expr)),
        right: Box::new(cs_const(1)),
    }, rest_expr, input);
    lemma_eval_pair(inner_pair, cs_const(0), input);

    lemma_eval_ifzero_then(
        cs_eq(cs_fst(content_expr), v_expr),
        push_sub, skip_result, input);

    //  Outer IfZero(lt==0): then branch → quantifier case
    let binary_result = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::Add { left: Box::new(cs_fst(content_expr)), right: Box::new(cs_const(1)) }),
            right: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::Add { left: Box::new(cs_snd(content_expr)), right: Box::new(cs_const(1)) }),
                right: Box::new(rest_expr),
            }),
        }),
        right: Box::new(cs_const(0)),
    };
    let quantifier_branch = CompSpec::IfZero {
        cond: Box::new(cs_eq(cs_fst(content_expr), v_expr)),
        then_br: Box::new(push_sub),
        else_br: Box::new(skip_result),
    };
    lemma_eval_ifzero_then(
        cs_lt(tag_minus_3, cs_const(4)),
        quantifier_branch, binary_result, input);
}

} //  verus!
