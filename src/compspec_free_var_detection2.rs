use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_decode::br_acc;
use crate::compspec_free_var_helpers::*;

verus! {

//  Isolated: Atomic step helpers for detection direction.

#[verifier::rlimit(500)]
pub proof fn lemma_step_eq_found(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires left_idx == v || right_idx == v,
    ensures ({
        let enc = pair(0nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        let result = eval_comp(has_free_var_step(), input);
        unpair2(result) != 0
    }),
{
    let enc = pair(0nat, pair(left_idx, right_idx));
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    //  For tag=0 (Eq), process_top's first IfZero takes then branch directly
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    lemma_eval_fst(cs_fst(br_acc()), input);
    lemma_unpair1_pair(enc + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), input);
    lemma_unpair2_pair(enc + 1, rest);
    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
    lemma_eval_pred(enc + 1);
    let top_enc_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    lemma_eval_fst(top_enc_cs, input);
    lemma_unpair1_pair(0nat, pair(left_idx, right_idx));
    lemma_eval_snd(top_enc_cs, input);
    lemma_unpair2_pair(0nat, pair(left_idx, right_idx));
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, pair(f_enc, v)));
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_unpair2_pair(acc, pair(f_enc, v));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
    lemma_unpair2_pair(f_enc, v);
    let content_cs = cs_snd(top_enc_cs);
    let v_cs = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_fst(content_cs, input);
    lemma_unpair1_pair(left_idx, right_idx);
    lemma_eval_snd(content_cs, input);
    lemma_unpair2_pair(left_idx, right_idx);
    lemma_eval_eq(cs_fst(content_cs), v_cs, input);
    lemma_eval_eq(cs_snd(content_cs), v_cs, input);
    let eq_l = cs_eq(cs_fst(content_cs), v_cs);
    let eq_r = cs_eq(cs_snd(content_cs), v_cs);
    lemma_eval_add(eq_l, eq_r, input);
    lemma_eval_pair(cs_snd(cs_fst(br_acc())), cs_or(eq_l, eq_r), input);
    lemma_unpair2_pair(rest, eval_comp(eq_l, input) + eval_comp(eq_r, input));
}

//  Isolated: In step helper for detection direction.
//  Separate file to avoid sibling function body pollution.
#[verifier::rlimit(500)]
pub proof fn lemma_step_in_found(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires left_idx == v || right_idx == v,
    ensures ({
        let enc = pair(1nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        let result = eval_comp(has_free_var_step(), input);
        unpair2(result) != 0
    }),
{
    let enc = pair(1nat, pair(left_idx, right_idx));
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);

    //  Evaluate process_top for tag=1 (In)
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    lemma_eval_fst(cs_fst(br_acc()), input);
    lemma_unpair1_pair(enc + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), input);
    lemma_unpair2_pair(enc + 1, rest);
    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
    lemma_eval_pred(enc + 1);
    let top_enc_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    lemma_eval_fst(top_enc_cs, input);
    lemma_unpair1_pair(1nat, pair(left_idx, right_idx));
    let tag_cs = cs_fst(top_enc_cs);
    let content_cs = cs_snd(top_enc_cs);
    //  tag=1 → first IfZero (tag==0) takes else
    lemma_eval_ifzero_else(tag_cs,
        CompSpec::CantorPair { left: Box::new(cs_snd(cs_fst(br_acc()))),
            right: Box::new(cs_or(cs_eq(cs_fst(content_cs), cs_snd(cs_snd(cs_snd(CompSpec::Id)))),
                                  cs_eq(cs_snd(content_cs), cs_snd(cs_snd(cs_snd(CompSpec::Id)))))) },
        CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, tag_cs)),
            then_br: Box::new(CompSpec::CantorPair { left: Box::new(cs_snd(cs_fst(br_acc()))),
                right: Box::new(cs_or(cs_eq(cs_fst(content_cs), cs_snd(cs_snd(cs_snd(CompSpec::Id)))),
                                      cs_eq(cs_snd(content_cs), cs_snd(cs_snd(cs_snd(CompSpec::Id)))))) }),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_cs))),
                then_br: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::CantorPair { left: Box::new(CompSpec::Add { left: Box::new(content_cs), right: Box::new(cs_const(1)) }), right: Box::new(cs_snd(cs_fst(br_acc()))) }),
                    right: Box::new(cs_const(0)) }),
                else_br: Box::new(has_free_var_binary_or_quantifier()),
            }),
        }, input);
    //  Pred(1)=0 → second IfZero takes then (In result)
    lemma_eval_comp(CompSpec::Pred, tag_cs, input);
    lemma_eval_pred(1nat);
    let v_cs = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    let in_result = CompSpec::CantorPair { left: Box::new(cs_snd(cs_fst(br_acc()))),
        right: Box::new(cs_or(cs_eq(cs_fst(content_cs), v_cs), cs_eq(cs_snd(content_cs), v_cs))) };
    lemma_eval_ifzero_then(cs_comp(CompSpec::Pred, tag_cs), in_result,
        CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_cs))),
            then_br: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::CantorPair { left: Box::new(CompSpec::Add { left: Box::new(content_cs), right: Box::new(cs_const(1)) }), right: Box::new(cs_snd(cs_fst(br_acc()))) }),
                right: Box::new(cs_const(0)) }),
            else_br: Box::new(has_free_var_binary_or_quantifier()),
        }, input);
    //  Now eval(process_top, input) == eval(in_result, input)
    lemma_eval_snd(top_enc_cs, input);
    lemma_unpair2_pair(1nat, pair(left_idx, right_idx));
    //  v
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, pair(f_enc, v)));
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_unpair2_pair(acc, pair(f_enc, v));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
    lemma_unpair2_pair(f_enc, v);
    //  terms
    lemma_eval_fst(content_cs, input);
    lemma_unpair1_pair(left_idx, right_idx);
    lemma_eval_snd(content_cs, input);
    lemma_unpair2_pair(left_idx, right_idx);
    //  found = or(eq(left,v), eq(right,v))
    lemma_eval_eq(cs_fst(content_cs), v_cs, input);
    lemma_eval_eq(cs_snd(content_cs), v_cs, input);
    let eq_l = cs_eq(cs_fst(content_cs), v_cs);
    let eq_r = cs_eq(cs_snd(content_cs), v_cs);
    lemma_eval_add(eq_l, eq_r, input);
    lemma_eval_pair(cs_snd(cs_fst(br_acc())), cs_or(eq_l, eq_r), input);
    lemma_unpair2_pair(rest, eval_comp(eq_l, input) + eval_comp(eq_r, input));
}

} // verus!
