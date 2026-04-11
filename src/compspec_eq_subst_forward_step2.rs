use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_eq_subst_backward::{
    lemma_eq_subst_dispatch,
    lemma_esb_extract,
    lemma_esb_dispatch_unary,
    lemma_esb_dispatch_binary,
    lemma_esb_dispatch_quant,
};

verus! {

///  Common entry extraction: establishes eval facts for entry, left_node, right_node, etc.
///  Not a separate function — call sites inline this pattern.

///  Forward Not step: both tags = 2, pushes sub-entry, valid = 1.
#[verifier::rlimit(800)]
pub proof fn lemma_eq_subst_forward_step_unary(
    left_node: nat, right_node: nat,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat, x_enc: nat, y_enc: nat,
)
    requires
        valid > 0,
        unpair1(left_node) == 2,
        unpair1(right_node) == 2,
    ensures ({
        let entry_val = pair(left_node, right_node) + 1;
        let acc = pair(pair(entry_val, rest_val), valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        let n = pair(counter, pair(acc, s));
        let sub_entry = pair(unpair2(left_node), unpair2(right_node));
        eval_comp(check_eq_subst_step(), n) == pair(pair(sub_entry + 1, rest_val), 1nat)
    }),
{
    hide(eval_comp);
    let entry_val = pair(left_node, right_node) + 1;
    let acc = pair(pair(entry_val, rest_val), valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    //  Dispatch
    assert(eval_comp(check_eq_subst_step(), n)
        == eval_comp(check_eq_subst_process(), n)) by {
        reveal(eval_comp);
        lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    };

    //  Entry extraction
    assert(eval_comp(esb_entry(), n) == pair(left_node, right_node)) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
    };
    assert(eval_comp(esb_left_node(), n) == left_node) by {
        reveal(eval_comp); lemma_eval_fst(esb_entry(), n);
        lemma_unpair1_pair(left_node, right_node);
    };
    assert(eval_comp(esb_right_node(), n) == right_node) by {
        reveal(eval_comp); lemma_eval_snd(esb_entry(), n);
        lemma_unpair2_pair(left_node, right_node);
    };
    assert(eval_comp(esb_left_tag(), n) == 2) by {
        reveal(eval_comp); lemma_eval_fst(esb_left_node(), n);
    };
    assert(eval_comp(esb_right_tag(), n) == 2) by {
        reveal(eval_comp); lemma_eval_fst(esb_right_node(), n);
    };
    assert(eval_comp(esb_rest(), n) == rest_val) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_snd(cs_fst(br_acc()), n);
        lemma_unpair2_pair(entry_val, rest_val);
    };

    //  Unary dispatch
    assert(eval_comp(check_eq_subst_process(), n) == eval_comp(esb_unary_ok(), n)) by {
        reveal(eval_comp);
        lemma_esb_dispatch_unary(n, 2);
    };

    //  Evaluate esb_unary_ok
    assert(eval_comp(cs_snd(esb_left_node()), n) == unpair2(left_node)) by {
        reveal(eval_comp); lemma_eval_snd(esb_left_node(), n);
    };
    assert(eval_comp(cs_snd(esb_right_node()), n) == unpair2(right_node)) by {
        reveal(eval_comp); lemma_eval_snd(esb_right_node(), n);
    };
    let ue_cs = cs_pair(cs_snd(esb_left_node()), cs_snd(esb_right_node()));
    assert(eval_comp(ue_cs, n) == pair(unpair2(left_node), unpair2(right_node))) by {
        reveal(eval_comp);
        lemma_eval_pair(cs_snd(esb_left_node()), cs_snd(esb_right_node()), n);
    };
    let sub_entry = pair(unpair2(left_node), unpair2(right_node));
    assert(eval_comp(CompSpec::Add { left: Box::new(ue_cs), right: Box::new(cs_const(1)) }, n)
        == sub_entry + 1) by {
        reveal(eval_comp); lemma_eval_add(ue_cs, cs_const(1), n);
    };
    //  tags_match = cs_eq(2, 2) = 1
    assert(eval_comp(esb_tags_match(), n) == 1nat) by {
        reveal(eval_comp); lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
    };
    //  Result
    let stack_cs = cs_pair(
        CompSpec::Add { left: Box::new(ue_cs), right: Box::new(cs_const(1)) },
        esb_rest());
    assert(eval_comp(stack_cs, n) == pair(sub_entry + 1, rest_val)) by {
        reveal(eval_comp);
        lemma_eval_pair(
            CompSpec::Add { left: Box::new(ue_cs), right: Box::new(cs_const(1)) },
            esb_rest(), n);
    };
    assert(eval_comp(esb_unary_ok(), n) == pair(pair(sub_entry + 1, rest_val), 1nat)) by {
        reveal(eval_comp); lemma_eval_pair(stack_cs, esb_tags_match(), n);
    };
}

///  Forward Binary step: tags match (3-6), pushes two child entries, valid = 1.
#[verifier::rlimit(800)]
pub proof fn lemma_eq_subst_forward_step_binary(
    left_node: nat, right_node: nat,
    tag: nat, rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat, x_enc: nat, y_enc: nat,
)
    requires
        valid > 0,
        tag >= 3, tag <= 6,
        unpair1(left_node) == tag,
        unpair1(right_node) == tag,
    ensures ({
        let entry_val = pair(left_node, right_node) + 1;
        let acc = pair(pair(entry_val, rest_val), valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        let n = pair(counter, pair(acc, s));
        let lc = unpair2(left_node); let rc = unpair2(right_node);
        let el = pair(unpair1(lc), unpair1(rc));
        let er = pair(unpair2(lc), unpair2(rc));
        eval_comp(check_eq_subst_step(), n)
            == pair(pair(el + 1, pair(er + 1, rest_val)), 1nat)
    }),
{
    hide(eval_comp);
    let entry_val = pair(left_node, right_node) + 1;
    let acc = pair(pair(entry_val, rest_val), valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    //  Dispatch + entry extraction (same pattern)
    assert(eval_comp(check_eq_subst_step(), n)
        == eval_comp(check_eq_subst_process(), n)) by {
        reveal(eval_comp);
        lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    };
    assert(eval_comp(esb_entry(), n) == pair(left_node, right_node)) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
    };
    assert(eval_comp(esb_left_node(), n) == left_node) by {
        reveal(eval_comp); lemma_eval_fst(esb_entry(), n);
        lemma_unpair1_pair(left_node, right_node);
    };
    assert(eval_comp(esb_right_node(), n) == right_node) by {
        reveal(eval_comp); lemma_eval_snd(esb_entry(), n);
        lemma_unpair2_pair(left_node, right_node);
    };
    assert(eval_comp(esb_left_tag(), n) == tag) by {
        reveal(eval_comp); lemma_eval_fst(esb_left_node(), n);
    };
    assert(eval_comp(esb_rest(), n) == rest_val) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_snd(cs_fst(br_acc()), n);
        lemma_unpair2_pair(entry_val, rest_val);
    };

    //  Binary dispatch
    assert(eval_comp(check_eq_subst_process(), n) == eval_comp(esb_binary_ok(), n)) by {
        reveal(eval_comp); lemma_esb_dispatch_binary(n, tag);
    };

    //  Content
    let lc = unpair2(left_node); let rc = unpair2(right_node);
    assert(eval_comp(cs_snd(esb_left_node()), n) == lc) by {
        reveal(eval_comp); lemma_eval_snd(esb_left_node(), n);
    };
    assert(eval_comp(cs_snd(esb_right_node()), n) == rc) by {
        reveal(eval_comp); lemma_eval_snd(esb_right_node(), n);
    };
    //  Children
    let el_cs = cs_pair(cs_fst(cs_snd(esb_left_node())), cs_fst(cs_snd(esb_right_node())));
    let er_cs = cs_pair(cs_snd(cs_snd(esb_left_node())), cs_snd(cs_snd(esb_right_node())));
    assert(eval_comp(cs_fst(cs_snd(esb_left_node())), n) == unpair1(lc)) by {
        reveal(eval_comp); lemma_eval_fst(cs_snd(esb_left_node()), n);
    };
    assert(eval_comp(cs_fst(cs_snd(esb_right_node())), n) == unpair1(rc)) by {
        reveal(eval_comp); lemma_eval_fst(cs_snd(esb_right_node()), n);
    };
    assert(eval_comp(cs_snd(cs_snd(esb_left_node())), n) == unpair2(lc)) by {
        reveal(eval_comp); lemma_eval_snd(cs_snd(esb_left_node()), n);
    };
    assert(eval_comp(cs_snd(cs_snd(esb_right_node())), n) == unpair2(rc)) by {
        reveal(eval_comp); lemma_eval_snd(cs_snd(esb_right_node()), n);
    };
    let el = pair(unpair1(lc), unpair1(rc));
    let er = pair(unpair2(lc), unpair2(rc));
    assert(eval_comp(el_cs, n) == el) by {
        reveal(eval_comp);
        lemma_eval_pair(cs_fst(cs_snd(esb_left_node())), cs_fst(cs_snd(esb_right_node())), n);
    };
    assert(eval_comp(er_cs, n) == er) by {
        reveal(eval_comp);
        lemma_eval_pair(cs_snd(cs_snd(esb_left_node())), cs_snd(cs_snd(esb_right_node())), n);
    };
    //  el+1, er+1
    let el1 = CompSpec::Add { left: Box::new(el_cs), right: Box::new(cs_const(1)) };
    let er1 = CompSpec::Add { left: Box::new(er_cs), right: Box::new(cs_const(1)) };
    assert(eval_comp(el1, n) == el + 1) by {
        reveal(eval_comp); lemma_eval_add(el_cs, cs_const(1), n);
    };
    assert(eval_comp(er1, n) == er + 1) by {
        reveal(eval_comp); lemma_eval_add(er_cs, cs_const(1), n);
    };
    //  Stack + tags_match
    assert(eval_comp(esb_tags_match(), n) == 1nat) by {
        reveal(eval_comp);
        lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
        lemma_eval_fst(esb_right_node(), n);
        lemma_unpair1_pair(left_node, right_node);
    };
    assert(eval_comp(cs_pair(er1, esb_rest()), n) == pair(er + 1, rest_val)) by {
        reveal(eval_comp); lemma_eval_pair(er1, esb_rest(), n);
    };
    let new_stack = cs_pair(el1, cs_pair(er1, esb_rest()));
    assert(eval_comp(new_stack, n) == pair(el + 1, pair(er + 1, rest_val))) by {
        reveal(eval_comp); lemma_eval_pair(el1, cs_pair(er1, esb_rest()), n);
    };
    assert(eval_comp(esb_binary_ok(), n) == pair(pair(el + 1, pair(er + 1, rest_val)), 1nat)) by {
        reveal(eval_comp); lemma_eval_pair(new_stack, esb_tags_match(), n);
    };
}

///  Forward Quantifier step: tags match (7-8), pushes sub-entry, valid = bound_match.
#[verifier::rlimit(800)]
pub proof fn lemma_eq_subst_forward_step_quant(
    left_node: nat, right_node: nat,
    tag: nat, rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat, x_enc: nat, y_enc: nat,
)
    requires
        valid > 0,
        tag >= 7,
        unpair1(left_node) == tag,
        unpair1(right_node) == tag,
    ensures ({
        let entry_val = pair(left_node, right_node) + 1;
        let acc = pair(pair(entry_val, rest_val), valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        let n = pair(counter, pair(acc, s));
        let lc = unpair2(left_node); let rc = unpair2(right_node);
        let sub_entry = pair(unpair2(lc), unpair2(rc));
        let bound_match: nat = if unpair1(lc) == unpair1(rc) { 1nat } else { 0nat };
        eval_comp(check_eq_subst_step(), n)
            == pair(pair(sub_entry + 1, rest_val), bound_match)
    }),
{
    hide(eval_comp);
    let entry_val = pair(left_node, right_node) + 1;
    let acc = pair(pair(entry_val, rest_val), valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    //  Dispatch + entry extraction
    assert(eval_comp(check_eq_subst_step(), n)
        == eval_comp(check_eq_subst_process(), n)) by {
        reveal(eval_comp);
        lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    };
    assert(eval_comp(esb_entry(), n) == pair(left_node, right_node)) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
    };
    assert(eval_comp(esb_left_node(), n) == left_node) by {
        reveal(eval_comp); lemma_eval_fst(esb_entry(), n);
        lemma_unpair1_pair(left_node, right_node);
    };
    assert(eval_comp(esb_right_node(), n) == right_node) by {
        reveal(eval_comp); lemma_eval_snd(esb_entry(), n);
        lemma_unpair2_pair(left_node, right_node);
    };
    assert(eval_comp(esb_left_tag(), n) == tag) by {
        reveal(eval_comp); lemma_eval_fst(esb_left_node(), n);
    };
    assert(eval_comp(esb_rest(), n) == rest_val) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_snd(cs_fst(br_acc()), n);
        lemma_unpair2_pair(entry_val, rest_val);
    };

    //  Quant dispatch
    assert(eval_comp(check_eq_subst_process(), n) == eval_comp(esb_quant_ok(), n)) by {
        reveal(eval_comp); lemma_esb_dispatch_quant(n, tag);
    };

    //  Content
    let lc = unpair2(left_node); let rc = unpair2(right_node);
    assert(eval_comp(cs_snd(esb_left_node()), n) == lc) by {
        reveal(eval_comp); lemma_eval_snd(esb_left_node(), n);
    };
    assert(eval_comp(cs_snd(esb_right_node()), n) == rc) by {
        reveal(eval_comp); lemma_eval_snd(esb_right_node(), n);
    };
    //  bound vars
    let lbv = unpair1(lc); let rbv = unpair1(rc);
    assert(eval_comp(cs_fst(cs_snd(esb_left_node())), n) == lbv) by {
        reveal(eval_comp); lemma_eval_fst(cs_snd(esb_left_node()), n);
    };
    assert(eval_comp(cs_fst(cs_snd(esb_right_node())), n) == rbv) by {
        reveal(eval_comp); lemma_eval_fst(cs_snd(esb_right_node()), n);
    };
    //  sub-entry
    let se_cs = cs_pair(cs_snd(cs_snd(esb_left_node())), cs_snd(cs_snd(esb_right_node())));
    assert(eval_comp(cs_snd(cs_snd(esb_left_node())), n) == unpair2(lc)) by {
        reveal(eval_comp); lemma_eval_snd(cs_snd(esb_left_node()), n);
    };
    assert(eval_comp(cs_snd(cs_snd(esb_right_node())), n) == unpair2(rc)) by {
        reveal(eval_comp); lemma_eval_snd(cs_snd(esb_right_node()), n);
    };
    let sub_entry = pair(unpair2(lc), unpair2(rc));
    assert(eval_comp(se_cs, n) == sub_entry) by {
        reveal(eval_comp);
        lemma_eval_pair(cs_snd(cs_snd(esb_left_node())), cs_snd(cs_snd(esb_right_node())), n);
    };
    let se1 = CompSpec::Add { left: Box::new(se_cs), right: Box::new(cs_const(1)) };
    assert(eval_comp(se1, n) == sub_entry + 1) by {
        reveal(eval_comp); lemma_eval_add(se_cs, cs_const(1), n);
    };
    //  tags_match * bound_match
    assert(eval_comp(esb_tags_match(), n) == 1nat) by {
        reveal(eval_comp);
        lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
        lemma_eval_fst(esb_right_node(), n);
        lemma_unpair1_pair(left_node, right_node);
    };
    let bound_eq = cs_eq(cs_fst(cs_snd(esb_left_node())), cs_fst(cs_snd(esb_right_node())));
    let bound_match: nat = if lbv == rbv { 1nat } else { 0nat };
    assert(eval_comp(bound_eq, n) == bound_match) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(cs_snd(esb_left_node())), cs_fst(cs_snd(esb_right_node())), n);
    };
    let valid_cs = cs_and(esb_tags_match(), bound_eq);
    assert(eval_comp(valid_cs, n) == bound_match) by {
        reveal(eval_comp); lemma_eval_cs_and(esb_tags_match(), bound_eq, n);
    };
    //  t_enc, t_set for quant (same as input — not changed)
    //  Stack
    let new_stack = cs_pair(se1, esb_rest());
    assert(eval_comp(new_stack, n) == pair(sub_entry + 1, rest_val)) by {
        reveal(eval_comp); lemma_eval_pair(se1, esb_rest(), n);
    };
    assert(eval_comp(esb_quant_ok(), n) == pair(pair(sub_entry + 1, rest_val), bound_match)) by {
        reveal(eval_comp); lemma_eval_pair(new_stack, valid_cs, n);
    };
}

///  For unary dispatch (left_tag == 2): if step valid != 0, then tags match.
///  Used in walk's _ => branch to derive contradiction.
#[verifier::rlimit(500)]
pub proof fn lemma_esb_forward_unary_tags_match(
    left_node: nat, right_node: nat,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat, x_enc: nat, y_enc: nat,
)
    requires
        valid > 0,
        unpair1(left_node) == 2,
    ensures ({
        let entry_val = pair(left_node, right_node) + 1;
        let acc = pair(pair(entry_val, rest_val), valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        let n = pair(counter, pair(acc, s));
        unpair2(eval_comp(check_eq_subst_step(), n)) != 0 ==>
            unpair1(right_node) == 2
    }),
{
    hide(eval_comp);
    let entry_val = pair(left_node, right_node) + 1;
    let acc = pair(pair(entry_val, rest_val), valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    //  Dispatch + entry extraction (reuse the unary step pattern)
    assert(eval_comp(check_eq_subst_step(), n)
        == eval_comp(check_eq_subst_process(), n)) by {
        reveal(eval_comp);
        lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    };
    //  Entry extraction
    assert(eval_comp(esb_left_tag(), n) == 2) by {
        reveal(eval_comp);
        crate::compspec_free_var_helpers::lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
        lemma_eval_fst(esb_entry(), n);
        lemma_unpair1_pair(left_node, right_node);
        lemma_eval_fst(esb_left_node(), n);
    };
    //  Unary dispatch
    assert(eval_comp(check_eq_subst_process(), n)
        == eval_comp(esb_unary_ok(), n)) by {
        reveal(eval_comp);
        lemma_esb_dispatch_unary(n, 2);
    };
    //  Right node + right tag
    assert(eval_comp(esb_entry(), n) == pair(left_node, right_node)) by {
        reveal(eval_comp);
        crate::compspec_free_var_helpers::lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
    };
    assert(eval_comp(esb_right_node(), n) == right_node) by {
        reveal(eval_comp); lemma_eval_snd(esb_entry(), n);
        lemma_unpair2_pair(left_node, right_node);
    };
    assert(eval_comp(esb_right_tag(), n) == unpair1(right_node)) by {
        reveal(eval_comp); lemma_eval_fst(esb_right_node(), n);
    };
    let tm: nat = if unpair1(right_node) == 2 { 1nat } else { 0nat };
    assert(eval_comp(esb_tags_match(), n) == tm) by {
        reveal(eval_comp);
        lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
    };
    //  Result: pair(new_stack, tags_match)
    //  unpair2(result) == tags_match
    assert(unpair2(eval_comp(esb_unary_ok(), n)) == tm) by {
        reveal(eval_comp);
        crate::compspec_free_var_helpers::lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_snd(cs_fst(br_acc()), n);
        lemma_unpair2_pair(entry_val, rest_val);
        //  Rest
        lemma_eval_snd(esb_left_node(), n);
        lemma_eval_snd(esb_right_node(), n);
        let ue_cs = cs_pair(cs_snd(esb_left_node()), cs_snd(esb_right_node()));
        lemma_eval_pair(cs_snd(esb_left_node()), cs_snd(esb_right_node()), n);
        lemma_eval_add(ue_cs, cs_const(1), n);
        let stack_cs = cs_pair(
            CompSpec::Add { left: Box::new(ue_cs), right: Box::new(cs_const(1)) },
            esb_rest());
        lemma_eval_pair(
            CompSpec::Add { left: Box::new(ue_cs), right: Box::new(cs_const(1)) },
            esb_rest(), n);
        lemma_eval_pair(stack_cs, esb_tags_match(), n);
        lemma_unpair2_pair(eval_comp(stack_cs, n), tm);
    };
}

///  For binary dispatch (left_tag in 3..=6): if step valid != 0, then tags match.
#[verifier::rlimit(800)]
pub proof fn lemma_esb_forward_binary_tags_match(
    left_node: nat, right_node: nat, tag: nat,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat, x_enc: nat, y_enc: nat,
)
    requires
        valid > 0,
        tag >= 3, tag <= 6,
        unpair1(left_node) == tag,
    ensures ({
        let entry_val = pair(left_node, right_node) + 1;
        let acc = pair(pair(entry_val, rest_val), valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        let n = pair(counter, pair(acc, s));
        unpair2(eval_comp(check_eq_subst_step(), n)) != 0 ==>
            unpair1(right_node) == tag
    }),
{
    hide(eval_comp);
    let entry_val = pair(left_node, right_node) + 1;
    let acc = pair(pair(entry_val, rest_val), valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    //  Dispatch
    assert(eval_comp(check_eq_subst_step(), n)
        == eval_comp(check_eq_subst_process(), n)) by {
        reveal(eval_comp);
        lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    };
    //  Entry extraction
    assert(eval_comp(esb_left_tag(), n) == tag) by {
        reveal(eval_comp);
        crate::compspec_free_var_helpers::lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
        lemma_eval_fst(esb_entry(), n);
        lemma_unpair1_pair(left_node, right_node);
        lemma_eval_fst(esb_left_node(), n);
    };
    //  Binary dispatch
    assert(eval_comp(check_eq_subst_process(), n)
        == eval_comp(esb_binary_ok(), n)) by {
        reveal(eval_comp);
        lemma_esb_dispatch_binary(n, tag);
    };
    //  Right tag
    assert(eval_comp(esb_entry(), n) == pair(left_node, right_node)) by {
        reveal(eval_comp);
        crate::compspec_free_var_helpers::lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
    };
    assert(eval_comp(esb_right_node(), n) == right_node) by {
        reveal(eval_comp); lemma_eval_snd(esb_entry(), n);
        lemma_unpair2_pair(left_node, right_node);
    };
    assert(eval_comp(esb_right_tag(), n) == unpair1(right_node)) by {
        reveal(eval_comp); lemma_eval_fst(esb_right_node(), n);
    };
    //  esb_binary_ok valid = tags_match
    let tm: nat = if unpair1(right_node) == tag { 1nat } else { 0nat };
    assert(eval_comp(esb_tags_match(), n) == tm) by {
        reveal(eval_comp);
        lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
    };
    //  Result valid
    assert(unpair2(eval_comp(esb_binary_ok(), n)) == tm) by {
        reveal(eval_comp);
        crate::compspec_free_var_helpers::lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_snd(cs_fst(br_acc()), n);
        lemma_unpair2_pair(entry_val, rest_val);
        //  Build the new_stack
        lemma_eval_snd(esb_left_node(), n);
        lemma_eval_snd(esb_right_node(), n);
        let lc = unpair2(left_node);
        let rc = unpair2(right_node);
        let el_cs = cs_pair(cs_fst(cs_snd(esb_left_node())), cs_fst(cs_snd(esb_right_node())));
        let er_cs = cs_pair(cs_snd(cs_snd(esb_left_node())), cs_snd(cs_snd(esb_right_node())));
        lemma_eval_fst(cs_snd(esb_left_node()), n);
        lemma_eval_fst(cs_snd(esb_right_node()), n);
        lemma_eval_snd(cs_snd(esb_left_node()), n);
        lemma_eval_snd(cs_snd(esb_right_node()), n);
        let el = pair(unpair1(lc), unpair1(rc));
        let er = pair(unpair2(lc), unpair2(rc));
        lemma_eval_pair(cs_fst(cs_snd(esb_left_node())), cs_fst(cs_snd(esb_right_node())), n);
        lemma_eval_pair(cs_snd(cs_snd(esb_left_node())), cs_snd(cs_snd(esb_right_node())), n);
        let el1 = CompSpec::Add { left: Box::new(el_cs), right: Box::new(cs_const(1)) };
        let er1 = CompSpec::Add { left: Box::new(er_cs), right: Box::new(cs_const(1)) };
        lemma_eval_add(el_cs, cs_const(1), n);
        lemma_eval_add(er_cs, cs_const(1), n);
        lemma_eval_pair(er1, esb_rest(), n);
        let new_stack = cs_pair(el1, cs_pair(er1, esb_rest()));
        lemma_eval_pair(el1, cs_pair(er1, esb_rest()), n);
        lemma_eval_pair(new_stack, esb_tags_match(), n);
        lemma_unpair2_pair(eval_comp(new_stack, n), tm);
    };
}

} // verus!
