use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_subst_step_helpers::{lemma_subst_step_dispatch, lemma_subst_dispatch_compound};

verus! {

///  Forward step for Binary (phi_tag 3-6): evaluates one iterate step and extracts result.
///  Result: valid = cs_eq(phi_tag, result_tag), stack has both sub-pairs pushed.
///  Isolated in own file per rlimit tips.
#[verifier::rlimit(1200)]
pub proof fn lemma_forward_step_binary(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) >= 3nat,
        unpair1(phi_node) <= 6nat,
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        let tag_eq: nat = if unpair1(result_node) == unpair1(phi_node) { 1nat } else { 0nat };
        let phi_c = unpair2(phi_node);
        let result_c = unpair2(result_node);
        let entry_l = pair(unpair1(phi_c), unpair1(result_c));
        let entry_r = pair(unpair2(phi_c), unpair2(result_c));
        let new_stack = pair(entry_l + 1, pair(entry_r + 1, rest));
        eval_comp(check_subst_step(), input)
            == pair(new_stack, pair(tag_eq, pair(t_enc, t_set)))
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));
    let tag = unpair1(phi_node);

    //  Step → process_pair
    assert(eval_comp(check_subst_step(), input)
        == eval_comp(check_subst_process_pair(), input)) by {
        reveal(eval_comp);
        lemma_subst_step_dispatch(i, entry + 1, rest, valid, t_enc, t_set,
            phi_enc, result_enc, var);
    }

    //  process_pair → check_subst_compound (tag >= 3)
    assert(eval_comp(check_subst_process_pair(), input)
        == eval_comp(check_subst_compound(), input)) by {
        reveal(eval_comp);
        lemma_subst_dispatch_compound(i, phi_node, result_node, rest,
            valid, t_enc, t_set, phi_enc, result_enc, var);
    }

    //  Extract entry components
    assert(eval_comp(br_acc(), input) == acc) by {
        reveal(eval_comp); lemma_eval_br_acc(i, acc, orig);
    }
    assert(eval_comp(cs_fst(br_acc()), input) == stack) by {
        reveal(eval_comp);
        lemma_eval_fst(br_acc(), input);
        lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    }
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    assert(eval_comp(entry_cs, input) == entry) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(br_acc()), input);
        lemma_unpair1_pair(entry + 1, rest);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
        lemma_eval_pred(entry + 1);
    }
    assert(eval_comp(cs_snd(cs_fst(br_acc())), input) == rest) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_fst(br_acc()), input);
        lemma_unpair2_pair(entry + 1, rest);
    }
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node) by {
        reveal(eval_comp); lemma_eval_fst(entry_cs, input); lemma_unpair1_pair(phi_node, result_node);
    }
    assert(eval_comp(cs_snd(entry_cs), input) == result_node) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input); lemma_unpair2_pair(phi_node, result_node);
    }

    let phi_tag_cs = cs_fst(cs_fst(entry_cs));
    let result_tag_cs = cs_fst(cs_snd(entry_cs));
    let phi_content_cs = cs_snd(cs_fst(entry_cs));
    let result_content_cs = cs_snd(cs_snd(entry_cs));
    assert(eval_comp(phi_tag_cs, input) == tag) by {
        reveal(eval_comp); lemma_eval_fst(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_tag_cs, input) == unpair1(result_node)) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input);
        lemma_eval_fst(cs_snd(entry_cs), input);
    }
    assert(eval_comp(phi_content_cs, input) == unpair2(phi_node)) by {
        reveal(eval_comp); lemma_eval_snd(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_content_cs, input) == unpair2(result_node)) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input);
        lemma_eval_snd(cs_snd(entry_cs), input);
    }

    //  is_quant = cs_lt(6, tag) = 0 (tag <= 6)
    let is_quant = cs_lt(cs_const(6), phi_tag_cs);
    assert(eval_comp(is_quant, input) == 0nat) by {
        reveal(eval_comp); lemma_eval_lt(cs_const(6), phi_tag_cs, input);
    }

    //  cs_eq(phi_tag, result_tag)
    let tags_match = cs_eq(phi_tag_cs, result_tag_cs);
    assert(eval_comp(tags_match, input)
        == (if unpair1(result_node) == tag { 1nat } else { 0nat })) by {
        reveal(eval_comp); lemma_eval_eq(phi_tag_cs, result_tag_cs, input);
    }

    //  t_enc, t_set
    let t_enc_cs = cs_fst(cs_snd(cs_snd(br_acc())));
    let t_set_cs = cs_snd(cs_snd(cs_snd(br_acc())));
    assert(eval_comp(t_enc_cs, input) == t_enc && eval_comp(t_set_cs, input) == t_set) by {
        reveal(eval_comp);
        lemma_eval_snd(br_acc(), input);
        lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
        lemma_eval_snd(cs_snd(br_acc()), input);
        lemma_unpair2_pair(valid, pair(t_enc, t_set));
        lemma_eval_fst(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair1_pair(t_enc, t_set);
        lemma_eval_snd(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair2_pair(t_enc, t_set);
    }

    //  Content sub-parts
    let phi_c = unpair2(phi_node);
    let result_c = unpair2(result_node);
    assert(eval_comp(cs_fst(phi_content_cs), input) == unpair1(phi_c)) by {
        reveal(eval_comp); lemma_eval_fst(phi_content_cs, input);
    }
    assert(eval_comp(cs_fst(result_content_cs), input) == unpair1(result_c)) by {
        reveal(eval_comp); lemma_eval_fst(result_content_cs, input);
    }
    assert(eval_comp(cs_snd(phi_content_cs), input) == unpair2(phi_c)) by {
        reveal(eval_comp); lemma_eval_snd(phi_content_cs, input);
    }
    assert(eval_comp(cs_snd(result_content_cs), input) == unpair2(result_c)) by {
        reveal(eval_comp); lemma_eval_snd(result_content_cs, input);
    }

    //  Evaluate check_subst_compound: IfZero(is_quant=0) → then (binary)
    let rest_cs = cs_snd(cs_fst(br_acc()));
    assert(eval_comp(check_subst_compound(), input) == ({
        let entry_l = pair(unpair1(phi_c), unpair1(result_c));
        let entry_r = pair(unpair2(phi_c), unpair2(result_c));
        let new_stack = pair(entry_l + 1, pair(entry_r + 1, rest));
        let tag_eq: nat = if unpair1(result_node) == tag { 1nat } else { 0nat };
        pair(new_stack, pair(tag_eq, pair(t_enc, t_set)))
    })) by {
        reveal(eval_comp);
        let lp_cs = cs_pair(cs_fst(phi_content_cs), cs_fst(result_content_cs));
        let rp_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));
        lemma_eval_pair(cs_fst(phi_content_cs), cs_fst(result_content_cs), input);
        lemma_eval_add(lp_cs, cs_const(1), input);
        lemma_eval_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs), input);
        lemma_eval_add(rp_cs, cs_const(1), input);
        let lp1 = CompSpec::Add { left: Box::new(lp_cs), right: Box::new(cs_const(1)) };
        let rp1 = CompSpec::Add { left: Box::new(rp_cs), right: Box::new(cs_const(1)) };
        lemma_eval_pair(rp1, rest_cs, input);
        lemma_eval_pair(lp1, cs_pair(rp1, rest_cs), input);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_pair(tags_match, cs_pair(t_enc_cs, t_set_cs), input);
        let new_stack_cs = cs_pair(lp1, cs_pair(rp1, rest_cs));
        let valid_pair_cs = cs_pair(tags_match, cs_pair(t_enc_cs, t_set_cs));
        lemma_eval_pair(new_stack_cs, valid_pair_cs, input);
        let then_br = cs_pair(new_stack_cs, valid_pair_cs);

        //  Build else_br reference for IfZero
        let bound_var_cs = cs_fst(phi_content_cs);
        let var_cs = cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))));
        let bound_eq_var = cs_eq(bound_var_cs, var_cs);
        let result_bound_cs = cs_fst(result_content_cs);
        let sub_pair_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));
        let sp1 = CompSpec::Add { left: Box::new(sub_pair_cs), right: Box::new(cs_const(1)) };
        let quant_free = cs_pair(
            cs_pair(sp1, rest_cs),
            cs_pair(cs_and(tags_match, cs_eq(bound_var_cs, result_bound_cs)),
                cs_pair(t_enc_cs, t_set_cs)));
        let quant_bound = cs_pair(
            rest_cs,
            cs_pair(cs_and(tags_match, cs_eq(cs_fst(entry_cs), cs_snd(entry_cs))),
                cs_pair(t_enc_cs, t_set_cs)));
        let quant_br = CompSpec::IfZero {
            cond: Box::new(bound_eq_var),
            then_br: Box::new(quant_free),
            else_br: Box::new(quant_bound),
        };
        lemma_eval_ifzero_then(is_quant, then_br, quant_br, input);
    }
}

} // verus!
