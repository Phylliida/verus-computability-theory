use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;

verus! {

///  Forward step for Not (phi_tag=2): evaluates one iterate step and extracts valid field.
///  Result: valid = cs_eq(phi_tag, result_tag), rest of output structure.
///  Isolated in own file per rlimit tips.
#[verifier::rlimit(1200)]
pub proof fn lemma_forward_step_not(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) == 2nat,
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        let tag_eq: nat = if unpair1(result_node) == 2nat { 1nat } else { 0nat };
        let sub_entry = pair(unpair2(phi_node), unpair2(result_node));
        eval_comp(check_subst_step(), input)
            == pair(pair(sub_entry + 1, rest), pair(tag_eq, pair(t_enc, t_set)))
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));

    //  Step → process_pair
    assert(eval_comp(check_subst_step(), input)
        == eval_comp(check_subst_process_pair(), input)) by {
        reveal(eval_comp);
        lemma_subst_step_dispatch(i, entry + 1, rest, valid, t_enc, t_set,
            phi_enc, result_enc, var);
    }

    //  Extract components
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
    assert(eval_comp(phi_tag_cs, input) == 2nat) by {
        reveal(eval_comp); lemma_eval_fst(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_tag_cs, input) == unpair1(result_node)) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_eval_fst(cs_snd(entry_cs), input);
    }

    //  Dispatch process_pair: tag 2 → else → else → then → check_subst_unary
    assert(eval_comp(check_subst_process_pair(), input)
        == eval_comp(check_subst_unary(), input)) by {
        reveal(eval_comp);
        lemma_eval_comp(CompSpec::Pred, phi_tag_cs, input);
        lemma_eval_pred(2nat);
        let pred_tag = cs_comp(CompSpec::Pred, phi_tag_cs);
        lemma_eval_comp(CompSpec::Pred, pred_tag, input);
        lemma_eval_pred(1nat);
        let pred_pred_tag = cs_comp(CompSpec::Pred, pred_tag);
        lemma_eval_ifzero_then(pred_pred_tag,
            check_subst_unary(), check_subst_compound(), input);
        lemma_eval_ifzero_else(pred_tag,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(pred_pred_tag),
                then_br: Box::new(check_subst_unary()),
                else_br: Box::new(check_subst_compound()),
            }, input);
        lemma_eval_ifzero_else(phi_tag_cs,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(pred_tag),
                then_br: Box::new(check_subst_atomic_terms()),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(pred_pred_tag),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }),
            }, input);
    }

    //  cs_eq(phi_tag, result_tag)
    let tag_eq_cs = cs_eq(phi_tag_cs, result_tag_cs);
    assert(eval_comp(tag_eq_cs, input) == (if unpair1(result_node) == 2nat { 1nat } else { 0nat })) by {
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

    //  Evaluate check_subst_unary output
    let rest_cs = cs_snd(cs_fst(br_acc()));
    let phi_sub_cs = cs_snd(cs_fst(entry_cs));
    let result_sub_cs = cs_snd(cs_snd(entry_cs));
    assert(eval_comp(phi_sub_cs, input) == unpair2(phi_node)) by {
        reveal(eval_comp); lemma_eval_snd(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_sub_cs, input) == unpair2(result_node)) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input);
        lemma_eval_snd(cs_snd(entry_cs), input);
    }

    assert(eval_comp(check_subst_unary(), input) == ({
        let sub_entry = pair(unpair2(phi_node), unpair2(result_node));
        let tag_eq: nat = if unpair1(result_node) == 2nat { 1nat } else { 0nat };
        pair(pair(sub_entry + 1, rest), pair(tag_eq, pair(t_enc, t_set)))
    })) by {
        reveal(eval_comp);
        let new_entry_cs = cs_pair(phi_sub_cs, result_sub_cs);
        lemma_eval_pair(phi_sub_cs, result_sub_cs, input);
        lemma_eval_add(new_entry_cs, cs_const(1), input);
        let ne_plus_1 = CompSpec::Add { left: Box::new(new_entry_cs), right: Box::new(cs_const(1)) };
        lemma_eval_pair(ne_plus_1, rest_cs, input);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_pair(tag_eq_cs, cs_pair(t_enc_cs, t_set_cs), input);
        lemma_eval_pair(cs_pair(ne_plus_1, rest_cs),
            cs_pair(tag_eq_cs, cs_pair(t_enc_cs, t_set_cs)), input);
    }
}

} // verus!
