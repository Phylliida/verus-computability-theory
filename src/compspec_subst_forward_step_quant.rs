use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_subst_step_helpers::{lemma_subst_step_dispatch, lemma_subst_dispatch_compound};

verus! {

///  Forward step for Quantifier (tags 7-8): evaluates one iterate step.
///  Handles both bound (v==var) and free (v!=var) cases.
///  Result depends on whether bound var matches substitution var.
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_step_quant(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) >= 7nat,
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        let tag_eq: nat = if unpair1(result_node) == unpair1(phi_node) { 1nat } else { 0nat };
        let bound_var = unpair1(unpair2(phi_node));
        if bound_var == var {
            //  Bound case: valid = cs_and(tag_eq, cs_eq(phi_node, result_node))
            let node_eq: nat = if phi_node == result_node { 1nat } else { 0nat };
            eval_comp(check_subst_step(), input)
                == pair(rest, pair(tag_eq * node_eq, pair(t_enc, t_set)))
        } else {
            //  Free case: valid = cs_and(tag_eq, cs_eq(bound_var, bound_var_result))
            let bound_result = unpair1(unpair2(result_node));
            let bound_eq: nat = if bound_var == bound_result { 1nat } else { 0nat };
            let sub_entry = pair(unpair2(unpair2(phi_node)), unpair2(unpair2(result_node)));
            eval_comp(check_subst_step(), input)
                == pair(pair(sub_entry + 1, rest), pair(tag_eq * bound_eq, pair(t_enc, t_set)))
        }
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

    //  process_pair → compound (tag >= 7 >= 3)
    assert(eval_comp(check_subst_process_pair(), input)
        == eval_comp(check_subst_compound(), input)) by {
        reveal(eval_comp);
        lemma_subst_dispatch_compound(i, phi_node, result_node, rest,
            valid, t_enc, t_set, phi_enc, result_enc, var);
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
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node &&
           eval_comp(cs_snd(entry_cs), input) == result_node) by {
        reveal(eval_comp);
        lemma_eval_fst(entry_cs, input);
        lemma_unpair1_pair(phi_node, result_node);
        lemma_eval_snd(entry_cs, input);
        lemma_unpair2_pair(phi_node, result_node);
    }

    //  Tags, content
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

    //  is_quant != 0 (tag >= 7)
    let is_quant = cs_lt(cs_const(6), phi_tag_cs);
    assert(eval_comp(is_quant, input) != 0nat) by {
        reveal(eval_comp); lemma_eval_lt(cs_const(6), phi_tag_cs, input);
    }

    //  tags_match
    let tags_match = cs_eq(phi_tag_cs, result_tag_cs);
    assert(eval_comp(tags_match, input) == (if unpair1(result_node) == tag { 1nat } else { 0nat })) by {
        reveal(eval_comp); lemma_eval_eq(phi_tag_cs, result_tag_cs, input);
    }

    //  bound_var and var
    let bound_var_cs = cs_fst(phi_content_cs);
    let var_cs = cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))));
    assert(eval_comp(bound_var_cs, input) == unpair1(unpair2(phi_node))) by {
        reveal(eval_comp); lemma_eval_fst(phi_content_cs, input);
    }
    assert(eval_comp(var_cs, input) == var) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), input);
        lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
        lemma_eval_snd(cs_snd(CompSpec::Id), input);
        lemma_eval_snd(CompSpec::Id, input);
        lemma_unpair2_pair(i, pair(acc, orig));
        lemma_unpair2_pair(acc, orig);
        lemma_unpair2_pair(phi_enc, pair(result_enc, var));
        lemma_unpair2_pair(result_enc, var);
    }
    let bound_eq_var = cs_eq(bound_var_cs, var_cs);
    assert(eval_comp(bound_eq_var, input) ==
        (if unpair1(unpair2(phi_node)) == var { 1nat } else { 0nat })) by {
        reveal(eval_comp); lemma_eval_eq(bound_var_cs, var_cs, input);
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

    let rest_cs = cs_snd(cs_fst(br_acc()));
    let bound_var = unpair1(unpair2(phi_node));

    //  Evaluate check_subst_compound based on bound_var vs var
    assert(eval_comp(check_subst_compound(), input) == ({
        let tag_eq: nat = if unpair1(result_node) == tag { 1nat } else { 0nat };
        if bound_var == var {
            let node_eq: nat = if phi_node == result_node { 1nat } else { 0nat };
            pair(rest, pair(tag_eq * node_eq, pair(t_enc, t_set)))
        } else {
            let bound_result = unpair1(unpair2(result_node));
            let bound_eq: nat = if bound_var == bound_result { 1nat } else { 0nat };
            let sub_entry = pair(unpair2(unpair2(phi_node)), unpair2(unpair2(result_node)));
            pair(pair(sub_entry + 1, rest), pair(tag_eq * bound_eq, pair(t_enc, t_set)))
        }
    })) by {
        reveal(eval_comp);
        let result_bound_cs = cs_fst(result_content_cs);
        assert(eval_comp(result_bound_cs, input) == unpair1(unpair2(result_node))) by {
            lemma_eval_fst(result_content_cs, input);
        }

        //  Build branch expressions
        let lp_cs = cs_pair(cs_fst(phi_content_cs), cs_fst(result_content_cs));
        let rp_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));
        let lp1 = CompSpec::Add { left: Box::new(lp_cs), right: Box::new(cs_const(1)) };
        let rp1 = CompSpec::Add { left: Box::new(rp_cs), right: Box::new(cs_const(1)) };
        let binary_then = cs_pair(
            cs_pair(lp1, cs_pair(rp1, rest_cs)),
            cs_pair(tags_match, cs_pair(t_enc_cs, t_set_cs)));

        let sub_pair_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));
        let sp1 = CompSpec::Add { left: Box::new(sub_pair_cs), right: Box::new(cs_const(1)) };

        if bound_var == var {
            //  IfZero(bound_eq_var=1) → else (exact match)
            let node_eq_cs = cs_eq(cs_fst(entry_cs), cs_snd(entry_cs));
            assert(eval_comp(node_eq_cs, input) == (if phi_node == result_node { 1nat } else { 0nat })) by {
                lemma_eval_eq(cs_fst(entry_cs), cs_snd(entry_cs), input);
            }
            lemma_eval_cs_and(tags_match, node_eq_cs, input);
            lemma_eval_pair(t_enc_cs, t_set_cs, input);
            lemma_eval_pair(cs_and(tags_match, node_eq_cs), cs_pair(t_enc_cs, t_set_cs), input);
            lemma_eval_pair(rest_cs, cs_pair(cs_and(tags_match, node_eq_cs), cs_pair(t_enc_cs, t_set_cs)), input);
            let else_br = cs_pair(rest_cs,
                cs_pair(cs_and(tags_match, node_eq_cs), cs_pair(t_enc_cs, t_set_cs)));
            let then_br = cs_pair(
                cs_pair(sp1, rest_cs),
                cs_pair(cs_and(tags_match, cs_eq(bound_var_cs, result_bound_cs)),
                    cs_pair(t_enc_cs, t_set_cs)));
            lemma_eval_ifzero_else(bound_eq_var, then_br, else_br, input);
            lemma_eval_ifzero_else(is_quant, binary_then,
                CompSpec::IfZero {
                    cond: Box::new(bound_eq_var),
                    then_br: Box::new(then_br),
                    else_br: Box::new(else_br),
                }, input);
        } else {
            //  IfZero(bound_eq_var=0) → then (push sub)
            let bound_match_cs = cs_eq(bound_var_cs, result_bound_cs);
            assert(eval_comp(bound_match_cs, input) ==
                (if bound_var == unpair1(unpair2(result_node)) { 1nat } else { 0nat })) by {
                lemma_eval_eq(bound_var_cs, result_bound_cs, input);
            }
            lemma_eval_cs_and(tags_match, bound_match_cs, input);
            lemma_eval_snd(phi_content_cs, input);
            lemma_eval_snd(result_content_cs, input);
            lemma_eval_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs), input);
            lemma_eval_add(sub_pair_cs, cs_const(1), input);
            lemma_eval_pair(sp1, rest_cs, input);
            lemma_eval_pair(t_enc_cs, t_set_cs, input);
            lemma_eval_pair(cs_and(tags_match, bound_match_cs), cs_pair(t_enc_cs, t_set_cs), input);
            lemma_eval_pair(cs_pair(sp1, rest_cs),
                cs_pair(cs_and(tags_match, bound_match_cs), cs_pair(t_enc_cs, t_set_cs)), input);
            let then_br = cs_pair(
                cs_pair(sp1, rest_cs),
                cs_pair(cs_and(tags_match, bound_match_cs), cs_pair(t_enc_cs, t_set_cs)));
            let node_eq_cs = cs_eq(cs_fst(entry_cs), cs_snd(entry_cs));
            let else_br = cs_pair(rest_cs,
                cs_pair(cs_and(tags_match, node_eq_cs), cs_pair(t_enc_cs, t_set_cs)));
            lemma_eval_ifzero_then(bound_eq_var, then_br, else_br, input);
            lemma_eval_ifzero_else(is_quant, binary_then,
                CompSpec::IfZero {
                    cond: Box::new(bound_eq_var),
                    then_br: Box::new(then_br),
                    else_br: Box::new(else_br),
                }, input);
        }
    }
}

} // verus!
