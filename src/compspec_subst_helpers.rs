use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::*;
use crate::compspec_subst_induction::*;

verus! {

///  When phi_enc == 0: check_subst_comp returns 1 (0 iterations, base valid=1).
pub proof fn lemma_check_subst_comp_zero_fuel(result_enc: nat, var: nat)
    ensures
        eval_comp(check_subst_comp(), pair(0nat, pair(result_enc, var))) != 0,
{
    let input = pair(0nat, pair(result_enc, var));
    let phi = cs_fst(CompSpec::Id);
    let result = cs_fst(cs_snd(CompSpec::Id));

    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(0nat, pair(result_enc, var));
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(0nat, pair(result_enc, var));
    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_unpair1_pair(result_enc, var);
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_unpair2_pair(result_enc, var);

    lemma_eval_pair(phi, result, input);
    lemma_eval_add(cs_pair(phi, result), cs_const(1), input);
    lemma_eval_pair(
        CompSpec::Add { left: Box::new(cs_pair(phi, result)), right: Box::new(cs_const(1)) },
        cs_const(0), input);
    lemma_eval_pair(cs_const(0), cs_const(0), input);
    lemma_eval_pair(cs_const(1), cs_pair(cs_const(0), cs_const(0)), input);
    let stack_expr = cs_pair(
        CompSpec::Add { left: Box::new(cs_pair(phi, result)), right: Box::new(cs_const(1)) },
        cs_const(0));
    let valid_expr = cs_pair(cs_const(1), cs_pair(cs_const(0), cs_const(0)));
    lemma_eval_pair(stack_expr, valid_expr, input);
    let base_expr = cs_pair(stack_expr, valid_expr);

    lemma_eval_bounded_rec(phi, base_expr, check_subst_step(), input);

    let base_val = eval_comp(base_expr, input);
    let stack_val = eval_comp(stack_expr, input);
    let valid_part = pair(1nat, pair(0nat, 0nat));

    lemma_eval_comp(cs_fst(cs_snd(CompSpec::Id)),
        CompSpec::BoundedRec {
            count_fn: Box::new(phi),
            base: Box::new(base_expr),
            step: Box::new(check_subst_step()),
        }, input);

    lemma_eval_snd(CompSpec::Id, base_val);
    lemma_unpair2_pair(stack_val, valid_part);
    lemma_eval_fst(cs_snd(CompSpec::Id), base_val);
    lemma_unpair1_pair(1nat, pair(0nat, 0nat));
}

///  When valid > 0 and stack is empty, step returns acc unchanged.
pub proof fn lemma_subst_step_empty(
    i: nat, valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires valid > 0,
    ensures ({
        let acc = pair(0nat, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(check_subst_step(), input) == acc
    }),
{
    let stack = 0nat;
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));

    lemma_eval_br_acc(i, acc, orig);
    let valid_cs = cs_fst(cs_snd(br_acc()));
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
    lemma_eval_fst(cs_snd(br_acc()), input);
    lemma_unpair1_pair(valid, pair(t_enc, t_set));
    let stack_cs = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    let fst_stack = cs_fst(stack_cs);
    lemma_eval_fst(stack_cs, input);
    assert(pair(0nat, 0nat) == 0nat) by {
        assert(0nat * 1nat == 0nat) by(nonlinear_arith);
    }
    lemma_unpair1_pair(0nat, 0nat);
    lemma_eval_ifzero_then(fst_stack, br_acc(), check_subst_process_pair(), input);
    lemma_eval_ifzero_else(valid_cs, br_acc(),
        CompSpec::IfZero {
            cond: Box::new(fst_stack),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_subst_process_pair()),
        }, input);
}

///  compspec_iterate stays stable with empty stack and valid > 0.
pub proof fn lemma_subst_empty_stable(
    fuel: nat, valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires valid > 0,
    ensures ({
        let acc = pair(0nat, pair(valid, pair(t_enc, t_set)));
        let orig = pair(phi_enc, pair(result_enc, var));
        compspec_iterate(check_subst_step(), fuel, acc, orig) == acc
    }),
    decreases fuel,
{
    let acc = pair(0nat, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    if fuel > 0 {
        lemma_subst_step_empty((fuel - 1) as nat, valid, t_enc, t_set,
            phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, orig);
        lemma_subst_empty_stable((fuel - 1) as nat, valid, t_enc, t_set,
            phi_enc, result_enc, var);
    }
}

///  Unfold check_subst_comp to compspec_iterate.
proof fn lemma_check_subst_unfold(phi_enc: nat, result_enc: nat, var: nat)
    ensures ({
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base_val = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
        eval_comp(check_subst_comp(), input)
            == unpair1(unpair2(compspec_iterate(check_subst_step(), phi_enc, base_val, input)))
    }),
{
    let input = pair(phi_enc, pair(result_enc, var));
    let phi_cs = cs_fst(CompSpec::Id);
    let result_cs = cs_fst(cs_snd(CompSpec::Id));

    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(phi_enc, pair(result_enc, var));
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(phi_enc, pair(result_enc, var));
    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_unpair1_pair(result_enc, var);
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_unpair2_pair(result_enc, var);

    lemma_eval_pair(phi_cs, result_cs, input);
    lemma_eval_add(cs_pair(phi_cs, result_cs), cs_const(1), input);
    let entry_plus_1 = CompSpec::Add {
        left: Box::new(cs_pair(phi_cs, result_cs)), right: Box::new(cs_const(1)) };
    lemma_eval_pair(entry_plus_1, cs_const(0), input);
    lemma_eval_pair(cs_const(0), cs_const(0), input);
    lemma_eval_pair(cs_const(1), cs_pair(cs_const(0), cs_const(0)), input);
    let stack_expr = cs_pair(entry_plus_1, cs_const(0));
    let valid_expr = cs_pair(cs_const(1), cs_pair(cs_const(0), cs_const(0)));
    lemma_eval_pair(stack_expr, valid_expr, input);
    let base_expr = cs_pair(stack_expr, valid_expr);

    lemma_eval_bounded_rec(phi_cs, base_expr, check_subst_step(), input);

    let br_result = compspec_iterate(check_subst_step(), phi_enc,
        eval_comp(base_expr, input), input);
    lemma_eval_comp(cs_fst(cs_snd(CompSpec::Id)),
        CompSpec::BoundedRec {
            count_fn: Box::new(phi_cs),
            base: Box::new(base_expr),
            step: Box::new(check_subst_step()),
        }, input);
    lemma_eval_snd(CompSpec::Id, br_result);
    lemma_eval_fst(cs_snd(CompSpec::Id), br_result);
}

///  Backward: check_subst_comp returns nonzero for valid substitutions.
pub proof fn lemma_check_subst_comp_backward(phi: Formula, var: nat, t: Term)
    ensures
        eval_comp(check_subst_comp(),
            pair(encode(phi), pair(encode(subst(phi, var, t)), var))) != 0,
{
    let phi_enc = encode(phi);
    let result_enc = encode(subst(phi, var, t));
    if phi_enc == 0 {
        lemma_check_subst_comp_zero_fuel(result_enc, var);
    } else {
        //  Unfold to compspec_iterate
        lemma_check_subst_unfold(phi_enc, result_enc, var);
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base_val = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));

        //  Fuel adequacy: phi_enc >= subst_traversal_cost(phi, var)
        lemma_encode_ge_subst_cost(phi, var);

        //  Traversal: processes all nodes, leaves stack at 0, valid at 1
        lemma_subst_traversal(phi, var, t, 0nat, 0nat, 0nat, phi_enc, result_enc, phi_enc);

        //  After traversal: iterate result = iterate(phi_enc - cost, pair(0, pair(1, pair(0,0))), input)
        //  Empty-stack stability: remaining iterations preserve acc
        let remaining = (phi_enc - subst_traversal_cost(phi, var)) as nat;
        lemma_subst_empty_stable(remaining, 1nat, 0nat, 0nat, phi_enc, result_enc, var);

        //  Extract valid = 1
        let final_acc = pair(0nat, pair(1nat, pair(0nat, 0nat)));
        lemma_unpair2_pair(0nat, pair(1nat, pair(0nat, 0nat)));
        lemma_unpair1_pair(1nat, pair(0nat, 0nat));
    }
}

} //  verus!
