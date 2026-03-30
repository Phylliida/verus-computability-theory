use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::*;

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

//  ============================================================
//  Stability lemmas for check_subst_step
//  ============================================================

///  When valid == 0, check_subst_step returns acc unchanged.
proof fn lemma_subst_step_invalid(
    i: nat, stack: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    ensures ({
        let acc = pair(stack, pair(0nat, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(check_subst_step(), input) == acc
    }),
{
    let acc = pair(stack, pair(0nat, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));

    lemma_eval_br_acc(i, acc, orig);
    let valid_cs = cs_fst(cs_snd(br_acc()));
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(stack, pair(0nat, pair(t_enc, t_set)));
    lemma_eval_fst(cs_snd(br_acc()), input);
    lemma_unpair1_pair(0nat, pair(t_enc, t_set));
    //  valid == 0 → IfZero takes then branch → returns acc
    lemma_eval_ifzero_then(valid_cs,
        br_acc(),
        CompSpec::IfZero {
            cond: Box::new(cs_fst(cs_fst(br_acc()))),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_subst_process_pair()),
        },
        input);
}

///  When valid > 0 and stack is empty (fst(stack)==0), step returns acc unchanged.
pub proof fn lemma_subst_step_empty(
    i: nat, valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires valid > 0, unpair1(0nat) == 0,
    ensures ({
        let stack = 0nat;
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
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
    //  valid > 0 → IfZero else branch → inner IfZero on fst(stack)
    let stack_cs = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    let fst_stack = cs_fst(stack_cs);
    lemma_eval_fst(stack_cs, input);
    //  stack == 0, fst(0) should be 0
    assert(pair(0nat, 0nat) == 0nat) by {
        assert(0nat * 1nat == 0nat) by(nonlinear_arith);
    }
    lemma_unpair1_pair(0nat, 0nat);
    //  fst(stack) == 0 → inner IfZero then branch → returns acc
    lemma_eval_ifzero_then(fst_stack,
        br_acc(),
        check_subst_process_pair(),
        input);
    lemma_eval_ifzero_else(valid_cs,
        br_acc(),
        CompSpec::IfZero {
            cond: Box::new(fst_stack),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_subst_process_pair()),
        },
        input);
}

///  compspec_iterate with check_subst_step stays stable when valid>0 and stack empty.
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
        assert(pair(0nat, 0nat) == 0nat) by {
            assert(0nat * 1nat == 0nat) by(nonlinear_arith);
        }
        lemma_unpair1_pair(0nat, 0nat);
        lemma_subst_step_empty((fuel - 1) as nat, valid, t_enc, t_set,
            phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, orig);
        lemma_subst_empty_stable((fuel - 1) as nat, valid, t_enc, t_set,
            phi_enc, result_enc, var);
    }
}

///  Unfold check_subst_comp to compspec_iterate.
///  Shows: eval_comp(check_subst_comp(), input) ==
///    unpair1(unpair2(compspec_iterate(check_subst_step(), phi_enc, base_val, input)))
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

    //  Evaluate base expression
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

    //  BoundedRec unfolds to compspec_iterate
    lemma_eval_bounded_rec(phi_cs, base_expr, check_subst_step(), input);

    //  Extract valid: cs_fst(cs_snd(Id)) applied to the BoundedRec result
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
///  Input: pair(encode(phi), pair(encode(subst(phi, var, t)), var))
///
///  Proof strategy:
///  1. phi_enc == 0: zero-fuel gives valid=1
///  2. phi_enc > 0: unfold to compspec_iterate, show valid stays 1
///     via structural induction and step evaluation lemmas
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

        //  Need: unpair1(unpair2(compspec_iterate(step, phi_enc, base_val, input))) != 0
        //
        //  The BoundedRec processes the (phi_enc, result_enc) tree in parallel.
        //  Since subst preserves tags at every level, every cs_eq tag check
        //  returns 1, and valid stays 1 throughout.
        //
        //  After formula_size(phi) steps, the stack is empty.
        //  Remaining fuel (phi_enc - formula_size(phi)) iterations preserve the acc.
        //
        //  Full proof requires:
        //  - Per-variant step evaluation lemmas (one per Formula constructor)
        //  - Structural induction showing each step processes correctly
        //  - Fuel adequacy: phi_enc >= formula_size(phi) when phi_enc > 0
        //  - Empty-stack stability (already proved: lemma_subst_empty_stable)
        //
        //  This follows the same pattern as compspec_free_var_induction.rs
        //  but for check_subst_step instead of has_free_var_step.
        //
        //  TODO: Write per-variant step evaluation helpers in a separate file
        //  (compspec_subst_step_helpers.rs) to avoid trigger pollution.
        //  Then structural induction in compspec_subst_induction.rs.
        lemma_check_subst_comp_zero_fuel(result_enc, var);
        //  ^^^ PLACEHOLDER — does not prove the phi_enc > 0 case
    }
}

} //  verus!
