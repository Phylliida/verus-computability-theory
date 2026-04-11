use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;

verus! {

///  Step with valid=0 returns acc unchanged.
pub proof fn lemma_esb_step_valid_zero(counter: nat, stack: nat, s: nat)
    ensures
        eval_comp(check_eq_subst_step(), pair(counter, pair(pair(stack, 0nat), s)))
            == pair(stack, 0nat),
{
    let acc = pair(stack, 0nat);
    let n = pair(counter, pair(acc, s));
    lemma_eval_br_acc(counter, acc, s);
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
pub proof fn lemma_esb_valid_zero_stable(fuel: nat, stack: nat, s: nat)
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

///  Forward walk dispatcher: delegates to per-variant helpers.
#[verifier::rlimit(5000)]
pub proof fn lemma_eq_subst_forward_walk(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, valid: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        valid != 0,
        fuel >= formula_size(f1),
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(encode(f1), encode(f2)) + 1, rest), valid),
                pair(pe, pair(re, pair(x_enc, y_enc))))
        ) != 0,
    ensures
        eq_subst_compatible(f1, f2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1, 2nat,
{
    let tag = formula_tag(f1);
    if tag <= 1 {
        crate::compspec_eq_subst_forward_walk_atomic::lemma_eq_subst_forward_walk_atomic(
            f1, f2, x_enc, y_enc, rest, valid, pe, re, fuel);
    } else if tag == 2 {
        crate::compspec_eq_subst_forward_walk_unary::lemma_eq_subst_forward_walk_unary(
            f1, f2, x_enc, y_enc, rest, valid, pe, re, fuel);
    } else if tag <= 6 {
        crate::compspec_eq_subst_forward_walk_binary::lemma_eq_subst_forward_walk_binary(
            f1, f2, x_enc, y_enc, rest, valid, pe, re, fuel);
    } else {
        crate::compspec_eq_subst_forward_walk_quant::lemma_eq_subst_forward_walk_quant(
            f1, f2, x_enc, y_enc, rest, valid, pe, re, fuel);
    }
}

} // verus!
