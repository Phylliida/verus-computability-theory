use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_helpers::*;

verus! {

///  Input independence: the step result doesn't depend on pe/re, only on acc and var.
///  Proof: both calls to the step helper give the same explicit expression.
///  This is a KEY lemma that enables relating outer iterates to inner check_subst_comp calls.
///
///  Strategy: case-split on valid and stack. When valid=0 or stack=0, step returns acc (trivially independent).
///  When valid>0 and stack nonempty, we use the fact that check_subst_step only accesses acc and var.
///
///  NOTE: We prove this via Z3's ability to match the CompSpec evaluation.
///  The step function check_subst_step only uses:
///  - br_acc() = cs_fst(cs_snd(Id)) — accessing acc
///  - cs_snd^4(Id) — accessing var
///  Both are the same for inputs with the same (i, acc, var).
#[verifier::rlimit(3000)]
pub proof fn lemma_step_input_independent(
    i: nat, acc: nat, pe1: nat, re1: nat, pe2: nat, re2: nat, var: nat,
)
    ensures
        eval_comp(check_subst_step(),
            pair(i, pair(acc, pair(pe1, pair(re1, var)))))
        == eval_comp(check_subst_step(),
            pair(i, pair(acc, pair(pe2, pair(re2, var))))),
{
    let input1 = pair(i, pair(acc, pair(pe1, pair(re1, var))));
    let input2 = pair(i, pair(acc, pair(pe2, pair(re2, var))));

    //  Both inputs decode to the same acc
    lemma_eval_br_acc_general(i, acc, pe1, re1, var);
    lemma_eval_br_acc_general(i, acc, pe2, re2, var);

    //  Both decode to the same var
    lemma_eval_var_general(i, acc, pe1, re1, var);
    lemma_eval_var_general(i, acc, pe2, re2, var);
}

///  Helper: br_acc evaluates to acc for any (pe, re).
proof fn lemma_eval_br_acc_general(i: nat, acc: nat, pe: nat, re: nat, var: nat)
    ensures
        eval_comp(br_acc(), pair(i, pair(acc, pair(pe, pair(re, var))))) == acc,
{
    let input = pair(i, pair(acc, pair(pe, pair(re, var))));
    let orig = pair(pe, pair(re, var));
    crate::compspec_free_var_helpers::lemma_eval_br_acc(i, acc, orig);
}

///  Helper: var extraction evaluates to var for any (pe, re).
proof fn lemma_eval_var_general(i: nat, acc: nat, pe: nat, re: nat, var: nat)
    ensures
        eval_comp(cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))),
            pair(i, pair(acc, pair(pe, pair(re, var))))) == var,
{
    let input = pair(i, pair(acc, pair(pe, pair(re, var))));
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), input);
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, pair(pe, pair(re, var))));
    lemma_unpair2_pair(acc, pair(pe, pair(re, var)));
    lemma_unpair2_pair(pe, pair(re, var));
    lemma_unpair2_pair(re, var);
}

///  Iterate input independence: follows from step independence by induction.
pub proof fn lemma_iterate_input_independent(
    fuel: nat, acc: nat, pe1: nat, re1: nat, pe2: nat, re2: nat, var: nat,
)
    ensures
        compspec_iterate(check_subst_step(), fuel, acc, pair(pe1, pair(re1, var)))
        == compspec_iterate(check_subst_step(), fuel, acc, pair(pe2, pair(re2, var))),
    decreases fuel,
{
    if fuel > 0 {
        let input1 = pair(pe1, pair(re1, var));
        let input2 = pair(pe2, pair(re2, var));
        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, input1);
        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, input2);
        lemma_step_input_independent((fuel - 1) as nat, acc, pe1, re1, pe2, re2, var);
        let next_acc = eval_comp(check_subst_step(),
            pair((fuel - 1) as nat, pair(acc, input1)));
        lemma_iterate_input_independent((fuel - 1) as nat, next_acc, pe1, re1, pe2, re2, var);
    }
}

} // verus!
