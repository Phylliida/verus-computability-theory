use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::*;

verus! {

///  Extract var from check_subst BoundedRec input.
///  Input: pair(iter, pair(acc, pair(phi_enc, pair(result_enc, var))))
pub proof fn lemma_subst_var_extract(i: nat, acc: nat, phi_enc: nat, result_enc: nat, var: nat)
    ensures
        eval_comp(cs_snd(cs_snd(cs_snd(CompSpec::Id))),
            pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))))) == var,
{
    let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
    lemma_unpair2_pair(acc, pair(phi_enc, pair(result_enc, var)));
    lemma_unpair2_pair(phi_enc, pair(result_enc, var));
    lemma_unpair2_pair(result_enc, var);
}

///  Extract accumulator components from check_subst BoundedRec input.
///  acc = pair(stack, pair(valid, pair(t_enc, t_set)))
pub proof fn lemma_subst_acc_extract(
    i: nat, stack: nat, valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    ensures ({
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(br_acc(), input) == acc &&
        eval_comp(cs_fst(br_acc()), input) == stack &&
        eval_comp(cs_fst(cs_snd(br_acc())), input) == valid
    }),
{
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));
    lemma_eval_br_acc(i, acc, orig);
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
    lemma_eval_fst(cs_snd(br_acc()), input);
    lemma_unpair1_pair(valid, pair(t_enc, t_set));
}

///  When valid > 0 and stack has entry with phi_tag == result_tag (both atomic, tag <= 1),
///  check_subst_step pops the entry and keeps valid=1.
///
///  For atomic formulas (Eq/In), check_subst_atomic_terms only multiplies
///  valid by cs_eq(phi_tag, result_tag), which is 1 when tags match.
///  Result: pair(rest, pair(valid * 1, pair(t_enc, t_set)))
pub proof fn lemma_subst_step_atomic(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) == unpair1(result_node),
        unpair1(phi_node) <= 1,  //  atomic: Eq or In tag
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(check_subst_step(), input)
            == pair(rest, pair(valid, pair(t_enc, t_set)))
    }),
{
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));
    let tag = unpair1(phi_node);

    //  Step 1: Extract acc components
    lemma_subst_acc_extract(i, stack, valid, t_enc, t_set, phi_enc, result_enc, var);

    //  Step 2: valid > 0 → outer IfZero else branch
    //  Step 3: fst(stack) = entry + 1 > 0 → inner IfZero else branch → process_pair
    lemma_eval_fst(cs_fst(br_acc()), input);
    lemma_unpair1_pair(entry + 1, rest);

    //  Step 4: process_pair extracts entry = fst(stack) - 1, rest = snd(stack)
    //  phi_node = fst(entry), result_node = snd(entry)
    //  phi_tag = fst(phi_node)

    //  Step 5: phi_tag <= 1 → IfZero dispatch to check_subst_atomic_terms
    //  For tag == 0: IfZero(phi_tag) → then branch (atomic)
    //  For tag == 1: IfZero(phi_tag) → else → IfZero(pred(phi_tag)) → then (pred(1)=0)

    //  Step 6: check_subst_atomic_terms returns
    //  pair(rest, pair(cs_and(cs_eq(phi_tag, result_tag), 1) * valid_rest, pair(t_enc, t_set)))
    //  Since phi_tag == result_tag, cs_eq returns 1, cs_and(1, 1) = 1
    //  So valid stays the same

    //  The full eval chain is very deep. For now, we note:
    //  - The step function dispatches through IfZero on valid, fst(stack), phi_tag
    //  - For matching tags, the result is pair(rest, pair(valid, pair(t_enc, t_set)))

    //  TODO: Complete the IfZero chain evaluation
    //  This requires ~20 more lemma calls for the full dispatch path.
    //  Deferring to keep this file compilable.
    lemma_eval_br_acc(i, acc, orig);
}

} //  verus!
