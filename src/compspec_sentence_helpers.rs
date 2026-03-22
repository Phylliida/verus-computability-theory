use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

/// Show one step of check_is_sentence_step preserves acc when has_free_var returns 0.
/// Isolated in its own file to reduce trigger pollution from compspec_halts proof fn bodies.
pub proof fn lemma_cis_step_preserves(i: nat, acc: nat, f_enc: nat)
    requires
        eval_comp(has_free_var_comp(), pair(f_enc, i)) == 0,
    ensures
        eval_comp(check_is_sentence_step(), pair(i, pair(acc, f_enc))) == acc,
{
    let input = pair(i, pair(acc, f_enc));

    // Unpack pairs (needed for eval_comp of sub-expressions)
    lemma_unpair1_pair(i, pair(acc, f_enc));
    lemma_unpair2_pair(i, pair(acc, f_enc));
    lemma_unpair1_pair(acc, f_enc);
    lemma_unpair2_pair(acc, f_enc);

    // Build the step manually (same as check_is_sentence_step but without reveal)
    let acc_expr = cs_fst(cs_snd(CompSpec::Id));
    let f_enc_expr = cs_snd(cs_snd(CompSpec::Id));
    let i_expr = cs_fst(CompSpec::Id);
    let pair_expr = CompSpec::CantorPair {
        left: Box::new(f_enc_expr),
        right: Box::new(i_expr),
    };
    let hfv = has_free_var_comp();
    let check = cs_comp(hfv, pair_expr);
    let not_check = cs_not(check);
    let step = cs_and(acc_expr, not_check);

    // Evaluate sub-expressions one at a time using rewriting lemmas
    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);

    // check = Comp(hfv, pair_expr), eval = eval(hfv, eval(pair_expr, input))
    lemma_eval_comp(hfv, pair_expr, input);

    // cs_and = Mul, eval = eval(acc_expr) * eval(not_check)
    lemma_eval_cs_and(acc_expr, not_check, input);

    // Connect to check_is_sentence_step (isolated reveal)
    assert(step == check_is_sentence_step()) by {
        reveal(check_is_sentence_step);
    };
}

} // verus!
