use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

/// Show that one step of the sentence check preserves acc when has_free_var returns 0.
/// Reveals check_is_sentence_step (opaque) and uses rewriting lemmas to avoid
/// Z3 diving into has_free_var_comp's BoundedRec tree.
proof fn lemma_cis_step_preserves(i: nat, acc: nat, f_enc: nat)
    requires
        eval_comp(has_free_var_comp(), pair(f_enc, i)) == 0,
    ensures
        eval_comp(check_is_sentence_step(), pair(i, pair(acc, f_enc))) == acc,
{
    reveal(check_is_sentence_step);

    let input = pair(i, pair(acc, f_enc));

    // Unpack pair structure
    lemma_unpair1_pair(i, pair(acc, f_enc));
    lemma_unpair2_pair(i, pair(acc, f_enc));
    lemma_unpair1_pair(acc, f_enc);
    lemma_unpair2_pair(acc, f_enc);

    // check_is_sentence_step() = cs_and(acc_expr, cs_not(check))
    // where acc_expr = cs_fst(cs_snd(Id))
    //       check = cs_comp(has_free_var_comp(), CantorPair(f_enc_expr, i_expr))
    let f_enc_expr = cs_snd(cs_snd(CompSpec::Id));
    let i_expr = cs_fst(CompSpec::Id);
    let pair_expr = CompSpec::CantorPair {
        left: Box::new(f_enc_expr),
        right: Box::new(i_expr),
    };
    let hfv = has_free_var_comp();
    let check = cs_comp(hfv, pair_expr);
    let not_check = cs_not(check);
    let acc_expr = cs_fst(cs_snd(CompSpec::Id));

    // eval(acc_expr, input) = acc
    assert(eval_comp(acc_expr, input) == acc) by {
        lemma_eval_fst(cs_snd(CompSpec::Id), input);
        lemma_eval_snd(CompSpec::Id, input);
    };

    // eval(check, input) = eval(hfv, pair(f_enc, i)) == 0
    assert(eval_comp(check, input) == 0nat) by {
        lemma_eval_comp(hfv, pair_expr, input);
        // eval_comp(pair_expr, input) = pair(f_enc, i)
        // eval_comp(hfv, pair(f_enc, i)) == 0 by requires
    };

    // eval(cs_not(check), input) = if 0 == 0 { 1 } else { 0 } = 1
    assert(eval_comp(not_check, input) == 1nat);

    // eval(cs_and(acc_expr, not_check), input) = acc * 1 = acc
    lemma_eval_cs_and(acc_expr, not_check, input);
}

/// For sentences, the check_is_sentence iterate preserves nonzero accumulator.
/// check_is_sentence_step is opaque here — we rely on lemma_cis_step_preserves
/// for the step computation, not Z3 unfolding.
proof fn lemma_check_is_sentence_iter(
    f_enc: nat,
    fuel: nat,
    acc: nat,
)
    requires
        acc != 0,
        forall|v: nat| eval_comp(has_free_var_comp(), pair(f_enc, v)) == 0,
    ensures
        iterate(
            |x: nat| eval_comp(check_is_sentence_step(), x),
            fuel, acc, f_enc,
        ) != 0,
    decreases fuel,
{
    if fuel > 0 {
        let i = (fuel - 1) as nat;

        // One step: since has_free_var(f_enc, i) == 0, step returns acc
        lemma_cis_step_preserves(i, acc, f_enc);
        let step_fn = |x: nat| eval_comp(check_is_sentence_step(), x);
        assert(step_fn(pair(i, pair(acc, f_enc))) == acc);

        // Inductive step
        lemma_check_is_sentence_iter(f_enc, (fuel - 1) as nat, acc);
    }
}

/// For encoded sentences, check_is_sentence returns nonzero.
/// check_is_sentence_step being opaque ensures the closure from eval_comp's
/// BoundedRec unfolding matches our iterate closure exactly.
pub proof fn lemma_check_is_sentence_backward_helper(f_enc: nat)
    requires
        forall|v: nat| eval_comp(has_free_var_comp(), pair(f_enc, v)) == 0,
    ensures
        eval_comp(check_is_sentence(), f_enc) != 0,
{
    // check_is_sentence() = BoundedRec { Id, Const(1), check_is_sentence_step() }
    // eval_comp unfolds to: iterate(|x| eval_comp(check_is_sentence_step(), x), f_enc, 1, f_enc)
    // Both closures capture the same opaque check_is_sentence_step() → identity match
    lemma_check_is_sentence_iter(f_enc, f_enc, 1);
}

} // verus!
