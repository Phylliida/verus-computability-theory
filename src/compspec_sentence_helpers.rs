use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

/// Sublemma: eval_comp(cs_comp(hfv, pair_expr), input) == 0
proof fn lemma_cis_check_eval(i: nat, acc: nat, f_enc: nat)
    requires
        eval_comp(has_free_var_comp(), pair(f_enc, i)) == 0,
    ensures ({
        let input = pair(i, pair(acc, f_enc));
        let hfv = has_free_var_comp();
        let pair_expr = CompSpec::CantorPair {
            left: Box::new(cs_snd(cs_snd(CompSpec::Id))),
            right: Box::new(cs_fst(CompSpec::Id)),
        };
        let check = cs_comp(hfv, pair_expr);
        eval_comp(check, input) == 0nat
    }),
{
    let input = pair(i, pair(acc, f_enc));
    lemma_unpair1_pair(i, pair(acc, f_enc));
    lemma_unpair2_pair(i, pair(acc, f_enc));
    lemma_unpair1_pair(acc, f_enc);
    lemma_unpair2_pair(acc, f_enc);

    let hfv = has_free_var_comp();
    let pair_expr = CompSpec::CantorPair {
        left: Box::new(cs_snd(cs_snd(CompSpec::Id))),
        right: Box::new(cs_fst(CompSpec::Id)),
    };

    // Evaluate the left component: cs_snd(cs_snd(Id))
    lemma_eval_snd(CompSpec::Id, input);
    // eval_comp(CantorSnd(Id), input) = unpair2(input) = pair(acc, f_enc)
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    // eval_comp(CantorSnd(CantorSnd(Id)), input) = unpair2(pair(acc, f_enc)) = f_enc
    assert(eval_comp(cs_snd(cs_snd(CompSpec::Id)), input) == f_enc);

    // Evaluate the right component: cs_fst(Id)
    lemma_eval_fst(CompSpec::Id, input);
    // eval_comp(CantorFst(Id), input) = unpair1(input) = i
    assert(eval_comp(cs_fst(CompSpec::Id), input) == i);

    // CantorPair evaluates to pair of sub-evaluations
    assert(eval_comp(pair_expr, input) == pair(f_enc, i));

    // cs_comp(hfv, pair_expr): Comp case of eval_comp
    lemma_eval_comp(hfv, pair_expr, input);
    // eval_comp(check, input) = eval_comp(hfv, pair(f_enc, i)) == 0 by requires
}

/// Main eval: the step computes acc when has_free_var returns 0.
proof fn lemma_cis_step_eval_raw(i: nat, acc: nat, f_enc: nat)
    requires
        eval_comp(has_free_var_comp(), pair(f_enc, i)) == 0,
    ensures ({
        let acc_expr = cs_fst(cs_snd(CompSpec::Id));
        let hfv = has_free_var_comp();
        let pair_expr = CompSpec::CantorPair {
            left: Box::new(cs_snd(cs_snd(CompSpec::Id))),
            right: Box::new(cs_fst(CompSpec::Id)),
        };
        let check = cs_comp(hfv, pair_expr);
        let not_check = cs_not(check);
        let step = cs_and(acc_expr, not_check);
        eval_comp(step, pair(i, pair(acc, f_enc))) == acc
    }),
{
    let input = pair(i, pair(acc, f_enc));

    lemma_cis_check_eval(i, acc, f_enc);

    lemma_unpair1_pair(i, pair(acc, f_enc));
    lemma_unpair2_pair(i, pair(acc, f_enc));
    lemma_unpair1_pair(acc, f_enc);

    let acc_expr = cs_fst(cs_snd(CompSpec::Id));
    let hfv = has_free_var_comp();
    let pair_expr = CompSpec::CantorPair {
        left: Box::new(cs_snd(cs_snd(CompSpec::Id))),
        right: Box::new(cs_fst(CompSpec::Id)),
    };
    let check = cs_comp(hfv, pair_expr);
    let not_check = cs_not(check);

    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    assert(eval_comp(acc_expr, input) == acc);

    // check evaluates to 0 (from sublemma), so cs_not gives 1
    assert(eval_comp(check, input) == 0nat);
    assert(eval_comp(not_check, input) == 1nat);

    lemma_eval_cs_and(acc_expr, not_check, input);
    assert(eval_comp(cs_and(acc_expr, not_check), input) == acc * 1nat);
}

/// The manually-built step equals check_is_sentence_step.
proof fn lemma_cis_step_eq()
    ensures ({
        let acc_expr = cs_fst(cs_snd(CompSpec::Id));
        let hfv = has_free_var_comp();
        let pair_expr = CompSpec::CantorPair {
            left: Box::new(cs_snd(cs_snd(CompSpec::Id))),
            right: Box::new(cs_fst(CompSpec::Id)),
        };
        let check = cs_comp(hfv, pair_expr);
        let not_check = cs_not(check);
        let step = cs_and(acc_expr, not_check);
        step == check_is_sentence_step()
    }),
{
    reveal(check_is_sentence_step);
}

/// Main: one step of check_is_sentence_step preserves acc when has_free_var returns 0.
pub proof fn lemma_cis_step_preserves(i: nat, acc: nat, f_enc: nat)
    requires
        eval_comp(has_free_var_comp(), pair(f_enc, i)) == 0,
    ensures
        eval_comp(check_is_sentence_step(), pair(i, pair(acc, f_enc))) == acc,
{
    lemma_cis_step_eval_raw(i, acc, f_enc);
    lemma_cis_step_eq();
}

} // verus!
