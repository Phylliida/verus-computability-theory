use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Tag match for Not (tag 2): if checker accepts and phi has tag 2, result has tag 2.
///  Contradiction: tag mismatch → check_subst_unary sets valid = cs_eq(2, result_tag) = 0.
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_not_tag_match(phi_enc: nat, result_enc: nat, var: nat)
    requires
        unpair1(phi_enc) == 2nat,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        unpair1(result_enc) == 2nat,
{
    if unpair1(result_enc) != 2 {
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
        let si = pair(phi_enc as nat, pair(base, input));

        lemma_check_subst_unfold(phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);

        //  Dispatch: step → process_pair → unary (tag 2)
        assert(eval_comp(check_subst_step(), si)
            == eval_comp(check_subst_process_pair(), si)) by {
            lemma_subst_step_dispatch(phi_enc, entry + 1, 0nat, 1nat, 0nat, 0nat,
                phi_enc, result_enc, var);
        }

        //  Extract phi_tag, result_tag
        extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        let phi_tag_cs = cs_fst(csa_phi_node());
        let result_tag_cs = cs_fst(csa_result_node());

        //  Dispatch process_pair: tag 2 → else → else → then (unary)
        assert(eval_comp(check_subst_process_pair(), si)
            == eval_comp(check_subst_unary(), si)) by {
            lemma_eval_comp(CompSpec::Pred, phi_tag_cs, si);
            lemma_eval_pred(2nat);
            let pred_tag = cs_comp(CompSpec::Pred, phi_tag_cs);
            lemma_eval_comp(CompSpec::Pred, pred_tag, si);
            lemma_eval_pred(1nat);
            let pred_pred_tag = cs_comp(CompSpec::Pred, pred_tag);
            lemma_eval_ifzero_then(pred_pred_tag,
                check_subst_unary(), check_subst_compound(), si);
            lemma_eval_ifzero_else(pred_tag,
                check_subst_atomic_terms(),
                CompSpec::IfZero {
                    cond: Box::new(pred_pred_tag),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }, si);
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
                }, si);
        }

        //  cs_eq(phi_tag=2, result_tag) = 0 (since result_tag != 2)
        let tag_eq = eval_comp(cs_eq(phi_tag_cs, result_tag_cs), si);
        assert(tag_eq == 0nat) by {
            lemma_eval_eq(phi_tag_cs, result_tag_cs, si);
        }

        //  Evaluate check_subst_unary: valid = tag_eq = 0
        let rest_cs = csa_rest();
        let t_enc_cs = csa_t_enc();
        let t_set_cs = csa_t_set();
        let phi_sub_cs = cs_snd(csa_phi_node());
        let result_sub_cs = cs_snd(csa_result_node());
        let new_entry_cs = cs_pair(phi_sub_cs, result_sub_cs);
        let valid_cs = cs_eq(phi_tag_cs, result_tag_cs);

        assert(eval_comp(check_subst_unary(), si) == ({
            let phi_sub = unpair2(phi_enc);
            let result_sub = unpair2(result_enc);
            let new_entry = pair(phi_sub, result_sub);
            pair(pair(new_entry + 1, 0nat), pair(0nat, pair(0nat, 0nat)))
        })) by {
            lemma_eval_pair(phi_sub_cs, result_sub_cs, si);
            lemma_eval_add(new_entry_cs, cs_const(1), si);
            let ne_plus_1 = CompSpec::Add { left: Box::new(new_entry_cs), right: Box::new(cs_const(1)) };
            lemma_eval_pair(ne_plus_1, rest_cs, si);
            lemma_eval_pair(t_enc_cs, t_set_cs, si);
            lemma_eval_pair(valid_cs, cs_pair(t_enc_cs, t_set_cs), si);
            lemma_eval_pair(cs_pair(ne_plus_1, rest_cs),
                cs_pair(valid_cs, cs_pair(t_enc_cs, t_set_cs)), si);
        }

        //  Step result has valid = 0. Use valid_zero_stable for remaining fuel.
        let step_result = eval_comp(check_subst_step(), si);
        let new_stack = unpair1(step_result);
        let new_state = unpair2(unpair2(step_result));
        lemma_pair_surjective(step_result);
        lemma_pair_surjective(unpair2(step_result));
        lemma_pair_surjective(new_state);
        lemma_subst_valid_zero_stable(phi_enc, new_stack,
            unpair1(new_state), unpair2(new_state),
            phi_enc, result_enc, var);
        lemma_unpair2_pair(new_stack, pair(0nat, new_state));
        lemma_unpair1_pair(0nat, new_state);
    }
}

} // verus!
