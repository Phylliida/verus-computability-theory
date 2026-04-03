use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Tag match for Quantifier (tags 7-8): if checker accepts, result tag matches phi tag.
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_quant_tag_match(phi_enc: nat, result_enc: nat, var: nat)
    requires
        unpair1(phi_enc) >= 7nat,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        unpair1(result_enc) == unpair1(phi_enc),
{
    if unpair1(result_enc) != unpair1(phi_enc) {
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
        let si = pair(phi_enc as nat, pair(base, input));

        lemma_check_subst_unfold(phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);

        assert(eval_comp(check_subst_step(), si)
            == eval_comp(check_subst_process_pair(), si)) by {
            lemma_subst_step_dispatch(phi_enc, entry + 1, 0nat, 1nat, 0nat, 0nat,
                phi_enc, result_enc, var);
        }

        extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        let phi_tag_cs = cs_fst(csa_phi_node());
        let result_tag_cs = cs_fst(csa_result_node());

        //  Dispatch to compound (tag >= 7 >= 3)
        assert(eval_comp(check_subst_process_pair(), si)
            == eval_comp(check_subst_compound(), si)) by {
            lemma_subst_dispatch_compound(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
                phi_enc, result_enc, var);
        }

        //  cs_eq = 0 (tags differ)
        let tags_match = cs_eq(phi_tag_cs, result_tag_cs);
        assert(eval_comp(tags_match, si) == 0nat) by {
            lemma_eval_eq(phi_tag_cs, result_tag_cs, si);
        }

        //  is_quant != 0 (tag >= 7)
        let is_quant = cs_lt(cs_const(6), phi_tag_cs);
        assert(eval_comp(is_quant, si) != 0nat) by {
            lemma_eval_lt(cs_const(6), phi_tag_cs, si);
        }

        let t_enc_cs = csa_t_enc();
        let t_set_cs = csa_t_set();
        let rest_cs = csa_rest();
        let phi_content_cs = cs_snd(csa_phi_node());
        let result_content_cs = cs_snd(csa_result_node());
        let bound_var_cs = cs_fst(phi_content_cs);
        let var_cs = cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))));
        let bound_eq_var = cs_eq(bound_var_cs, var_cs);
        let result_bound_cs = cs_fst(result_content_cs);

        let step_result = eval_comp(check_subst_compound(), si);
        assert(unpair1(unpair2(step_result)) == 0nat) by {
            //  Build binary then_br (for outer IfZero reference)
            let lp_cs = cs_pair(cs_fst(phi_content_cs), cs_fst(result_content_cs));
            let rp_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));
            let lp1 = CompSpec::Add { left: Box::new(lp_cs), right: Box::new(cs_const(1)) };
            let rp1 = CompSpec::Add { left: Box::new(rp_cs), right: Box::new(cs_const(1)) };
            let binary_then = cs_pair(
                cs_pair(lp1, cs_pair(rp1, rest_cs)),
                cs_pair(tags_match, cs_pair(t_enc_cs, t_set_cs)));

            //  Build quantifier branches
            let sub_pair_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));
            let sp1 = CompSpec::Add { left: Box::new(sub_pair_cs), right: Box::new(cs_const(1)) };
            let quant_free = cs_pair(
                cs_pair(sp1, rest_cs),
                cs_pair(cs_and(tags_match, cs_eq(bound_var_cs, result_bound_cs)),
                    cs_pair(t_enc_cs, t_set_cs)));
            let quant_bound = cs_pair(
                rest_cs,
                cs_pair(cs_and(tags_match, cs_eq(csa_phi_node(), csa_result_node())),
                    cs_pair(t_enc_cs, t_set_cs)));
            let quant_br = CompSpec::IfZero {
                cond: Box::new(bound_eq_var),
                then_br: Box::new(quant_free),
                else_br: Box::new(quant_bound),
            };

            //  IfZero(is_quant!=0) → else → quant_br
            lemma_eval_ifzero_else(is_quant, binary_then, quant_br, si);

            //  Evaluate bound_eq_var
            lemma_eval_fst(phi_content_cs, si);
            lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), si);
            lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), si);
            lemma_eval_snd(cs_snd(CompSpec::Id), si);
            lemma_eval_snd(CompSpec::Id, si);
            lemma_unpair2_pair(phi_enc as nat, pair(base, input));
            lemma_unpair2_pair(base, input);
            lemma_unpair2_pair(phi_enc, pair(result_enc, var));
            lemma_unpair2_pair(result_enc, var);
            lemma_eval_eq(bound_var_cs, var_cs, si);
            let bev = eval_comp(bound_eq_var, si);

            if bev == 0 {
                //  quant_free branch: valid = cs_and(0, ...) = 0
                lemma_eval_ifzero_then(bound_eq_var, quant_free, quant_bound, si);
                lemma_eval_fst(result_content_cs, si);
                lemma_eval_eq(bound_var_cs, result_bound_cs, si);
                lemma_eval_cs_and(tags_match, cs_eq(bound_var_cs, result_bound_cs), si);
                assert(0nat * eval_comp(cs_eq(bound_var_cs, result_bound_cs), si) == 0nat)
                    by (nonlinear_arith);
                lemma_eval_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs), si);
                lemma_eval_add(sub_pair_cs, cs_const(1), si);
                lemma_eval_pair(sp1, rest_cs, si);
                lemma_eval_pair(t_enc_cs, t_set_cs, si);
                lemma_eval_pair(cs_and(tags_match, cs_eq(bound_var_cs, result_bound_cs)),
                    cs_pair(t_enc_cs, t_set_cs), si);
                lemma_eval_pair(cs_pair(sp1, rest_cs),
                    cs_pair(cs_and(tags_match, cs_eq(bound_var_cs, result_bound_cs)),
                        cs_pair(t_enc_cs, t_set_cs)), si);
                let qf = eval_comp(quant_free, si);
                lemma_unpair2_pair(eval_comp(cs_pair(sp1, rest_cs), si),
                    eval_comp(cs_pair(cs_and(tags_match, cs_eq(bound_var_cs, result_bound_cs)),
                        cs_pair(t_enc_cs, t_set_cs)), si));
                lemma_unpair1_pair(0nat, eval_comp(cs_pair(t_enc_cs, t_set_cs), si));
            } else {
                //  quant_bound branch: valid = cs_and(0, ...) = 0
                lemma_eval_ifzero_else(bound_eq_var, quant_free, quant_bound, si);
                lemma_eval_eq(csa_phi_node(), csa_result_node(), si);
                lemma_eval_cs_and(tags_match, cs_eq(csa_phi_node(), csa_result_node()), si);
                assert(0nat * eval_comp(cs_eq(csa_phi_node(), csa_result_node()), si) == 0nat)
                    by (nonlinear_arith);
                lemma_eval_pair(t_enc_cs, t_set_cs, si);
                lemma_eval_pair(cs_and(tags_match, cs_eq(csa_phi_node(), csa_result_node())),
                    cs_pair(t_enc_cs, t_set_cs), si);
                lemma_eval_pair(rest_cs,
                    cs_pair(cs_and(tags_match, cs_eq(csa_phi_node(), csa_result_node())),
                        cs_pair(t_enc_cs, t_set_cs)), si);
                let qb = eval_comp(quant_bound, si);
                lemma_unpair2_pair(eval_comp(rest_cs, si),
                    eval_comp(cs_pair(cs_and(tags_match, cs_eq(csa_phi_node(), csa_result_node())),
                        cs_pair(t_enc_cs, t_set_cs)), si));
                lemma_unpair1_pair(0nat, eval_comp(cs_pair(t_enc_cs, t_set_cs), si));
            }
        }

        //  valid_zero_stable
        lemma_pair_surjective(step_result);
        lemma_pair_surjective(unpair2(step_result));
        let new_state = unpair2(unpair2(step_result));
        lemma_pair_surjective(new_state);
        lemma_subst_valid_zero_stable(phi_enc, unpair1(step_result),
            unpair1(new_state), unpair2(new_state),
            phi_enc, result_enc, var);
        lemma_unpair2_pair(unpair1(step_result), pair(0nat, new_state));
        lemma_unpair1_pair(0nat, new_state);
    }
}

} // verus!
