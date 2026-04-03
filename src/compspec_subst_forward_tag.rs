use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_extract::extract_general;

verus! {

///  Tag match for Eq (tag 0): if checker accepts, result must have tag 0.
///  If result has tag != 0, the tag_eq factor in valid is 0, making valid = 0.
///  Isolated in own file for rlimit.
#[verifier::rlimit(1000)]
pub proof fn lemma_forward_eq_tag_match(phi_enc: nat, result_enc: nat, var: nat)
    requires
        unpair1(phi_enc) == 0nat,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        unpair1(result_enc) == 0nat,
{
    if unpair1(result_enc) != 0 {
        //  Derive contradiction: tag mismatch → checker returns 0
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
        let si = pair(phi_enc as nat, pair(base, input));

        lemma_check_subst_unfold(phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);

        //  Dispatch → atomic_terms (phi_tag == 0)
        assert(eval_comp(check_subst_step(), si) == eval_comp(check_subst_atomic_terms(), si)) by {
            lemma_subst_step_dispatch(phi_enc, entry + 1, 0nat, 1nat, 0nat, 0nat,
                phi_enc, result_enc, var);
            extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
                phi_enc, result_enc, var);
            let phi_tag_cs = cs_fst(csa_phi_node());
            lemma_eval_ifzero_then(phi_tag_cs,
                check_subst_atomic_terms(),
                CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, phi_tag_cs)),
                    then_br: Box::new(check_subst_atomic_terms()),
                    else_br: Box::new(CompSpec::IfZero {
                        cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs))),
                        then_br: Box::new(check_subst_unary()),
                        else_br: Box::new(check_subst_compound()),
                    }),
                }, si);
        }

        //  tag_eq = cs_eq(0, result_tag) = 0 (since result_tag != 0)
        extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        let tag_eq = eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si);
        assert(tag_eq == 0nat) by {
            lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
        }

        //  valid = tag_eq * (...) = 0 * (...) = 0
        let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
            cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
        assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));
        let full_valid = eval_comp(valid_cs, si);
        assert(full_valid == 0nat) by {
            lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
            lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
                cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
            assert(0nat * eval_comp(cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si) == 0nat)
                by (nonlinear_arith);
        }

        //  Step result has valid = 0
        lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
        lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
        let state = eval_comp(cs_snd(csa_term2()), si);
        assert(eval_comp(check_subst_step(), si) == pair(0nat, pair(0nat, state)));

        //  Empty-stack stability with valid=0 preserves
        lemma_pair_surjective(state);
        lemma_subst_empty_stable_general(phi_enc, 0nat,
            unpair1(state), unpair2(state), phi_enc, result_enc, var);

        //  checker result = 0
        lemma_unpair2_pair(0nat, pair(0nat, state));
        lemma_unpair1_pair(0nat, state);
        //  But requires says checker result != 0 — contradiction
    }
}

///  Tag match for In (tag 1): if checker accepts, result must have tag 1.
#[verifier::rlimit(1000)]
pub proof fn lemma_forward_in_tag_match(phi_enc: nat, result_enc: nat, var: nat)
    requires
        unpair1(phi_enc) == 1nat,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        unpair1(result_enc) == 1nat,
{
    if unpair1(result_enc) != 1 {
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
        let si = pair(phi_enc as nat, pair(base, input));

        lemma_check_subst_unfold(phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);

        //  Dispatch → atomic_terms (phi_tag == 1: else then then)
        assert(eval_comp(check_subst_step(), si) == eval_comp(check_subst_atomic_terms(), si)) by {
            lemma_subst_step_dispatch(phi_enc, entry + 1, 0nat, 1nat, 0nat, 0nat,
                phi_enc, result_enc, var);
            extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
                phi_enc, result_enc, var);
            let phi_tag_cs = cs_fst(csa_phi_node());
            lemma_eval_ifzero_else(phi_tag_cs,
                check_subst_atomic_terms(),
                CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, phi_tag_cs)),
                    then_br: Box::new(check_subst_atomic_terms()),
                    else_br: Box::new(CompSpec::IfZero {
                        cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs))),
                        then_br: Box::new(check_subst_unary()),
                        else_br: Box::new(check_subst_compound()),
                    }),
                }, si);
            lemma_eval_comp(CompSpec::Pred, phi_tag_cs, si);
            lemma_eval_pred(1nat);
            lemma_eval_ifzero_then(cs_comp(CompSpec::Pred, phi_tag_cs),
                check_subst_atomic_terms(),
                CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs))),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }, si);
        }

        //  tag_eq = cs_eq(1, result_tag) = 0 (since result_tag != 1)
        extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        let tag_eq = eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si);
        assert(tag_eq == 0nat) by {
            lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
        }

        let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
            cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
        assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));
        let full_valid = eval_comp(valid_cs, si);
        assert(full_valid == 0nat) by {
            lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
            lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
                cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
            assert(0nat * eval_comp(cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si) == 0nat)
                by (nonlinear_arith);
        }

        lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
        lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
        let state = eval_comp(cs_snd(csa_term2()), si);
        assert(eval_comp(check_subst_step(), si) == pair(0nat, pair(0nat, state)));

        lemma_pair_surjective(state);
        lemma_subst_empty_stable_general(phi_enc, 0nat,
            unpair1(state), unpair2(state), phi_enc, result_enc, var);
        lemma_unpair2_pair(0nat, pair(0nat, state));
        lemma_unpair1_pair(0nat, state);
    }
}

} // verus!
