use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Iterate-level tag match for Eq (tag 0): if iterate from Eq entry gives valid != 0,
///  result must have tag 0.
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_eq_tag_iter(
    phi_enc: nat, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
)
    requires
        unpair1(phi_enc) == 0nat,
        fuel >= 1,
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(phi_enc, result_enc) + 1, rest),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0,
    ensures
        unpair1(result_enc) == 0nat,
{
    hide(eval_comp);
    if unpair1(result_enc) != 0 {
        let entry = pair(phi_enc, result_enc);
        let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
        let input = pair(pe, pair(re, var));
        let si = pair((fuel - 1) as nat, pair(acc, input));

        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, input);

        //  Step dispatch → atomic_terms (tag 0)
        assert(eval_comp(check_subst_step(), si)
            == eval_comp(check_subst_atomic_terms(), si)) by {
            reveal(eval_comp);
            lemma_subst_step_dispatch((fuel - 1) as nat, entry + 1, rest, 1nat, te, ts,
                pe, re, var);
            extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
                pe, re, var);
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

        //  tag_eq = 0 (tags differ)
        assert(eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si) == 0nat) by {
            reveal(eval_comp);
            extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
                pe, re, var);
            lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
        }

        //  valid product = 0 * (v1 * v2) = 0. Eval the pair structure.
        let step_result = eval_comp(check_subst_step(), si);
        assert(unpair1(unpair2(step_result)) == 0nat) by {
            reveal(eval_comp);
            extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
                pe, re, var);
            lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
            lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
                cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
            assert(0nat * eval_comp(cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si) == 0nat)
                by (nonlinear_arith);
            let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
                cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
            lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
            lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
            lemma_unpair2_pair(eval_comp(csa_rest(), si),
                eval_comp(cs_pair(valid_cs, cs_snd(csa_term2())), si));
            lemma_unpair1_pair(0nat, eval_comp(cs_snd(csa_term2()), si));
        }

        //  valid_zero_stable for remaining fuel
        lemma_pair_surjective(step_result);
        lemma_pair_surjective(unpair2(step_result));
        let ns = unpair2(unpair2(step_result));
        lemma_pair_surjective(ns);
        lemma_subst_valid_zero_stable((fuel - 1) as nat, unpair1(step_result),
            unpair1(ns), unpair2(ns), pe, re, var);
        lemma_unpair2_pair(unpair1(step_result), pair(0nat, ns));
        lemma_unpair1_pair(0nat, ns);
    }
}

///  Iterate-level tag match for In (tag 1).
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_in_tag_iter(
    phi_enc: nat, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
)
    requires
        unpair1(phi_enc) == 1nat,
        fuel >= 1,
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(phi_enc, result_enc) + 1, rest),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0,
    ensures
        unpair1(result_enc) == 1nat,
{
    hide(eval_comp);
    if unpair1(result_enc) != 1 {
        let entry = pair(phi_enc, result_enc);
        let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
        let input = pair(pe, pair(re, var));
        let si = pair((fuel - 1) as nat, pair(acc, input));

        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, input);

        //  Step dispatch → atomic_terms (tag 1: else → then)
        assert(eval_comp(check_subst_step(), si)
            == eval_comp(check_subst_atomic_terms(), si)) by {
            reveal(eval_comp);
            lemma_subst_step_dispatch((fuel - 1) as nat, entry + 1, rest, 1nat, te, ts,
                pe, re, var);
            extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
                pe, re, var);
            let phi_tag_cs = cs_fst(csa_phi_node());
            let pred_tag = cs_comp(CompSpec::Pred, phi_tag_cs);
            lemma_eval_comp(CompSpec::Pred, phi_tag_cs, si);
            lemma_eval_pred(1nat);
            lemma_eval_ifzero_then(pred_tag,
                check_subst_atomic_terms(),
                CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, pred_tag)),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }, si);
            lemma_eval_ifzero_else(phi_tag_cs,
                check_subst_atomic_terms(),
                CompSpec::IfZero {
                    cond: Box::new(pred_tag),
                    then_br: Box::new(check_subst_atomic_terms()),
                    else_br: Box::new(CompSpec::IfZero {
                        cond: Box::new(cs_comp(CompSpec::Pred, pred_tag)),
                        then_br: Box::new(check_subst_unary()),
                        else_br: Box::new(check_subst_compound()),
                    }),
                }, si);
        }

        //  tag_eq = 0
        assert(eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si) == 0nat) by {
            reveal(eval_comp);
            extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
                pe, re, var);
            lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
        }

        //  valid = 0
        let step_result = eval_comp(check_subst_step(), si);
        assert(unpair1(unpair2(step_result)) == 0nat) by {
            reveal(eval_comp);
            extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
                pe, re, var);
            lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
            lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
                cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
            assert(0nat * eval_comp(cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si) == 0nat)
                by (nonlinear_arith);
            let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
                cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
            lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
            lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
            lemma_unpair2_pair(eval_comp(csa_rest(), si),
                eval_comp(cs_pair(valid_cs, cs_snd(csa_term2())), si));
            lemma_unpair1_pair(0nat, eval_comp(cs_snd(csa_term2()), si));
        }

        lemma_pair_surjective(step_result);
        lemma_pair_surjective(unpair2(step_result));
        let ns = unpair2(unpair2(step_result));
        lemma_pair_surjective(ns);
        lemma_subst_valid_zero_stable((fuel - 1) as nat, unpair1(step_result),
            unpair1(ns), unpair2(ns), pe, re, var);
        lemma_unpair2_pair(unpair1(step_result), pair(0nat, ns));
        lemma_unpair1_pair(0nat, ns);
    }
}

} // verus!
