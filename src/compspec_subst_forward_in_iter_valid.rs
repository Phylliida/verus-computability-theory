use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Show valid product != 0 for In (tag 1) at iterate level.
///  Mirror of lemma_forward_eq_valid_iter with tag 1 dispatch.
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_in_valid_iter(
    phi_enc: nat, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
    v1: nat, v2: nat,
)
    requires
        unpair1(phi_enc) == 1nat,
        unpair1(result_enc) == 1nat,
        fuel >= 1,
        ({
            let entry = pair(phi_enc, result_enc);
            let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
            let si = pair((fuel - 1) as nat, pair(acc, pair(pe, pair(re, var))));
            eval_comp(cs_fst(csa_term1()), si) == v1 &&
            eval_comp(cs_fst(csa_term2()), si) == v2
        }),
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(phi_enc, result_enc) + 1, rest),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0,
    ensures
        v1 != 0nat,
        v2 != 0nat,
{
    hide(eval_comp);
    let entry = pair(phi_enc, result_enc);
    let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
    let input = pair(pe, pair(re, var));
    let si = pair((fuel - 1) as nat, pair(acc, input));

    lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, input);

    //  Step dispatch to atomic_terms (tag 1: else → then)
    assert(eval_comp(check_subst_step(), si)
        == eval_comp(check_subst_atomic_terms(), si)) by {
        reveal(eval_comp);
        lemma_subst_step_dispatch((fuel - 1) as nat, entry + 1, rest, 1nat, te, ts,
            pe, re, var);
        extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
            pe, re, var);
        let phi_tag_cs = cs_fst(csa_phi_node());
        //  IfZero(phi_tag=1) → else
        let pred_tag = cs_comp(CompSpec::Pred, phi_tag_cs);
        lemma_eval_comp(CompSpec::Pred, phi_tag_cs, si);
        lemma_eval_pred(1nat);
        //  IfZero(Pred(1)=0) → then → atomic_terms
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

    //  tag_eq = cs_eq(1, 1) = 1
    assert(eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si) == 1nat) by {
        reveal(eval_comp);
        extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
            pe, re, var);
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
    }

    //  Valid product = 1 * (v1 * v2)
    let valid_product = 1nat * (v1 * v2);
    assert(eval_comp(check_subst_atomic_terms(), si)
        == pair(rest, pair(valid_product, eval_comp(cs_snd(csa_term2()), si)))) by {
        reveal(eval_comp);
        extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
            pe, re, var);
        lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
        lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
            cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
        let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
            cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
        lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
        lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
    }

    if valid_product == 0nat {
        let state = eval_comp(cs_snd(csa_term2()), si);
        assert(eval_comp(check_subst_step(), si) == pair(rest, pair(0nat, state)));
        lemma_pair_surjective(state);
        lemma_subst_valid_zero_stable((fuel - 1) as nat, rest,
            unpair1(state), unpair2(state), pe, re, var);
        lemma_unpair2_pair(rest, pair(0nat, state));
        lemma_unpair1_pair(0nat, state);
    }

    if v1 == 0nat {
        assert(v1 * v2 == 0nat) by (nonlinear_arith)
            requires v1 == 0nat;
    }
    if v2 == 0nat {
        assert(v1 * v2 == 0nat) by (nonlinear_arith)
            requires v2 == 0nat;
    }
}

} // verus!
