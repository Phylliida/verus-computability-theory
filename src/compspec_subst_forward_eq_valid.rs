use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_extract::extract_general;

verus! {

///  Show full_valid != 0 for forward Eq case.
///  Evaluates the valid product, shows step result form, uses empty-stack stability.
///  Isolated in own file for rlimit.
#[verifier::rlimit(800)]
pub proof fn lemma_forward_eq_valid_nonzero(
    si: nat, v1: nat, v2: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        ({
            let entry = pair(phi_enc, result_enc);
            let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
            let input = pair(phi_enc, pair(result_enc, var));
            si == pair(phi_enc as nat, pair(base, input))
        }),
        eval_comp(cs_fst(csa_term1()), si) == v1,
        eval_comp(cs_fst(csa_term2()), si) == v2,
        eval_comp(check_subst_step(), si) == eval_comp(check_subst_atomic_terms(), si),
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
        //  Unfold facts (from caller)
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var)))
            == unpair1(unpair2(compspec_iterate(check_subst_step(), (phi_enc + 1) as nat,
                pair(pair(pair(phi_enc, result_enc) + 1, 0nat), pair(1nat, pair(0nat, 0nat))),
                pair(phi_enc, pair(result_enc, var))))),
        compspec_iterate(check_subst_step(), (phi_enc + 1) as nat,
            pair(pair(pair(phi_enc, result_enc) + 1, 0nat), pair(1nat, pair(0nat, 0nat))),
            pair(phi_enc, pair(result_enc, var)))
            == compspec_iterate(check_subst_step(), phi_enc,
                eval_comp(check_subst_step(), si),
                pair(phi_enc, pair(result_enc, var))),
        //  Tag match (phi and result both have same tag)
        eval_comp(cs_fst(csa_phi_node()), si) == eval_comp(cs_fst(csa_result_node()), si),
    ensures
        1nat * (v1 * v2) != 0nat,
{
    //  Tag check = 1 (same tags)
    let tag_eq = eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si);
    assert(tag_eq == 1nat) by {
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
    }

    //  Valid product
    let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
    let full_valid = eval_comp(valid_cs, si);
    assert(full_valid == 1nat * (v1 * v2)) by {
        lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
        lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
            cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
    }

    //  Step result form: pair(0, pair(full_valid, state))
    assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));
    extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
        phi_enc, result_enc, var);
    lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
    lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
    let state = eval_comp(cs_snd(csa_term2()), si);
    assert(eval_comp(check_subst_step(), si) == pair(0nat, pair(full_valid, state)));

    //  Empty-stack stability → check_subst_comp == full_valid
    lemma_pair_surjective(state);
    lemma_subst_empty_stable_general(phi_enc, full_valid,
        unpair1(state), unpair2(state), phi_enc, result_enc, var);
    lemma_unpair2_pair(0nat, pair(full_valid, state));
    lemma_unpair1_pair(full_valid, state);

    //  full_valid != 0 (from check_subst_comp != 0)
    assert(full_valid != 0nat);
}

} // verus!
