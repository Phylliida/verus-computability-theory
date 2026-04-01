use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers2::lemma_subst_eq_terms_pass;
use crate::compspec_subst_extract::extract_atomic_eq_values;

verus! {

///  Atomic Eq: check_subst_atomic_terms result has rest + nonzero valid.
///  The caller uses Part 1's step==atomic_terms equality to derive step result.
#[verifier::rlimit(800)]
pub proof fn lemma_subst_atomic_eq_result(
    left: Term, right: Term, var: nat, t: Term,
    rest: nat, valid: nat, t_enc_val: nat, t_set_val: nat,
    phi_enc: nat, result_enc: nat,
)
    requires
        valid > 0,
        t_set_val == 0 || t_enc_val == encode_term(t),
    ensures ({
        let f = Formula::Eq { left, right };
        let entry = pair(encode(f), encode(subst(f, var, t)));
        let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
        let s = pair(phi_enc, pair(result_enc, var));
        let n = pair(0nat, pair(acc, s));
        //  Only references check_subst_atomic_terms (small tree), not check_subst_step (huge)
        unpair1(eval_comp(check_subst_atomic_terms(), n)) == rest &&
        unpair1(unpair2(eval_comp(check_subst_atomic_terms(), n))) != 0
    }),
{
    let f = Formula::Eq { left, right };
    let entry = pair(encode(f), encode(subst(f, var, t)));
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    let s = pair(phi_enc, pair(result_enc, var));
    let n = pair(0nat, pair(acc, s));

    //  Part 1: v1 != 0, v2 != 0, rest value
    lemma_subst_eq_terms_pass(left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);

    //  Structural equality
    let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
    assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));

    //  Tags (scoped)
    assert(eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), n) == 1nat) by {
        extract_atomic_eq_values(left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), n);
    }

    //  Bridge: structural equality → eval equality
    assert(eval_comp(check_subst_atomic_terms(), n)
        == eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), n));

    //  Eval chain
    let v1 = eval_comp(cs_fst(csa_term1()), n);
    let v2 = eval_comp(cs_fst(csa_term2()), n);
    lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), n);
    lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), n);
    lemma_eval_pair(valid_cs, cs_snd(csa_term2()), n);
    lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), n);
    assert(1nat * (v1 * v2) != 0) by (nonlinear_arith) requires v1 != 0, v2 != 0;

    //  Explicitly chain: eval_comp(cs_pair(...), n) → pair(rest, pair(v, state))
    let at_result = eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), n);
    lemma_unpair1_pair(rest, eval_comp(cs_pair(valid_cs, cs_snd(csa_term2())), n));
    assert(unpair1(at_result) == rest);
    lemma_unpair2_pair(rest, eval_comp(cs_pair(valid_cs, cs_snd(csa_term2())), n));
    lemma_unpair1_pair(1nat * (v1 * v2), eval_comp(cs_snd(csa_term2()), n));
    assert(unpair1(unpair2(at_result)) != 0);

    //  Bridge: check_subst_atomic_terms result == at_result
    assert(eval_comp(check_subst_atomic_terms(), n) == at_result);
    assert(unpair1(eval_comp(check_subst_atomic_terms(), n)) == rest);
    assert(unpair1(unpair2(eval_comp(check_subst_atomic_terms(), n))) != 0);
}

} // verus!
