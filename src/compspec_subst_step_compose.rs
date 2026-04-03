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
    i: nat, left: Term, right: Term, var: nat, t: Term,
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
        let n = pair(i, pair(acc, s));
        //  Exact result: pair(rest, pair(1, state)) where state = cs_snd(csa_term2()) eval
        eval_comp(check_subst_step(), n) == pair(rest, pair(1nat,
            eval_comp(cs_snd(csa_term2()), n)))
    }),
{
    let f = Formula::Eq { left, right };
    let entry = pair(encode(f), encode(subst(f, var, t)));
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    let s = pair(phi_enc, pair(result_enc, var));
    let n = pair(i, pair(acc, s));

    //  Part 1: v1 != 0, v2 != 0, rest value
    lemma_subst_eq_terms_pass(i, left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);

    //  Structural equality
    let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
    assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));

    //  Tags (scoped)
    assert(eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), n) == 1nat) by {
        extract_atomic_eq_values(i, left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), n);
    }

    //  Bridge: structural equality → eval equality
    assert(eval_comp(check_subst_atomic_terms(), n)
        == eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), n));

    //  Eval chain — v1 == 1 and v2 == 1 (from terms_pass)
    let v1 = eval_comp(cs_fst(csa_term1()), n);
    let v2 = eval_comp(cs_fst(csa_term2()), n);
    assert(v1 == 1 && v2 == 1);
    lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), n);
    lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), n);
    //  valid = 1 * (1 * 1) = 1
    assert(eval_comp(valid_cs, n) == 1nat);
    lemma_eval_pair(valid_cs, cs_snd(csa_term2()), n);
    lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), n);

    //  Full result: pair(rest, pair(1, cs_snd(csa_term2()) eval))
    let state = eval_comp(cs_snd(csa_term2()), n);
    assert(eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), n)
        == pair(rest, pair(1nat, state)));
    assert(eval_comp(check_subst_atomic_terms(), n) == pair(rest, pair(1nat, state)));
}

///  Atomic In: same as Eq but with tag 1 dispatch.
#[verifier::rlimit(800)]
pub proof fn lemma_subst_atomic_in_result(
    i: nat, left: Term, right: Term, var: nat, t: Term,
    rest: nat, valid: nat, t_enc_val: nat, t_set_val: nat,
    phi_enc: nat, result_enc: nat,
)
    requires
        valid > 0,
        t_set_val == 0 || t_enc_val == encode_term(t),
    ensures ({
        let f = Formula::In { left, right };
        let entry = pair(encode(f), encode(subst(f, var, t)));
        let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
        let s = pair(phi_enc, pair(result_enc, var));
        let n = pair(i, pair(acc, s));
        //  Exact result
        eval_comp(check_subst_step(), n) == pair(rest, pair(1nat,
            eval_comp(cs_snd(csa_term2()), n)))
    }),
{
    let f = Formula::In { left, right };
    let entry = pair(encode(f), encode(subst(f, var, t)));
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    let s = pair(phi_enc, pair(result_enc, var));
    let n = pair(i, pair(acc, s));

    crate::compspec_subst_step_helpers2::lemma_subst_in_terms_pass(
        i, left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);

    let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
    assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));

    assert(eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), n) == 1nat) by {
        crate::compspec_subst_extract::extract_atomic_in_values(
            i, left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), n);
    }

    assert(eval_comp(check_subst_atomic_terms(), n)
        == eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), n));

    let v1 = eval_comp(cs_fst(csa_term1()), n);
    let v2 = eval_comp(cs_fst(csa_term2()), n);
    assert(v1 == 1 && v2 == 1);
    lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), n);
    lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), n);
    assert(eval_comp(valid_cs, n) == 1nat);
    lemma_eval_pair(valid_cs, cs_snd(csa_term2()), n);
    lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), n);

    let state = eval_comp(cs_snd(csa_term2()), n);
    assert(eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), n)
        == pair(rest, pair(1nat, state)));
    assert(eval_comp(check_subst_atomic_terms(), n) == pair(rest, pair(1nat, state)));
}

} // verus!
