use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::br_acc;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_term_eval::lemma_subst_one_term_valid;
use crate::compspec_subst_extract::extract_atomic_eq_values;

verus! {

///  Part 1: Dispatch + term checks → both terms pass.
pub proof fn lemma_subst_eq_terms_pass(
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
        eval_comp(check_subst_step(), n) == eval_comp(check_subst_atomic_terms(), n) &&
        eval_comp(cs_fst(csa_term1()), n) != 0 &&
        eval_comp(cs_fst(csa_term2()), n) != 0 &&
        eval_comp(csa_rest(), n) == rest
    }),
{
    let f = Formula::Eq { left, right };
    let entry = pair(encode(f), encode(subst(f, var, t)));
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    let s = pair(phi_enc, pair(result_enc, var));
    let n = pair(0nat, pair(acc, s));
    let t_val = encode_term(t);

    assert(eval_comp(check_subst_step(), n) == eval_comp(check_subst_atomic_terms(), n)) by {
        lemma_subst_step_dispatch(0nat, entry + 1, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc, var);
        lemma_encode_is_pair(f);
        lemma_encode_is_pair(subst(f, var, t));
        lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
        lemma_unpair1_pair(0nat, pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t))));
        extract_atomic_eq_values(left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);
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
            }, n);
    }

    extract_atomic_eq_values(left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);
    match left { Term::Var { index } => {} }
    match right { Term::Var { index } => {} }

    lemma_subst_one_term_valid(
        cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node())),
        csa_var(), csa_t_enc(), csa_t_set(), n,
        encode_term(left), encode_term(subst_term(left, var, t)), var,
        t_enc_val, t_set_val, t_val);

    lemma_subst_one_term_valid(
        cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node())),
        csa_var(), cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())), n,
        encode_term(right), encode_term(subst_term(right, var, t)), var,
        eval_comp(cs_fst(cs_snd(csa_term1())), n),
        eval_comp(cs_snd(cs_snd(csa_term1())), n), t_val);
}

} // verus!
