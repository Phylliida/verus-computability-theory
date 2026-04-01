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

///  One step on Eq formula: valid stays nonzero for valid substitution.
#[verifier::rlimit(800)]
pub proof fn lemma_subst_atomic_eq_valid(
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
        let result = eval_comp(check_subst_step(), n);
        unpair1(result) == rest && unpair1(unpair2(result)) != 0
    }),
{
    let f = Formula::Eq { left, right };
    let entry = pair(encode(f), encode(subst(f, var, t)));
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    let s = pair(phi_enc, pair(result_enc, var));
    let n = pair(0nat, pair(acc, s));
    let t_val = encode_term(t);

    //  Dispatch: step → process_pair → atomic_terms (scoped)
    assert(eval_comp(check_subst_step(), n) == eval_comp(check_subst_atomic_terms(), n)) by {
        lemma_subst_step_dispatch(0nat, entry + 1, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc, var);
        lemma_encode_is_pair(f);
        lemma_encode_is_pair(subst(f, var, t));
        lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
        lemma_unpair1_pair(0nat, pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t))));
        extract_atomic_eq_values(left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);
        let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
        let phi_tag_cs = cs_fst(cs_fst(entry_cs));
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
    //  Ambient: step == atomic_terms

    //  Extract values
    extract_atomic_eq_values(left, right, var, t, rest, valid, t_enc_val, t_set_val, phi_enc, result_enc);
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    let pn = cs_fst(entry_cs);
    let rn = cs_snd(entry_cs);
    let var_cs = cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))));
    let te_cs = cs_fst(cs_snd(cs_snd(br_acc())));
    let ts_cs = cs_snd(cs_snd(cs_snd(br_acc())));

    //  Term checks
    match left { Term::Var { index } => {} }
    match right { Term::Var { index } => {} }

    let pt1 = cs_fst(cs_snd(pn));
    let rt1 = cs_fst(cs_snd(rn));
    lemma_subst_one_term_valid(pt1, rt1, var_cs, te_cs, ts_cs, n,
        encode_term(left), encode_term(subst_term(left, var, t)), var,
        t_enc_val, t_set_val, t_val);

    let term1 = check_subst_one_term(pt1, rt1, var_cs, te_cs, ts_cs);

    let pt2 = cs_snd(cs_snd(pn));
    let rt2 = cs_snd(cs_snd(rn));
    lemma_subst_one_term_valid(pt2, rt2, var_cs, cs_fst(cs_snd(term1)), cs_snd(cs_snd(term1)), n,
        encode_term(right), encode_term(subst_term(right, var, t)), var,
        eval_comp(cs_fst(cs_snd(term1)), n), eval_comp(cs_snd(cs_snd(term1)), n), t_val);

    let term2 = check_subst_one_term(pt2, rt2, var_cs, cs_fst(cs_snd(term1)), cs_snd(cs_snd(term1)));
    let v1 = eval_comp(cs_fst(term1), n);
    let v2 = eval_comp(cs_fst(term2), n);

    //  Compose
    lemma_eval_eq(cs_fst(pn), cs_fst(rn), n);
    lemma_eval_cs_and(cs_fst(term1), cs_fst(term2), n);
    lemma_eval_cs_and(cs_eq(cs_fst(pn), cs_fst(rn)), cs_and(cs_fst(term1), cs_fst(term2)), n);
    let valid_cs = cs_and(cs_eq(cs_fst(pn), cs_fst(rn)), cs_and(cs_fst(term1), cs_fst(term2)));
    lemma_eval_pair(valid_cs, cs_snd(term2), n);
    lemma_eval_pair(cs_snd(cs_fst(br_acc())), cs_pair(valid_cs, cs_snd(term2)), n);
    assert(1nat * (v1 * v2) != 0) by (nonlinear_arith) requires v1 != 0, v2 != 0;
    lemma_unpair1_pair(rest, eval_comp(cs_pair(valid_cs, cs_snd(term2)), n));
    lemma_unpair1_pair(1nat * (v1 * v2), eval_comp(cs_snd(term2), n));
}

} // verus!
