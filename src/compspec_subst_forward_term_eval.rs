use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

///  General per-term eval: evaluate check_subst_one_term for ANY input.
///  Like backward lemma_subst_one_term_valid but WITHOUT correctness requirements.
///  Isolated in own file for rlimit (per rlimit tips: module splitting).
#[verifier::rlimit(500)]
pub proof fn lemma_subst_one_term_eval_general(
    phi_term_cs: CompSpec, result_term_cs: CompSpec,
    var_cs: CompSpec, t_enc_cs: CompSpec, t_set_cs: CompSpec,
    input: nat,
    phi_val: nat, result_val: nat, var_val: nat,
    t_enc_val: nat, t_set_val: nat,
)
    requires
        eval_comp(phi_term_cs, input) == phi_val,
        eval_comp(result_term_cs, input) == result_val,
        eval_comp(var_cs, input) == var_val,
        eval_comp(t_enc_cs, input) == t_enc_val,
        eval_comp(t_set_cs, input) == t_set_val,
    ensures ({
        let tc = check_subst_one_term(phi_term_cs, result_term_cs, var_cs, t_enc_cs, t_set_cs);
        eval_comp(cs_fst(tc), input) == (if phi_val == var_val {
            if t_set_val == 0 { 1nat }
            else { if result_val == t_enc_val { 1nat } else { 0nat } }
        } else {
            if phi_val == result_val { 1nat } else { 0nat }
        }) &&
        eval_comp(cs_fst(cs_snd(tc)), input) == (if phi_val == var_val {
            if t_set_val == 0 { result_val } else { t_enc_val }
        } else { t_enc_val }) &&
        eval_comp(cs_snd(cs_snd(tc)), input) == (if phi_val == var_val {
            if t_set_val == 0 { 1nat } else { t_set_val }
        } else { t_set_val })
    }),
{
    let tc = check_subst_one_term(phi_term_cs, result_term_cs, var_cs, t_enc_cs, t_set_cs);
    let eq_phi_var = cs_eq(phi_term_cs, var_cs);
    lemma_eval_eq(phi_term_cs, var_cs, input);

    if phi_val == var_val {
        lemma_eval_ifzero_else(eq_phi_var,
            cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)),
            CompSpec::IfZero {
                cond: Box::new(t_set_cs),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs))),
            }, input);

        if t_set_val == 0 {
            lemma_eval_ifzero_then(t_set_cs,
                cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))),
                cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)),
                input);
            lemma_eval_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1)), input);
            lemma_eval_pair(result_term_cs, cs_const(1), input);
            //  Intermediate fst/snd on the pair expressions
            lemma_eval_fst(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))), input);
            lemma_eval_snd(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))), input);
            lemma_eval_fst(cs_pair(result_term_cs, cs_const(1)), input);
            lemma_eval_snd(cs_pair(result_term_cs, cs_const(1)), input);
            //  Bridge to tc
            lemma_eval_fst(tc, input);
            lemma_eval_snd(tc, input);
            lemma_eval_fst(cs_snd(tc), input);
            lemma_eval_snd(cs_snd(tc), input);
            lemma_unpair1_pair(1nat, pair(result_val, 1nat));
            lemma_unpair2_pair(1nat, pair(result_val, 1nat));
            lemma_unpair1_pair(result_val, 1nat);
            lemma_unpair2_pair(result_val, 1nat);
        } else {
            lemma_eval_ifzero_else(t_set_cs,
                cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))),
                cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)),
                input);
            lemma_eval_eq(result_term_cs, t_enc_cs, input);
            lemma_eval_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs), input);
            lemma_eval_pair(t_enc_cs, t_set_cs, input);
            lemma_eval_fst(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)), input);
            lemma_eval_snd(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)), input);
            lemma_eval_fst(cs_pair(t_enc_cs, t_set_cs), input);
            lemma_eval_snd(cs_pair(t_enc_cs, t_set_cs), input);
            //  Bridge to tc
            lemma_eval_fst(tc, input);
            lemma_eval_snd(tc, input);
            lemma_eval_fst(cs_snd(tc), input);
            lemma_eval_snd(cs_snd(tc), input);
            let v = if result_val == t_enc_val { 1nat } else { 0nat };
            lemma_unpair1_pair(v, pair(t_enc_val, t_set_val));
            lemma_unpair2_pair(v, pair(t_enc_val, t_set_val));
            lemma_unpair1_pair(t_enc_val, t_set_val);
            lemma_unpair2_pair(t_enc_val, t_set_val);
        }
    } else {
        lemma_eval_ifzero_then(eq_phi_var,
            cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)),
            CompSpec::IfZero {
                cond: Box::new(t_set_cs),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs))),
            }, input);
        lemma_eval_eq(phi_term_cs, result_term_cs, input);
        lemma_eval_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs), input);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_fst(cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)), input);
        lemma_eval_snd(cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)), input);
        lemma_eval_fst(cs_pair(t_enc_cs, t_set_cs), input);
        lemma_eval_snd(cs_pair(t_enc_cs, t_set_cs), input);
        //  Bridge to tc
        lemma_eval_fst(tc, input);
        lemma_eval_snd(tc, input);
        lemma_eval_fst(cs_snd(tc), input);
        lemma_eval_snd(cs_snd(tc), input);
        let v = if phi_val == result_val { 1nat } else { 0nat };
        lemma_unpair1_pair(v, pair(t_enc_val, t_set_val));
        lemma_unpair2_pair(v, pair(t_enc_val, t_set_val));
        lemma_unpair1_pair(t_enc_val, t_set_val);
        lemma_unpair2_pair(t_enc_val, t_set_val);
    }
}

} // verus!
