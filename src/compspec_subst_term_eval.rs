use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

//  ====================================================================
//  Per-term eval: evaluate check_subst_one_term for valid substitution.
//  Isolated in own file for rlimit management (per rlimit tips).
//  ====================================================================

///  For a valid substitution term: check_subst_one_term produces v=1
///  and maintains the t_enc invariant.
///
///  This evaluates the IfZero chain in check_subst_one_term:
///  - If phi_term == var: discover (t_set=0) or verify (t_set=1) t_enc
///  - If phi_term != var: verify result_term == phi_term
///
///  For valid substitutions, all checks pass → v = 1.
#[verifier::rlimit(500)]
pub proof fn lemma_subst_one_term_valid(
    phi_term_cs: CompSpec, result_term_cs: CompSpec,
    var_cs: CompSpec, t_enc_cs: CompSpec, t_set_cs: CompSpec,
    input: nat,
    phi_term_val: nat, result_term_val: nat, var_val: nat,
    t_enc_val: nat, t_set_val: nat, t_val: nat,
)
    requires
        //  Sub-expression eval values
        eval_comp(phi_term_cs, input) == phi_term_val,
        eval_comp(result_term_cs, input) == result_term_val,
        eval_comp(var_cs, input) == var_val,
        eval_comp(t_enc_cs, input) == t_enc_val,
        eval_comp(t_set_cs, input) == t_set_val,
        //  Term compatibility (from valid substitution)
        (phi_term_val == var_val ==> result_term_val == t_val),
        (phi_term_val != var_val ==> result_term_val == phi_term_val),
        //  t_enc invariant
        t_set_val == 0 || t_enc_val == t_val,
    ensures ({
        let term_check = check_subst_one_term(phi_term_cs, result_term_cs, var_cs, t_enc_cs, t_set_cs);
        //  v exactly 1 (for valid substitutions, all checks produce 1)
        eval_comp(cs_fst(term_check), input) == 1 &&
        //  t_enc invariant maintained
        (eval_comp(cs_snd(cs_snd(term_check)), input) == 0 ||
         eval_comp(cs_fst(cs_snd(term_check)), input) == t_val) &&
        //  Exact output state (for traversal chaining)
        eval_comp(cs_fst(cs_snd(term_check)), input) ==
            (if phi_term_val == var_val { if t_set_val == 0 { t_val } else { t_enc_val } } else { t_enc_val }) &&
        eval_comp(cs_snd(cs_snd(term_check)), input) ==
            (if phi_term_val == var_val { if t_set_val == 0 { 1nat } else { t_set_val } } else { t_set_val })
    }),
{
    let term_check = check_subst_one_term(phi_term_cs, result_term_cs, var_cs, t_enc_cs, t_set_cs);
    let eq_phi_var = cs_eq(phi_term_cs, var_cs);
    lemma_eval_eq(phi_term_cs, var_cs, input);

    if phi_term_val == var_val {
        //  phi_term == var → else branch of outer IfZero
        lemma_eval_ifzero_else(eq_phi_var,
            cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)),
            CompSpec::IfZero {
                cond: Box::new(t_set_cs),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs))),
            }, input);

        if t_set_val == 0 {
            //  First occurrence: discover t
            lemma_eval_ifzero_then(t_set_cs,
                cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))),
                cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)),
                input);
            //  result = pair(1, pair(result_term, 1))
            lemma_eval_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1)), input);
            lemma_eval_pair(result_term_cs, cs_const(1), input);
            lemma_eval_fst(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))), input);
            lemma_eval_snd(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))), input);
            lemma_eval_fst(cs_pair(result_term_cs, cs_const(1)), input);
            lemma_eval_snd(cs_pair(result_term_cs, cs_const(1)), input);
            //  Bridge to ensures: fst/snd of term_check
            lemma_eval_fst(term_check, input);
            lemma_eval_snd(term_check, input);
            lemma_eval_fst(cs_snd(term_check), input);
            lemma_eval_snd(cs_snd(term_check), input);
            lemma_unpair1_pair(1nat, pair(result_term_val, 1nat));
            lemma_unpair2_pair(1nat, pair(result_term_val, 1nat));
            lemma_unpair1_pair(result_term_val, 1nat);
            lemma_unpair2_pair(result_term_val, 1nat);
        } else {
            //  Subsequent: verify consistency
            lemma_eval_ifzero_else(t_set_cs,
                cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1))),
                cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)),
                input);
            //  result = pair(eq(result_term, t_enc), pair(t_enc, t_set))
            lemma_eval_eq(result_term_cs, t_enc_cs, input);
            lemma_eval_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs), input);
            lemma_eval_pair(t_enc_cs, t_set_cs, input);
            lemma_eval_fst(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)), input);
            lemma_eval_snd(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs)), input);
            lemma_eval_fst(cs_pair(t_enc_cs, t_set_cs), input);
            lemma_eval_snd(cs_pair(t_enc_cs, t_set_cs), input);
            //  Bridge to ensures
            lemma_eval_fst(term_check, input);
            lemma_eval_snd(term_check, input);
            lemma_eval_fst(cs_snd(term_check), input);
            lemma_eval_snd(cs_snd(term_check), input);
            let v = if result_term_val == t_enc_val { 1nat } else { 0nat };
            lemma_unpair1_pair(v, pair(t_enc_val, t_set_val));
            lemma_unpair2_pair(v, pair(t_enc_val, t_set_val));
            lemma_unpair1_pair(t_enc_val, t_set_val);
            lemma_unpair2_pair(t_enc_val, t_set_val);
        }
    } else {
        //  phi_term != var → then branch
        lemma_eval_ifzero_then(eq_phi_var,
            cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)),
            CompSpec::IfZero {
                cond: Box::new(t_set_cs),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(result_term_cs, cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(result_term_cs, t_enc_cs), cs_pair(t_enc_cs, t_set_cs))),
            }, input);
        //  result = pair(eq(phi_term, result_term), pair(t_enc, t_set))
        lemma_eval_eq(phi_term_cs, result_term_cs, input);
        lemma_eval_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs), input);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_fst(cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)), input);
        lemma_eval_snd(cs_pair(cs_eq(phi_term_cs, result_term_cs), cs_pair(t_enc_cs, t_set_cs)), input);
        lemma_eval_fst(cs_pair(t_enc_cs, t_set_cs), input);
        lemma_eval_snd(cs_pair(t_enc_cs, t_set_cs), input);
        //  Bridge to ensures
        lemma_eval_fst(term_check, input);
        lemma_eval_snd(term_check, input);
        lemma_eval_fst(cs_snd(term_check), input);
        lemma_eval_snd(cs_snd(term_check), input);
        let v = if result_term_val == phi_term_val { 1nat } else { 0nat };
        lemma_unpair1_pair(v, pair(t_enc_val, t_set_val));
        lemma_unpair2_pair(v, pair(t_enc_val, t_set_val));
        lemma_unpair1_pair(t_enc_val, t_set_val);
        lemma_unpair2_pair(t_enc_val, t_set_val);
    }
}

} // verus!
