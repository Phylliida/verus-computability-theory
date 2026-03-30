use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_free_var_helpers::*;

verus! {

///  Key structural property: subst preserves formula tags in the encoding.
pub proof fn lemma_subst_preserves_tag(f: Formula, var: nat, t: Term)
    ensures unpair1(encode(f)) == unpair1(encode(subst(f, var, t))),
    decreases f,
{
    match f {
        Formula::Eq { left, right } => {
            lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(0nat, pair(encode_term(subst_term(left, var, t)),
                encode_term(subst_term(right, var, t))));
        },
        Formula::In { left, right } => {
            lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(1nat, pair(encode_term(subst_term(left, var, t)),
                encode_term(subst_term(right, var, t))));
        },
        Formula::Not { sub } => {
            lemma_unpair1_pair(2nat, encode(*sub));
            lemma_unpair1_pair(2nat, encode(subst(*sub, var, t)));
        },
        Formula::And { left, right } => {
            lemma_unpair1_pair(3nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(3nat, pair(encode(subst(*left, var, t)),
                encode(subst(*right, var, t))));
        },
        Formula::Or { left, right } => {
            lemma_unpair1_pair(4nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(4nat, pair(encode(subst(*left, var, t)),
                encode(subst(*right, var, t))));
        },
        Formula::Implies { left, right } => {
            lemma_unpair1_pair(5nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(5nat, pair(encode(subst(*left, var, t)),
                encode(subst(*right, var, t))));
        },
        Formula::Iff { left, right } => {
            lemma_unpair1_pair(6nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(6nat, pair(encode(subst(*left, var, t)),
                encode(subst(*right, var, t))));
        },
        Formula::Forall { var: v, sub } => {
            lemma_unpair1_pair(7nat, pair(v, encode(*sub)));
            if v == var {} else {
                lemma_unpair1_pair(7nat, pair(v, encode(subst(*sub, var, t))));
            }
        },
        Formula::Exists { var: v, sub } => {
            lemma_unpair1_pair(8nat, pair(v, encode(*sub)));
            if v == var {} else {
                lemma_unpair1_pair(8nat, pair(v, encode(subst(*sub, var, t))));
            }
        },
    }
}

///  When phi_enc == 0: check_subst_comp returns 1 (0 iterations, base valid=1).
pub proof fn lemma_check_subst_comp_zero_fuel(result_enc: nat, var: nat)
    ensures
        eval_comp(check_subst_comp(), pair(0nat, pair(result_enc, var))) != 0,
{
    let input = pair(0nat, pair(result_enc, var));
    let phi = cs_fst(CompSpec::Id);
    let result = cs_fst(cs_snd(CompSpec::Id));

    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(0nat, pair(result_enc, var));
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(0nat, pair(result_enc, var));
    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_unpair1_pair(result_enc, var);
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_unpair2_pair(result_enc, var);

    lemma_eval_pair(phi, result, input);
    lemma_eval_add(cs_pair(phi, result), cs_const(1), input);
    lemma_eval_pair(
        CompSpec::Add { left: Box::new(cs_pair(phi, result)), right: Box::new(cs_const(1)) },
        cs_const(0), input);
    lemma_eval_pair(cs_const(0), cs_const(0), input);
    lemma_eval_pair(cs_const(1), cs_pair(cs_const(0), cs_const(0)), input);
    let stack_expr = cs_pair(
        CompSpec::Add { left: Box::new(cs_pair(phi, result)), right: Box::new(cs_const(1)) },
        cs_const(0));
    let valid_expr = cs_pair(cs_const(1), cs_pair(cs_const(0), cs_const(0)));
    lemma_eval_pair(stack_expr, valid_expr, input);
    let base_expr = cs_pair(stack_expr, valid_expr);

    lemma_eval_bounded_rec(phi, base_expr, check_subst_step(), input);

    let base_val = eval_comp(base_expr, input);
    let stack_val = eval_comp(stack_expr, input);
    let valid_part = pair(1nat, pair(0nat, 0nat));

    lemma_eval_comp(cs_fst(cs_snd(CompSpec::Id)),
        CompSpec::BoundedRec {
            count_fn: Box::new(phi),
            base: Box::new(base_expr),
            step: Box::new(check_subst_step()),
        }, input);

    lemma_eval_snd(CompSpec::Id, base_val);
    lemma_unpair2_pair(stack_val, valid_part);
    lemma_eval_fst(cs_snd(CompSpec::Id), base_val);
    lemma_unpair1_pair(1nat, pair(0nat, 0nat));
}

///  Backward: check_subst_comp returns nonzero for valid substitutions.
pub proof fn lemma_check_subst_comp_backward(phi: Formula, var: nat, t: Term)
    ensures
        eval_comp(check_subst_comp(),
            pair(encode(phi), pair(encode(subst(phi, var, t)), var))) != 0,
    decreases phi,
{
    let phi_enc = encode(phi);
    let result_enc = encode(subst(phi, var, t));
    if phi_enc == 0 {
        lemma_check_subst_comp_zero_fuel(result_enc, var);
    } else {
        //  phi_enc > 0: need full traversal proof
        //  For now, observe that the BoundedRec with count=phi_enc processes
        //  the formula tree. Since subst preserves tags at every level,
        //  all tag checks pass and valid stays 1.
        //
        //  The full proof requires per-step evaluation lemmas (analogous to
        //  compspec_free_var_helpers). This is the most labor-intensive part
        //  of the ASSUME #3 removal.
        //
        //  Key structural argument by formula variant:
        lemma_subst_preserves_tag(phi, var, t);
        match phi {
            Formula::Forall { var: v, sub } => {
                if v == var {
                    //  subst returns phi unchanged: encode(phi) == encode(result)
                    //  So the pair (phi_enc, result_enc) has identical entries
                    //  The checker sees phi_enc == result_enc at every node
                    //  This means valid stays 1
                    //  We can use zero-fuel on the result directly since
                    //  result == phi and both have encoding phi_enc
                    //  But check_subst_comp input is pair(phi_enc, pair(phi_enc, var))
                    //  with count=phi_enc > 0, so it runs iterations.
                    //  When phi_node == result_node at every step, all checks pass.
                    //  TODO: formalize this
                    lemma_check_subst_comp_zero_fuel(result_enc, var);
                    //  FIXME: wrong - this proves for phi_enc=0, not phi_enc>0
                } else {
                    lemma_check_subst_comp_backward(*sub, var, t);
                    //  FIXME: recursive result is about sub, not phi
                    lemma_check_subst_comp_zero_fuel(result_enc, var);
                }
            },
            _ => {
                lemma_check_subst_comp_zero_fuel(result_enc, var);
                //  FIXME: wrong for phi_enc > 0
            },
        }
    }
}

} //  verus!
