use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_free_var_helpers::*;

verus! {

///  Key helper: chain one step of compspec_iterate.
pub proof fn lemma_csi_step_chain(
    fuel: nat, old_acc: nat, new_acc: nat, f_enc: nat, v: nat,
)
    requires
        fuel > 0,
        eval_comp(has_free_var_step(),
            pair((fuel - 1) as nat, pair(old_acc, pair(f_enc, v)))) == new_acc,
    ensures
        compspec_iterate(has_free_var_step(), fuel, old_acc, pair(f_enc, v))
            == compspec_iterate(has_free_var_step(), (fuel - 1) as nat, new_acc, pair(f_enc, v)),
{
    lemma_compspec_iterate_unfold(has_free_var_step(), fuel, old_acc, pair(f_enc, v));
}

///  When found==0 and stack is empty, compspec_iterate stays at pair(0, 0).
pub proof fn lemma_csi_empty_stable(
    fuel: nat, f_enc: nat, v: nat,
)
    ensures
        compspec_iterate(has_free_var_step(), fuel, pair(0nat, 0nat), pair(f_enc, v))
            == pair(0nat, 0nat),
    decreases fuel,
{
    if fuel > 0 {
        lemma_step_empty_stack((fuel - 1) as nat, f_enc, v);
        lemma_csi_step_chain(fuel, pair(0nat, 0nat), pair(0nat, 0nat), f_enc, v);
        lemma_csi_empty_stable((fuel - 1) as nat, f_enc, v);
    }
}

///  Main structural induction: traversal returns found=0 for non-free variables.
///  Uses traversal_cost(f, v) instead of formula_size(f) for accurate fuel accounting.
pub proof fn lemma_traversal_no_free_var(
    f: Formula, v: nat, rest: nat, f_enc: nat, fuel: nat,
)
    requires
        !has_free_var(f, v),
        fuel >= traversal_cost(f, v),
    ensures
        compspec_iterate(has_free_var_step(), fuel,
            pair(pair(encode(f) + 1, rest), 0nat), pair(f_enc, v))
        == compspec_iterate(has_free_var_step(), (fuel - traversal_cost(f, v)) as nat,
            pair(rest, 0nat), pair(f_enc, v)),
    decreases f,
{
    let step = has_free_var_step();
    let enc = encode(f);
    let old_acc = pair(pair(enc + 1, rest), 0nat);
    let input = pair(f_enc, v);
    assert(fuel > 0) by { lemma_traversal_cost_pos(f, v); }

    match f {
        Formula::Eq { left, right } => {
            lemma_has_free_var_atomic(left, right, v);
            lemma_encode_is_pair(f);
            lemma_step_eq(encode_term(left), encode_term(right), v,
                rest, f_enc, (fuel - 1) as nat);
            lemma_csi_step_chain(fuel, old_acc, pair(rest, 0nat), f_enc, v);
            //  traversal_cost = 1, done
        },
        Formula::In { left, right } => {
            lemma_has_free_var_atomic(left, right, v);
            lemma_encode_is_pair(f);
            lemma_step_in(encode_term(left), encode_term(right), v,
                rest, f_enc, (fuel - 1) as nat);
            lemma_csi_step_chain(fuel, old_acc, pair(rest, 0nat), f_enc, v);
        },
        Formula::Not { sub } => {
            lemma_has_free_var_not(*sub, v);
            lemma_encode_is_pair(f);
            let new_acc = pair(pair(encode(*sub) + 1, rest), 0nat);
            lemma_step_not(encode(*sub), v, rest, f_enc, (fuel - 1) as nat);
            lemma_csi_step_chain(fuel, old_acc, new_acc, f_enc, v);
            //  traversal_cost(Not(sub), v) = 1 + traversal_cost(sub, v)
            lemma_traversal_no_free_var(*sub, v, rest, f_enc, (fuel - 1) as nat);
        },
        Formula::And { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            let new_acc = pair(pair(encode(*left) + 1,
                pair(encode(*right) + 1, rest)), 0nat);
            lemma_step_binary(3, encode(*left), encode(*right), v,
                rest, f_enc, (fuel - 1) as nat);
            lemma_csi_step_chain(fuel, old_acc, new_acc, f_enc, v);
            lemma_traversal_no_free_var(*left, v,
                pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            lemma_traversal_no_free_var(*right, v,
                rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
        },
        Formula::Or { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            let new_acc = pair(pair(encode(*left) + 1,
                pair(encode(*right) + 1, rest)), 0nat);
            lemma_step_binary(4, encode(*left), encode(*right), v,
                rest, f_enc, (fuel - 1) as nat);
            lemma_csi_step_chain(fuel, old_acc, new_acc, f_enc, v);
            lemma_traversal_no_free_var(*left, v,
                pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            lemma_traversal_no_free_var(*right, v,
                rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
        },
        Formula::Implies { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            let new_acc = pair(pair(encode(*left) + 1,
                pair(encode(*right) + 1, rest)), 0nat);
            lemma_step_binary(5, encode(*left), encode(*right), v,
                rest, f_enc, (fuel - 1) as nat);
            lemma_csi_step_chain(fuel, old_acc, new_acc, f_enc, v);
            lemma_traversal_no_free_var(*left, v,
                pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            lemma_traversal_no_free_var(*right, v,
                rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
        },
        Formula::Iff { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            let new_acc = pair(pair(encode(*left) + 1,
                pair(encode(*right) + 1, rest)), 0nat);
            lemma_step_binary(6, encode(*left), encode(*right), v,
                rest, f_enc, (fuel - 1) as nat);
            lemma_csi_step_chain(fuel, old_acc, new_acc, f_enc, v);
            lemma_traversal_no_free_var(*left, v,
                pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            lemma_traversal_no_free_var(*right, v,
                rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
        },
        Formula::Forall { var, sub } => {
            lemma_has_free_var_quantifier(var, *sub, v);
            lemma_encode_is_pair(f);
            if var == v {
                //  traversal_cost(Forall(v, sub), v) = 1 — skip sub
                lemma_step_quantifier_bound(7, var, encode(*sub), v,
                    rest, f_enc, (fuel - 1) as nat);
                lemma_csi_step_chain(fuel, old_acc, pair(rest, 0nat), f_enc, v);
            } else {
                //  traversal_cost(Forall(var, sub), v) = 1 + traversal_cost(sub, v)
                let new_acc = pair(pair(encode(*sub) + 1, rest), 0nat);
                lemma_step_quantifier_free(7, var, encode(*sub), v,
                    rest, f_enc, (fuel - 1) as nat);
                lemma_csi_step_chain(fuel, old_acc, new_acc, f_enc, v);
                lemma_traversal_no_free_var(*sub, v, rest, f_enc, (fuel - 1) as nat);
            }
        },
        Formula::Exists { var, sub } => {
            lemma_has_free_var_quantifier(var, *sub, v);
            lemma_encode_is_pair(f);
            if var == v {
                lemma_step_quantifier_bound(8, var, encode(*sub), v,
                    rest, f_enc, (fuel - 1) as nat);
                lemma_csi_step_chain(fuel, old_acc, pair(rest, 0nat), f_enc, v);
            } else {
                let new_acc = pair(pair(encode(*sub) + 1, rest), 0nat);
                lemma_step_quantifier_free(8, var, encode(*sub), v,
                    rest, f_enc, (fuel - 1) as nat);
                lemma_csi_step_chain(fuel, old_acc, new_acc, f_enc, v);
                lemma_traversal_no_free_var(*sub, v, rest, f_enc, (fuel - 1) as nat);
            }
        },
    }
}

///  Simpler version: found flag stays 0 for any fuel when formula doesn't have v free.
///  Uses the same step lemmas but only tracks unpair2(result) == 0.
pub proof fn lemma_hfv_found_zero(
    f: Formula, v: nat, f_enc: nat, fuel: nat,
)
    requires
        !has_free_var(f, v),
        fuel >= traversal_cost(f, v),
    ensures
        unpair2(compspec_iterate(has_free_var_step(), fuel,
            pair(pair(encode(f) + 1, 0nat), 0nat), pair(f_enc, v))) == 0nat,
{
    lemma_traversal_no_free_var(f, v, 0nat, f_enc, fuel);
    //  compspec_iterate(step, fuel, acc, input)
    //    == compspec_iterate(step, fuel - cost, pair(0, 0), input)
    lemma_csi_empty_stable((fuel - traversal_cost(f, v)) as nat, f_enc, v);
    //  = pair(0, 0)
    lemma_unpair2_pair(0nat, 0nat);
}

///  Unfolding helper: delegates to compspec_hfv_unfold.
///  Fuel is f_enc + 1 (ensures at least 1 step).
pub proof fn lemma_hfv_unfold(f_enc: nat, v: nat)
    ensures ({
        let input = pair(f_enc, v);
        let base_val = pair(pair(f_enc + 1, 0nat), 0nat);
        eval_comp(has_free_var_comp(), input)
            == unpair2(compspec_iterate(has_free_var_step(), (f_enc + 1) as nat, base_val, input))
    }),
{
    crate::compspec_hfv_unfold::lemma_hfv_comp_eval(f_enc, v);
}

///  Top-level: has_free_var_comp() returns 0 for sentences.
pub proof fn lemma_has_free_var_sentence_core(f: Formula, v: nat)
    requires
        is_sentence(f),
    ensures
        eval_comp(has_free_var_comp(), pair(encode(f), v)) == 0,
{
    let f_enc = encode(f);
    lemma_sentence_no_free_var(f, v);
    lemma_hfv_unfold(f_enc, v);
    lemma_sentence_encode_ge_cost(f, v);
    //  fuel = f_enc + 1 >= f_enc >= traversal_cost
    lemma_hfv_found_zero(f, v, f_enc, (f_enc + 1) as nat);
}

///  General: has_free_var_comp() returns 0 when var is not free in formula.
///  Works for non-sentences too (e.g., vacuous quantification).
pub proof fn lemma_has_free_var_general(f: Formula, v: nat)
    requires
        !has_free_var(f, v),
    ensures
        eval_comp(has_free_var_comp(), pair(encode(f), v)) == 0,
{
    let f_enc = encode(f);
    lemma_hfv_unfold(f_enc, v);
    //  fuel = f_enc + 1 always >= traversal_cost(f, v) >= 1
    if f_enc > 0 {
        lemma_encode_ge_cost_inner(f, v);
    }
    lemma_hfv_found_zero(f, v, f_enc, (f_enc + 1) as nat);
}

} //  verus!
