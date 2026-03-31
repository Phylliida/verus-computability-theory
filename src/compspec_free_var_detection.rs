use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::br_acc;
use crate::compspec_free_var_helpers::*;
use crate::compspec_free_var_induction::*;
use crate::compspec_hfv_unfold::*;

verus! {

//  ====================================================================
//  Detection direction: has_free_var(f, v) → has_free_var_comp(encode(f), v) != 0
//  ====================================================================

//  Step helper: Eq with var found — reuse existing lemma_step_eq's infrastructure.
//  The existing lemma_step_eq requires left_idx != v && right_idx != v (no free var).
//  For detection, at least one equals v, so the result's found field is nonzero.
//  Atomic step helpers (Eq/In detection) are in compspec_free_var_detection2.rs
//  (module isolation per rlimit tips — sibling body pollution).
use crate::compspec_free_var_detection2::lemma_step_eq_found;
use crate::compspec_free_var_detection2::lemma_step_in_found;

//  Iterate stability: when found != 0, iterate preserves found.
proof fn lemma_csi_found_stable(fuel: nat, stack: nat, found: nat, f_enc: nat, v: nat)
    requires found != 0,
    ensures compspec_iterate(has_free_var_step(), fuel, pair(stack, found), pair(f_enc, v))
        == pair(stack, found),
    decreases fuel,
{
    if fuel > 0 {
        lemma_step_found_nonzero((fuel - 1) as nat, stack, found, f_enc, v);
        lemma_csi_step_chain(fuel, pair(stack, found), pair(stack, found), f_enc, v);
        lemma_csi_found_stable((fuel - 1) as nat, stack, found, f_enc, v);
    }
}

//  Cost function for detection traversal.
pub open spec fn detection_cost(f: Formula, v: nat) -> nat
    decreases f,
{
    match f {
        Formula::Eq { .. } => 1,
        Formula::In { .. } => 1,
        Formula::Not { sub } => 1 + detection_cost(*sub, v),
        Formula::And { left, right } =>
            if has_free_var(*left, v) { 1 + detection_cost(*left, v) }
            else { 1 + traversal_cost(*left, v) + detection_cost(*right, v) },
        Formula::Or { left, right } =>
            if has_free_var(*left, v) { 1 + detection_cost(*left, v) }
            else { 1 + traversal_cost(*left, v) + detection_cost(*right, v) },
        Formula::Implies { left, right } =>
            if has_free_var(*left, v) { 1 + detection_cost(*left, v) }
            else { 1 + traversal_cost(*left, v) + detection_cost(*right, v) },
        Formula::Iff { left, right } =>
            if has_free_var(*left, v) { 1 + detection_cost(*left, v) }
            else { 1 + traversal_cost(*left, v) + detection_cost(*right, v) },
        Formula::Forall { var, sub } => 1 + detection_cost(*sub, v),
        Formula::Exists { var, sub } => 1 + detection_cost(*sub, v),
    }
}

proof fn lemma_detection_cost_le_size(f: Formula, v: nat)
    requires has_free_var(f, v),
    ensures detection_cost(f, v) <= formula_size(f),
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_detection_cost_le_size(*sub, v); },
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            if has_free_var(*left, v) {
                lemma_detection_cost_le_size(*left, v);
                lemma_formula_size_pos(*right);
            } else {
                lemma_traversal_cost_le_size(*left, v);
                lemma_detection_cost_le_size(*right, v);
            }
        },
        Formula::Forall { var, sub } => { lemma_detection_cost_le_size(*sub, v); },
        Formula::Exists { var, sub } => { lemma_detection_cost_le_size(*sub, v); },
    }
}

//  ====================================================================
//  Main detection walk: has_free_var(f, v) → iterate sets found.
//  ====================================================================

#[verifier::rlimit(300)]
pub proof fn lemma_hfv_walk_found(
    f: Formula, v: nat, rest: nat, f_enc: nat, fuel: nat,
)
    requires
        has_free_var(f, v),
        fuel >= detection_cost(f, v),
    ensures
        unpair2(compspec_iterate(has_free_var_step(), fuel,
            pair(pair(encode(f) + 1, rest), 0nat), pair(f_enc, v))) != 0,
    decreases f,
{
    let enc = encode(f);
    let acc = pair(pair(enc + 1, rest), 0nat);
    let s = pair(f_enc, v);
    lemma_encode_is_pair(f);

    match f {
        Formula::Eq { left, right } => {
            match (left, right) {
                (Term::Var { index: li }, Term::Var { index: ri }) => {
                    lemma_step_eq_found(li, ri, v, rest, f_enc, (fuel - 1) as nat);
                    lemma_csi_step_chain(fuel, acc,
                        eval_comp(has_free_var_step(), pair((fuel-1) as nat, pair(acc, s))), f_enc, v);
                    let result = eval_comp(has_free_var_step(), pair((fuel-1) as nat, pair(acc, s)));
                    let found = unpair2(result);
                    lemma_pair_surjective(result);
                    lemma_csi_found_stable((fuel - 1) as nat, unpair1(result), found, f_enc, v);
                },
            }
        },
        Formula::In { left, right } => {
            match (left, right) {
                (Term::Var { index: li }, Term::Var { index: ri }) => {
                    lemma_step_in_found(li, ri, v, rest, f_enc, (fuel - 1) as nat);
                    lemma_csi_step_chain(fuel, acc,
                        eval_comp(has_free_var_step(), pair((fuel-1) as nat, pair(acc, s))), f_enc, v);
                    let result = eval_comp(has_free_var_step(), pair((fuel-1) as nat, pair(acc, s)));
                    let found = unpair2(result);
                    lemma_pair_surjective(result);
                    lemma_csi_found_stable((fuel - 1) as nat, unpair1(result), found, f_enc, v);
                },
            }
        },
        Formula::Not { sub } => {
            lemma_step_not(encode(*sub), v, rest, f_enc, (fuel - 1) as nat);
            let new_acc = pair(pair(encode(*sub) + 1, rest), 0nat);
            lemma_csi_step_chain(fuel, acc, new_acc, f_enc, v);
            lemma_hfv_walk_found(*sub, v, rest, f_enc, (fuel - 1) as nat);
        },
        Formula::And { left, right } => {
            lemma_step_binary(3, encode(*left), encode(*right), v, rest, f_enc, (fuel - 1) as nat);
            let new_acc = pair(pair(encode(*left) + 1, pair(encode(*right) + 1, rest)), 0nat);
            lemma_csi_step_chain(fuel, acc, new_acc, f_enc, v);
            if has_free_var(*left, v) {
                lemma_hfv_walk_found(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            } else {
                lemma_traversal_no_free_var(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
                lemma_hfv_walk_found(*right, v, rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
            }
        },
        Formula::Or { left, right } => {
            lemma_step_binary(4, encode(*left), encode(*right), v, rest, f_enc, (fuel - 1) as nat);
            let new_acc = pair(pair(encode(*left) + 1, pair(encode(*right) + 1, rest)), 0nat);
            lemma_csi_step_chain(fuel, acc, new_acc, f_enc, v);
            if has_free_var(*left, v) {
                lemma_hfv_walk_found(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            } else {
                lemma_traversal_no_free_var(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
                lemma_hfv_walk_found(*right, v, rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
            }
        },
        Formula::Implies { left, right } => {
            lemma_step_binary(5, encode(*left), encode(*right), v, rest, f_enc, (fuel - 1) as nat);
            let new_acc = pair(pair(encode(*left) + 1, pair(encode(*right) + 1, rest)), 0nat);
            lemma_csi_step_chain(fuel, acc, new_acc, f_enc, v);
            if has_free_var(*left, v) {
                lemma_hfv_walk_found(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            } else {
                lemma_traversal_no_free_var(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
                lemma_hfv_walk_found(*right, v, rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
            }
        },
        Formula::Iff { left, right } => {
            lemma_step_binary(6, encode(*left), encode(*right), v, rest, f_enc, (fuel - 1) as nat);
            let new_acc = pair(pair(encode(*left) + 1, pair(encode(*right) + 1, rest)), 0nat);
            lemma_csi_step_chain(fuel, acc, new_acc, f_enc, v);
            if has_free_var(*left, v) {
                lemma_hfv_walk_found(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
            } else {
                lemma_traversal_no_free_var(*left, v, pair(encode(*right) + 1, rest), f_enc, (fuel - 1) as nat);
                lemma_hfv_walk_found(*right, v, rest, f_enc, (fuel - 1 - traversal_cost(*left, v)) as nat);
            }
        },
        Formula::Forall { var, sub } => {
            //  has_free_var(Forall(var, sub), v) → var != v && has_free_var(sub, v)
            lemma_step_quantifier_free(7, var, encode(*sub), v, rest, f_enc, (fuel - 1) as nat);
            let new_acc = pair(pair(encode(*sub) + 1, rest), 0nat);
            lemma_csi_step_chain(fuel, acc, new_acc, f_enc, v);
            lemma_hfv_walk_found(*sub, v, rest, f_enc, (fuel - 1) as nat);
        },
        Formula::Exists { var, sub } => {
            lemma_step_quantifier_free(8, var, encode(*sub), v, rest, f_enc, (fuel - 1) as nat);
            let new_acc = pair(pair(encode(*sub) + 1, rest), 0nat);
            lemma_csi_step_chain(fuel, acc, new_acc, f_enc, v);
            lemma_hfv_walk_found(*sub, v, rest, f_enc, (fuel - 1) as nat);
        },
    }
}

//  ====================================================================
//  Wrapper: has_free_var(f, v) → has_free_var_comp(encode(f), v) != 0
//  No encode != 0 precondition needed thanks to f_enc+1 fuel fix.
//  ====================================================================

pub proof fn lemma_has_free_var_detection(f: Formula, v: nat)
    requires has_free_var(f, v),
    ensures eval_comp(has_free_var_comp(), pair(encode(f), v)) != 0,
{
    let f_enc = encode(f);
    lemma_hfv_comp_eval(f_enc, v);
    //  eval == unpair2(compspec_iterate(step, f_enc+1, base, input))
    //  fuel = f_enc + 1 >= detection_cost(f, v)
    if f_enc > 0 {
        lemma_encode_ge_formula_size(f);
    }
    lemma_detection_cost_le_size(f, v);
    //  detection_cost <= formula_size <= f_enc (when f_enc > 0), and detection_cost >= 1
    //  f_enc + 1 >= detection_cost always
    lemma_hfv_walk_found(f, v, 0nat, f_enc, (f_enc + 1) as nat);
}

//  ====================================================================
//  Full biconditional:
//  has_free_var_comp(encode(f), v) == 0 ↔ !has_free_var(f, v)
//  ====================================================================

///  Forward direction for vacuous_quant: comp returns 0 → variable is not free.
pub proof fn lemma_has_free_var_comp_sound(f: Formula, v: nat)
    requires
        eval_comp(has_free_var_comp(), pair(encode(f), v)) == 0,
    ensures !has_free_var(f, v),
{
    //  Contrapositive of detection: has_free_var → comp != 0.
    if has_free_var(f, v) {
        lemma_has_free_var_detection(f, v);
    }
}

} //  verus!
