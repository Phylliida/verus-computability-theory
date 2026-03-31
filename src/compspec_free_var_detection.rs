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
#[verifier::rlimit(800)]
proof fn lemma_step_eq_found(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires left_idx == v || right_idx == v,
    ensures ({
        let enc = pair(0nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        let result = eval_comp(has_free_var_step(), input);
        unpair2(result) != 0
    }),
{
    let enc = pair(0nat, pair(left_idx, right_idx));
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);
    //  eval(step, input) == eval(process_top, input)

    //  Provide key intermediate values for process_top evaluation:
    //  acc, stack, top_enc, tag, content, v
    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    lemma_eval_fst(cs_fst(br_acc()), input);
    lemma_unpair1_pair(enc + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), input);
    lemma_unpair2_pair(enc + 1, rest);
    //  top_enc = Pred(enc+1) = enc = pair(0, pair(left_idx, right_idx))
    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
    lemma_eval_pred(enc + 1);
    let top_enc_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    //  tag = fst(enc) = 0
    lemma_eval_fst(top_enc_cs, input);
    lemma_unpair1_pair(0nat, pair(left_idx, right_idx));
    //  content = snd(enc) = pair(left_idx, right_idx)
    lemma_eval_snd(top_enc_cs, input);
    lemma_unpair2_pair(0nat, pair(left_idx, right_idx));
    //  v
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, pair(f_enc, v)));
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_unpair2_pair(acc, pair(f_enc, v));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
    lemma_unpair2_pair(f_enc, v);
    //  term values
    let content_cs = cs_snd(top_enc_cs);
    let v_cs = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_fst(content_cs, input);
    lemma_unpair1_pair(left_idx, right_idx);
    lemma_eval_snd(content_cs, input);
    lemma_unpair2_pair(left_idx, right_idx);
    //  found = or(eq(left, v), eq(right, v))
    lemma_eval_eq(cs_fst(content_cs), v_cs, input);
    lemma_eval_eq(cs_snd(content_cs), v_cs, input);
    let eq_l = cs_eq(cs_fst(content_cs), v_cs);
    let eq_r = cs_eq(cs_snd(content_cs), v_cs);
    lemma_eval_add(eq_l, eq_r, input);
    //  result pair
    lemma_eval_pair(cs_snd(cs_fst(br_acc())), cs_or(eq_l, eq_r), input);
    lemma_unpair2_pair(rest, eval_comp(eq_l, input) + eval_comp(eq_r, input));
}

//  Step helper: In with var found.
#[verifier::rlimit(1500)]
proof fn lemma_step_in_found(
    left_idx: nat, right_idx: nat, v: nat,
    rest: nat, f_enc: nat, i: nat,
)
    requires left_idx == v || right_idx == v,
    ensures ({
        let enc = pair(1nat, pair(left_idx, right_idx));
        let stack = pair(enc + 1, rest);
        let acc = pair(stack, 0nat);
        let input = pair(i, pair(acc, pair(f_enc, v)));
        let result = eval_comp(has_free_var_step(), input);
        unpair2(result) != 0
    }),
{
    let enc = pair(1nat, pair(left_idx, right_idx));
    let stack = pair(enc + 1, rest);
    let acc = pair(stack, 0nat);
    let input = pair(i, pair(acc, pair(f_enc, v)));

    lemma_step_to_process_top(i, enc + 1, rest, f_enc, v);

    lemma_eval_br_acc(i, acc, pair(f_enc, v));
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, 0nat);
    lemma_eval_fst(cs_fst(br_acc()), input);
    lemma_unpair1_pair(enc + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), input);
    lemma_unpair2_pair(enc + 1, rest);
    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
    lemma_eval_pred(enc + 1);
    let top_enc_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    //  tag = 1
    lemma_eval_fst(top_enc_cs, input);
    lemma_unpair1_pair(1nat, pair(left_idx, right_idx));
    //  Pred(1) = 0 → In branch
    let tag_cs = cs_fst(top_enc_cs);
    lemma_eval_comp(CompSpec::Pred, tag_cs, input);
    lemma_eval_pred(1nat);
    //  content, v, terms, found
    lemma_eval_snd(top_enc_cs, input);
    lemma_unpair2_pair(1nat, pair(left_idx, right_idx));
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, pair(f_enc, v)));
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_unpair2_pair(acc, pair(f_enc, v));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
    lemma_unpair2_pair(f_enc, v);
    let content_cs = cs_snd(top_enc_cs);
    let v_cs = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    lemma_eval_fst(content_cs, input);
    lemma_unpair1_pair(left_idx, right_idx);
    lemma_eval_snd(content_cs, input);
    lemma_unpair2_pair(left_idx, right_idx);
    lemma_eval_eq(cs_fst(content_cs), v_cs, input);
    lemma_eval_eq(cs_snd(content_cs), v_cs, input);
    let eq_l = cs_eq(cs_fst(content_cs), v_cs);
    let eq_r = cs_eq(cs_snd(content_cs), v_cs);
    lemma_eval_add(eq_l, eq_r, input);
    lemma_eval_pair(cs_snd(cs_fst(br_acc())), cs_or(eq_l, eq_r), input);
    lemma_unpair2_pair(rest, eval_comp(eq_l, input) + eval_comp(eq_r, input));
}

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
//  (when encode(f) > 0)
//  ====================================================================

pub proof fn lemma_has_free_var_detection(f: Formula, v: nat)
    requires has_free_var(f, v), encode(f) != 0,
    ensures eval_comp(has_free_var_comp(), pair(encode(f), v)) != 0,
{
    let f_enc = encode(f);
    lemma_hfv_comp_eval(f_enc, v);
    //  eval_comp(has_free_var_comp(), pair(f_enc, v))
    //  == unpair2(compspec_iterate(step, f_enc, pair(pair(f_enc+1, 0), 0), pair(f_enc, v)))

    lemma_encode_ge_formula_size(f);
    lemma_detection_cost_le_size(f, v);
    lemma_hfv_walk_found(f, v, 0nat, f_enc, f_enc);
}

//  ====================================================================
//  Full biconditional (for encode(f) > 0):
//  has_free_var_comp(encode(f), v) == 0 ↔ !has_free_var(f, v)
//  ====================================================================

///  Forward direction for vacuous_quant: comp returns 0 → variable is not free.
pub proof fn lemma_has_free_var_comp_sound(f: Formula, v: nat)
    requires
        encode(f) != 0,
        eval_comp(has_free_var_comp(), pair(encode(f), v)) == 0,
    ensures !has_free_var(f, v),
{
    //  Contrapositive of detection: has_free_var → comp != 0.
    //  So comp == 0 → !has_free_var.
    if has_free_var(f, v) {
        lemma_has_free_var_detection(f, v);
        //  comp != 0, contradicts requires
    }
}

} //  verus!
