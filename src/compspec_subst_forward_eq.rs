use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::br_acc;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_helpers::*;

verus! {

//  ====================================================================
//  Forward Eq constraints: split into focused helpers per rlimit tips.
//
//  1. extract_general — sub-expression eval values
//  2. lemma_forward_dispatch_eq — step → atomic_terms dispatch
//  3. lemma_forward_v1 — left term check value
//  4. lemma_forward_te1_ts1 — left term state output
//  5. lemma_forward_v2 — right term check value
//  6. lemma_forward_eq_constraints — combine to derive constraints
//  ====================================================================

///  Extract sub-expression eval values for a GENERAL entry.
#[verifier::rlimit(500)]
proof fn extract_general(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, te: nat, ts: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    ensures ({
        let entry = pair(phi_node, result_node);
        let acc = pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
        let orig = pair(phi_enc, pair(result_enc, var));
        let n = pair(i, pair(acc, orig));
        eval_comp(csa_entry(), n) == entry &&
        eval_comp(csa_phi_node(), n) == phi_node &&
        eval_comp(csa_result_node(), n) == result_node &&
        eval_comp(cs_fst(csa_phi_node()), n) == unpair1(phi_node) &&
        eval_comp(cs_fst(cs_snd(csa_phi_node())), n) == unpair1(unpair2(phi_node)) &&
        eval_comp(cs_snd(cs_snd(csa_phi_node())), n) == unpair2(unpair2(phi_node)) &&
        eval_comp(cs_fst(csa_result_node()), n) == unpair1(result_node) &&
        eval_comp(cs_fst(cs_snd(csa_result_node())), n) == unpair1(unpair2(result_node)) &&
        eval_comp(cs_snd(cs_snd(csa_result_node())), n) == unpair2(unpair2(result_node)) &&
        eval_comp(csa_var(), n) == var &&
        eval_comp(csa_t_enc(), n) == te &&
        eval_comp(csa_t_set(), n) == ts &&
        eval_comp(csa_rest(), n) == rest
    }),
{
    let entry = pair(phi_node, result_node);
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let n = pair(i, pair(acc, orig));

    lemma_eval_br_acc(i, acc, orig);
    lemma_eval_fst(br_acc(), n);
    lemma_unpair1_pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
    lemma_eval_fst(cs_fst(br_acc()), n);
    lemma_unpair1_pair(entry + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), n);
    lemma_unpair2_pair(entry + 1, rest);
    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
    lemma_eval_pred(entry + 1);
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    lemma_eval_fst(entry_cs, n);
    lemma_unpair1_pair(phi_node, result_node);
    lemma_eval_snd(entry_cs, n);
    lemma_unpair2_pair(phi_node, result_node);
    let pn = cs_fst(entry_cs);
    let rn = cs_snd(entry_cs);
    lemma_eval_fst(pn, n);
    lemma_eval_snd(pn, n);
    lemma_pair_surjective(phi_node);
    lemma_eval_fst(cs_snd(pn), n);
    lemma_eval_snd(cs_snd(pn), n);
    lemma_pair_surjective(unpair2(phi_node));
    lemma_eval_fst(rn, n);
    lemma_eval_snd(rn, n);
    lemma_pair_surjective(result_node);
    lemma_eval_fst(cs_snd(rn), n);
    lemma_eval_snd(cs_snd(rn), n);
    lemma_pair_surjective(unpair2(result_node));
    lemma_eval_snd(CompSpec::Id, n);
    lemma_unpair2_pair(i, pair(acc, orig));
    lemma_eval_snd(cs_snd(CompSpec::Id), n);
    lemma_unpair2_pair(acc, orig);
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), n);
    lemma_unpair2_pair(phi_enc, pair(result_enc, var));
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), n);
    lemma_unpair2_pair(result_enc, var);
    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
    lemma_eval_snd(cs_snd(br_acc()), n);
    lemma_unpair2_pair(valid, pair(te, ts));
    lemma_eval_fst(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair1_pair(te, ts);
    lemma_eval_snd(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair2_pair(te, ts);
}

///  Dispatch: for Eq (phi_tag == 0), step dispatches to atomic_terms.
#[verifier::rlimit(500)]
proof fn lemma_forward_dispatch_eq(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    te: nat, ts: nat, phi_enc: nat, result_enc: nat, var: nat,
)
    requires unpair1(phi_node) == 0,
    ensures ({
        let entry = pair(phi_node, result_node);
        let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
        let orig = pair(phi_enc, pair(result_enc, var));
        let n = pair(i, pair(acc, orig));
        eval_comp(check_subst_step(), n) == eval_comp(check_subst_atomic_terms(), n)
    }),
{
    let entry = pair(phi_node, result_node);
    let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let n = pair(i, pair(acc, orig));
    lemma_subst_step_dispatch(i, entry + 1, rest, 1, te, ts, phi_enc, result_enc, var);
    extract_general(i, phi_node, result_node, rest, 1, te, ts, phi_enc, result_enc, var);
    let phi_tag_cs = cs_fst(csa_phi_node());
    assert(eval_comp(phi_tag_cs, n) == 0nat);
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

///  v1: evaluate left term check. Returns the v1 value.
#[verifier::rlimit(500)]
proof fn lemma_forward_v1(
    n: nat, a: nat, ra: nat, var: nat,
)
    requires
        eval_comp(cs_fst(cs_snd(csa_phi_node())), n) == a,
        eval_comp(cs_fst(cs_snd(csa_result_node())), n) == ra,
        eval_comp(csa_var(), n) == var,
        eval_comp(csa_t_set(), n) == 0nat,
    ensures
        eval_comp(cs_fst(csa_term1()), n) ==
            (if a == var { 1nat } else { if a == ra { 1nat } else { 0nat } }),
{
    let eq_pv = cs_eq(cs_fst(cs_snd(csa_phi_node())), csa_var());
    lemma_eval_eq(cs_fst(cs_snd(csa_phi_node())), csa_var(), n);
    if a == var {
        lemma_eval_ifzero_else(eq_pv,
            cs_pair(cs_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node()))),
                cs_pair(csa_t_enc(), csa_t_set())),
            CompSpec::IfZero {
                cond: Box::new(csa_t_set()),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(cs_fst(cs_snd(csa_result_node())), csa_t_enc()),
                    cs_pair(csa_t_enc(), csa_t_set()))),
            }, n);
        lemma_eval_ifzero_then(csa_t_set(),
            cs_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1))),
            cs_pair(cs_eq(cs_fst(cs_snd(csa_result_node())), csa_t_enc()),
                cs_pair(csa_t_enc(), csa_t_set())),
            n);
        lemma_eval_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1)), n);
        lemma_eval_fst(csa_term1(), n);
        lemma_eval_fst(cs_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1))), n);
    } else {
        lemma_eval_ifzero_then(eq_pv,
            cs_pair(cs_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node()))),
                cs_pair(csa_t_enc(), csa_t_set())),
            CompSpec::IfZero {
                cond: Box::new(csa_t_set()),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(cs_fst(cs_snd(csa_result_node())), csa_t_enc()),
                    cs_pair(csa_t_enc(), csa_t_set()))),
            }, n);
        lemma_eval_pair(cs_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node()))),
            cs_pair(csa_t_enc(), csa_t_set()), n);
        lemma_eval_fst(csa_term1(), n);
        lemma_eval_fst(cs_pair(cs_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node()))),
            cs_pair(csa_t_enc(), csa_t_set())), n);
        lemma_eval_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node())), n);
    }
}

///  te1, ts1: left term state output.
#[verifier::rlimit(500)]
proof fn lemma_forward_te1_ts1(
    n: nat, a: nat, ra: nat, var: nat,
)
    requires
        eval_comp(cs_fst(cs_snd(csa_phi_node())), n) == a,
        eval_comp(cs_fst(cs_snd(csa_result_node())), n) == ra,
        eval_comp(csa_var(), n) == var,
        eval_comp(csa_t_enc(), n) == 0nat,
        eval_comp(csa_t_set(), n) == 0nat,
    ensures
        eval_comp(cs_fst(cs_snd(csa_term1())), n) == (if a == var { ra } else { 0nat }),
        eval_comp(cs_snd(cs_snd(csa_term1())), n) == (if a == var { 1nat } else { 0nat }),
{
    //  Reuse v1 eval path to get the branch, then extract snd
    let eq_pv = cs_eq(cs_fst(cs_snd(csa_phi_node())), csa_var());
    lemma_eval_eq(cs_fst(cs_snd(csa_phi_node())), csa_var(), n);
    lemma_eval_snd(csa_term1(), n);
    lemma_eval_fst(cs_snd(csa_term1()), n);
    lemma_eval_snd(cs_snd(csa_term1()), n);
    if a == var {
        lemma_eval_ifzero_else(eq_pv,
            cs_pair(cs_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node()))),
                cs_pair(csa_t_enc(), csa_t_set())),
            CompSpec::IfZero {
                cond: Box::new(csa_t_set()),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(cs_fst(cs_snd(csa_result_node())), csa_t_enc()),
                    cs_pair(csa_t_enc(), csa_t_set()))),
            }, n);
        lemma_eval_ifzero_then(csa_t_set(),
            cs_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1))),
            cs_pair(cs_eq(cs_fst(cs_snd(csa_result_node())), csa_t_enc()),
                cs_pair(csa_t_enc(), csa_t_set())),
            n);
        lemma_eval_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1)), n);
        lemma_eval_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1), n);
        lemma_unpair1_pair(ra, 1nat);
        lemma_unpair2_pair(ra, 1nat);
    } else {
        lemma_eval_ifzero_then(eq_pv,
            cs_pair(cs_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node()))),
                cs_pair(csa_t_enc(), csa_t_set())),
            CompSpec::IfZero {
                cond: Box::new(csa_t_set()),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(cs_fst(cs_snd(csa_result_node())), cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(cs_fst(cs_snd(csa_result_node())), csa_t_enc()),
                    cs_pair(csa_t_enc(), csa_t_set()))),
            }, n);
        lemma_eval_pair(cs_eq(cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node()))),
            cs_pair(csa_t_enc(), csa_t_set()), n);
        lemma_eval_pair(csa_t_enc(), csa_t_set(), n);
        lemma_unpair1_pair(0nat, 0nat);
        lemma_unpair2_pair(0nat, 0nat);
    }
}

///  v2: evaluate right term check. Returns the v2 value.
#[verifier::rlimit(500)]
proof fn lemma_forward_v2(
    n: nat, b: nat, rb: nat, var: nat, te1: nat, ts1: nat,
)
    requires
        eval_comp(cs_snd(cs_snd(csa_phi_node())), n) == b,
        eval_comp(cs_snd(cs_snd(csa_result_node())), n) == rb,
        eval_comp(csa_var(), n) == var,
        eval_comp(cs_fst(cs_snd(csa_term1())), n) == te1,
        eval_comp(cs_snd(cs_snd(csa_term1())), n) == ts1,
    ensures
        eval_comp(cs_fst(csa_term2()), n) == (if b == var {
            if ts1 == 0 { 1nat } else { if rb == te1 { 1nat } else { 0nat } }
        } else {
            if b == rb { 1nat } else { 0nat }
        }),
{
    let eq_pv2 = cs_eq(cs_snd(cs_snd(csa_phi_node())), csa_var());
    lemma_eval_eq(cs_snd(cs_snd(csa_phi_node())), csa_var(), n);
    if b == var {
        lemma_eval_ifzero_else(eq_pv2,
            cs_pair(cs_eq(cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node()))),
                cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())))),
            CompSpec::IfZero {
                cond: Box::new(cs_snd(cs_snd(csa_term1()))),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(cs_snd(cs_snd(csa_result_node())), cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(cs_snd(cs_snd(csa_result_node())), cs_fst(cs_snd(csa_term1()))),
                    cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1()))))),
            }, n);
        if ts1 == 0 {
            lemma_eval_ifzero_then(cs_snd(cs_snd(csa_term1())),
                cs_pair(cs_const(1), cs_pair(cs_snd(cs_snd(csa_result_node())), cs_const(1))),
                cs_pair(cs_eq(cs_snd(cs_snd(csa_result_node())), cs_fst(cs_snd(csa_term1()))),
                    cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())))),
                n);
            lemma_eval_pair(cs_const(1), cs_pair(cs_snd(cs_snd(csa_result_node())), cs_const(1)), n);
            lemma_eval_fst(csa_term2(), n);
            lemma_eval_fst(cs_pair(cs_const(1), cs_pair(cs_snd(cs_snd(csa_result_node())), cs_const(1))), n);
        } else {
            lemma_eval_ifzero_else(cs_snd(cs_snd(csa_term1())),
                cs_pair(cs_const(1), cs_pair(cs_snd(cs_snd(csa_result_node())), cs_const(1))),
                cs_pair(cs_eq(cs_snd(cs_snd(csa_result_node())), cs_fst(cs_snd(csa_term1()))),
                    cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())))),
                n);
            lemma_eval_pair(cs_eq(cs_snd(cs_snd(csa_result_node())), cs_fst(cs_snd(csa_term1()))),
                cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1()))), n);
            lemma_eval_fst(csa_term2(), n);
            lemma_eval_fst(cs_pair(cs_eq(cs_snd(cs_snd(csa_result_node())), cs_fst(cs_snd(csa_term1()))),
                cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())))), n);
            lemma_eval_eq(cs_snd(cs_snd(csa_result_node())), cs_fst(cs_snd(csa_term1())), n);
        }
    } else {
        lemma_eval_ifzero_then(eq_pv2,
            cs_pair(cs_eq(cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node()))),
                cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())))),
            CompSpec::IfZero {
                cond: Box::new(cs_snd(cs_snd(csa_term1()))),
                then_br: Box::new(cs_pair(cs_const(1), cs_pair(cs_snd(cs_snd(csa_result_node())), cs_const(1)))),
                else_br: Box::new(cs_pair(cs_eq(cs_snd(cs_snd(csa_result_node())), cs_fst(cs_snd(csa_term1()))),
                    cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1()))))),
            }, n);
        lemma_eval_pair(cs_eq(cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node()))),
            cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1()))), n);
        lemma_eval_fst(csa_term2(), n);
        lemma_eval_fst(cs_pair(cs_eq(cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node()))),
            cs_pair(cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())))), n);
        lemma_eval_eq(cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node())), n);
    }
}

///  Main: combine dispatch + term evals + empty-stack stability → constraints.
#[verifier::rlimit(1200)]
pub proof fn lemma_forward_eq_constraints(
    a: nat, b: nat, ra: nat, rb: nat, var: nat,
    phi_enc: nat, result_enc: nat,
)
    requires
        phi_enc == pair(0nat, pair(a, b)),
        result_enc == pair(0nat, pair(ra, rb)),
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        (a != var ==> ra == a),
        (b != var ==> rb == b),
        (a == var && b == var ==> rb == ra),
{
    let input = pair(phi_enc, pair(result_enc, var));
    lemma_check_subst_unfold(phi_enc, result_enc, var);
    let entry = pair(phi_enc, result_enc);
    let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));

    //  One iterate step
    lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);
    let si = pair(phi_enc as nat, pair(base, input));

    //  Dispatch → atomic_terms
    lemma_unpair1_pair(0nat, pair(a, b));
    lemma_forward_dispatch_eq(phi_enc, phi_enc, result_enc, 0nat, 0nat, 0nat,
        phi_enc, result_enc, var);

    //  Extract values
    extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
        phi_enc, result_enc, var);
    lemma_unpair2_pair(0nat, pair(a, b));
    lemma_unpair1_pair(a, b);
    lemma_unpair2_pair(a, b);
    lemma_unpair1_pair(0nat, pair(ra, rb));
    lemma_unpair2_pair(0nat, pair(ra, rb));
    lemma_unpair1_pair(ra, rb);
    lemma_unpair2_pair(ra, rb);

    //  Tag check
    let tag_eq = eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si);
    assert(tag_eq == 1nat) by {
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
    }

    //  v1, te1, ts1
    lemma_forward_v1(si, a, ra, var);
    let v1 = eval_comp(cs_fst(csa_term1()), si);
    lemma_forward_te1_ts1(si, a, ra, var);
    let te1 = eval_comp(cs_fst(cs_snd(csa_term1())), si);
    let ts1 = eval_comp(cs_snd(cs_snd(csa_term1())), si);

    //  v2
    lemma_forward_v2(si, b, rb, var, te1, ts1);
    let v2 = eval_comp(cs_fst(csa_term2()), si);

    //  Full valid = 1 * (v1 * v2)
    let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
    assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));
    lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
    lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
    let full_valid = eval_comp(valid_cs, si);
    assert(full_valid == 1nat * (v1 * v2));

    //  Eval result form
    assert(eval_comp(check_subst_atomic_terms(), si)
        == eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), si));
    lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
    lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
    let state = eval_comp(cs_snd(csa_term2()), si);
    let step_result = eval_comp(check_subst_step(), si);
    assert(step_result == pair(0nat, pair(full_valid, state)));

    //  Empty-stack stability → full_valid != 0
    assert(full_valid != 0nat) by {
        lemma_pair_surjective(state);
        lemma_subst_empty_stable(phi_enc, full_valid,
            unpair1(state), unpair2(state), phi_enc, result_enc, var);
        lemma_unpair2_pair(0nat, pair(full_valid, state));
        lemma_unpair1_pair(full_valid, state);
    }

    //  Factor: v1 != 0 AND v2 != 0
    assert(v1 != 0nat && v2 != 0nat) by {
        if v1 == 0 { assert(1nat * (0nat * v2) == 0nat) by (nonlinear_arith); }
        if v2 == 0 { assert(1nat * (v1 * 0nat) == 0nat) by (nonlinear_arith); }
    }

    //  Derive constraints from v1 != 0
    if a != var { assert(ra == a); }
    if b != var { assert(rb == b); }
    if a == var && b == var {
        assert(ts1 == 1nat);
        assert(te1 == ra);
        assert(rb == ra);
    }
}

} // verus!
