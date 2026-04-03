use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_term_eval::lemma_subst_one_term_eval_general;

verus! {

///  Forward Eq constraints: valid != 0 → term constraints.
///  Uses general per-term eval (isolated in own file) + extract (isolated in own file).
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

    //  Unfold to iterate (fuel = phi_enc + 1)
    lemma_check_subst_unfold(phi_enc, result_enc, var);
    let entry = pair(phi_enc, result_enc);
    let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));

    //  One iterate step
    lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);
    let si = pair(phi_enc as nat, pair(base, input));

    //  Dispatch: step → process_pair → atomic_terms
    assert(eval_comp(check_subst_step(), si) == eval_comp(check_subst_atomic_terms(), si)) by {
        lemma_subst_step_dispatch(phi_enc, entry + 1, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        lemma_unpair1_pair(0nat, pair(a, b));
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
            }, si);
    }

    //  Extract sub-expression values
    extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
        phi_enc, result_enc, var);
    lemma_unpair1_pair(0nat, pair(a, b));
    lemma_unpair2_pair(0nat, pair(a, b));
    lemma_unpair1_pair(a, b);
    lemma_unpair2_pair(a, b);
    lemma_unpair1_pair(0nat, pair(ra, rb));
    lemma_unpair2_pair(0nat, pair(ra, rb));
    lemma_unpair1_pair(ra, rb);
    lemma_unpair2_pair(ra, rb);

    //  Per-term eval: term1 (left)
    lemma_subst_one_term_eval_general(
        cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node())),
        csa_var(), csa_t_enc(), csa_t_set(), si,
        a, ra, var, 0nat, 0nat);
    //  Now know: v1, te1, ts1 as if-else expressions

    let v1 = eval_comp(cs_fst(csa_term1()), si);
    let te1 = eval_comp(cs_fst(cs_snd(csa_term1())), si);
    let ts1 = eval_comp(cs_snd(cs_snd(csa_term1())), si);

    //  Per-term eval: term2 (right) — uses te1, ts1 from term1
    lemma_subst_one_term_eval_general(
        cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node())),
        csa_var(), cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())), si,
        b, rb, var, te1, ts1);

    let v2 = eval_comp(cs_fst(csa_term2()), si);

    //  Tag check: both tags are 0
    let tag_eq = eval_comp(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())), si);
    assert(tag_eq == 1nat) by {
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
    }

    //  Full valid = tag_eq * (v1 * v2)
    let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
    assert(check_subst_atomic_terms() == cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))));
    lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
    lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
        cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
    let full_valid = eval_comp(valid_cs, si);
    assert(full_valid == 1nat * (v1 * v2));

    //  Step result form
    lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
    lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
    assert(eval_comp(check_subst_atomic_terms(), si)
        == eval_comp(cs_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2()))), si));
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

    //  Derive constraints
    if a != var { assert(ra == a); }
    if b != var { assert(rb == b); }
    if a == var && b == var {
        assert(ts1 == 1nat);
        assert(te1 == ra);
        assert(rb == ra);
    }
}

} // verus!
