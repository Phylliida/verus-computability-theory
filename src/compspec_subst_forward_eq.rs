use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_eq_terms::lemma_forward_eq_term_evals;
use crate::compspec_subst_forward_eq_valid::lemma_forward_eq_valid_nonzero;

verus! {

///  Forward Eq constraints: valid != 0 → term constraints.
///  All heavy work delegated to isolated helpers.
#[verifier::rlimit(800)]
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
    let entry = pair(phi_enc, result_enc);
    let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
    let si = pair(phi_enc as nat, pair(base, input));

    //  Unfold + one step
    lemma_check_subst_unfold(phi_enc, result_enc, var);
    lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);

    //  Dispatch → atomic_terms (scoped)
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

    //  Term evals (isolated helper)
    lemma_forward_eq_term_evals(si, a, b, ra, rb, var, phi_enc, result_enc);
    let v1 = eval_comp(cs_fst(csa_term1()), si);
    let te1 = eval_comp(cs_fst(cs_snd(csa_term1())), si);
    let ts1 = eval_comp(cs_snd(cs_snd(csa_term1())), si);
    let v2 = eval_comp(cs_fst(csa_term2()), si);

    //  Tag match (scoped)
    assert(eval_comp(cs_fst(csa_phi_node()), si) == eval_comp(cs_fst(csa_result_node()), si)) by {
        extract_general(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        lemma_unpair1_pair(0nat, pair(a, b));
        lemma_unpair1_pair(0nat, pair(ra, rb));
    }

    //  Valid nonzero (isolated helper)
    lemma_forward_eq_valid_nonzero(si, v1, v2, phi_enc, result_enc, var);
    //  Now: 1 * (v1 * v2) != 0

    //  Factor: v1 != 0 AND v2 != 0
    assert(v1 != 0nat && v2 != 0nat) by {
        if v1 == 0 { assert(1nat * (0nat * v2) == 0nat) by (nonlinear_arith); }
        if v2 == 0 { assert(1nat * (v1 * 0nat) == 0nat) by (nonlinear_arith); }
    }

    //  Derive constraints from v1 != 0, v2 != 0
    if a != var { assert(ra == a); }
    if b != var { assert(rb == b); }
    if a == var && b == var {
        assert(ts1 == 1nat);
        assert(te1 == ra);
        assert(rb == ra);
    }
}

} // verus!
