use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

///  v1: evaluate left term check for forward Eq case.
///  Isolated in own file for rlimit (per rlimit tips: module splitting).
#[verifier::rlimit(500)]
pub proof fn lemma_forward_v1(
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
pub proof fn lemma_forward_te1_ts1(
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

} // verus!
