use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

///  v2: evaluate right term check for forward Eq case.
///  Isolated in own file for rlimit (per rlimit tips: module splitting).
#[verifier::rlimit(500)]
pub proof fn lemma_forward_v2(
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

} // verus!
