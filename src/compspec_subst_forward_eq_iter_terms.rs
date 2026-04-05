use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_term_eval::lemma_subst_one_term_eval_general;

verus! {

///  Evaluate v1, te1, ts1 for FIRST term at iterate level with general (te, ts).
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_term1_iter(
    si: nat,
    a: nat, ra: nat, var: nat, te: nat, ts: nat,
)
    requires
        eval_comp(cs_fst(cs_snd(csa_phi_node())), si) == a,
        eval_comp(cs_fst(cs_snd(csa_result_node())), si) == ra,
        eval_comp(csa_var(), si) == var,
        eval_comp(csa_t_enc(), si) == te,
        eval_comp(csa_t_set(), si) == ts,
    ensures
        eval_comp(cs_fst(csa_term1()), si) == (if a == var {
            if ts == 0 { 1nat } else { if ra == te { 1nat } else { 0nat } }
        } else { if a == ra { 1nat } else { 0nat } }),
        eval_comp(cs_fst(cs_snd(csa_term1())), si) == (if a == var {
            if ts == 0 { ra } else { te }
        } else { te }),
        eval_comp(cs_snd(cs_snd(csa_term1())), si) ==
            (if a == var { if ts == 0 { 1nat } else { ts } } else { ts }),
{
    lemma_subst_one_term_eval_general(
        cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node())),
        csa_var(), csa_t_enc(), csa_t_set(), si,
        a, ra, var, te, ts);
}

///  Evaluate v2 for SECOND term at iterate level, given te1/ts1 from first term.
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_term2_iter(
    si: nat,
    b: nat, rb: nat, var: nat, te1: nat, ts1: nat,
)
    requires
        eval_comp(cs_snd(cs_snd(csa_phi_node())), si) == b,
        eval_comp(cs_snd(cs_snd(csa_result_node())), si) == rb,
        eval_comp(csa_var(), si) == var,
        eval_comp(cs_fst(cs_snd(csa_term1())), si) == te1,
        eval_comp(cs_snd(cs_snd(csa_term1())), si) == ts1,
    ensures
        eval_comp(cs_fst(csa_term2()), si) == (if b == var {
            if ts1 == 0 { 1nat } else { if rb == te1 { 1nat } else { 0nat } }
        } else { if b == rb { 1nat } else { 0nat } }),
{
    lemma_subst_one_term_eval_general(
        cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node())),
        csa_var(), cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())), si,
        b, rb, var, te1, ts1);
}

} // verus!
