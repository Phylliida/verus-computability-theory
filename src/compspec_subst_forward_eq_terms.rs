use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_term_eval::lemma_subst_one_term_eval_general;

verus! {

///  Evaluate v1, te1, ts1, v2 for Eq forward case.
///  Isolated in own file for rlimit (per rlimit tips: module splitting).
#[verifier::rlimit(800)]
pub proof fn lemma_forward_eq_term_evals(
    si: nat, a: nat, b: nat, ra: nat, rb: nat, var: nat,
    phi_enc: nat, result_enc: nat,
)
    requires
        phi_enc == pair(0nat, pair(a, b)),
        result_enc == pair(0nat, pair(ra, rb)),
        ({
            let entry = pair(phi_enc, result_enc);
            let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));
            let input = pair(phi_enc, pair(result_enc, var));
            si == pair(phi_enc as nat, pair(base, input))
        }),
    ensures
        eval_comp(cs_fst(csa_term1()), si) ==
            (if a == var { 1nat } else { if a == ra { 1nat } else { 0nat } }),
        eval_comp(cs_fst(cs_snd(csa_term1())), si) == (if a == var { ra } else { 0nat }),
        eval_comp(cs_snd(cs_snd(csa_term1())), si) == (if a == var { 1nat } else { 0nat }),
        eval_comp(cs_fst(csa_term2()), si) == ({
            let te1: nat = if a == var { ra } else { 0nat };
            let ts1: nat = if a == var { 1nat } else { 0nat };
            if b == var {
                if ts1 == 0 { 1nat } else { if rb == te1 { 1nat } else { 0nat } }
            } else { if b == rb { 1nat } else { 0nat } }
        }),
{
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

    //  Term 1 (left)
    lemma_subst_one_term_eval_general(
        cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node())),
        csa_var(), csa_t_enc(), csa_t_set(), si,
        a, ra, var, 0nat, 0nat);

    let te1 = eval_comp(cs_fst(cs_snd(csa_term1())), si);
    let ts1 = eval_comp(cs_snd(cs_snd(csa_term1())), si);

    //  Term 2 (right)
    lemma_subst_one_term_eval_general(
        cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node())),
        csa_var(), cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())), si,
        b, rb, var, te1, ts1);
}

} // verus!
