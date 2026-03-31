use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_forward_structure::*;
use crate::compspec_forward_structure2::*;
use crate::proof_system::*;

verus! {

//  Per-constructor decode bridge lemmas (one-level unfold only)
proof fn decode_implies(enc: nat)
    requires unpair1(enc) == 5,
    ensures decode_formula(enc) == mk_implies(
        decode_formula(unpair1(unpair2(enc))), decode_formula(unpair2(unpair2(enc)))),
{
    reveal(decode_formula);
    lemma_pair_surjective(enc);
}

proof fn decode_iff(enc: nat)
    requires unpair1(enc) == 6,
    ensures decode_formula(enc) == mk_iff(
        decode_formula(unpair1(unpair2(enc))), decode_formula(unpair2(unpair2(enc)))),
{
    reveal(decode_formula);
    lemma_pair_surjective(enc);
}

//  Complex forward checker proofs — isolated from simple proofs to avoid sibling pollution

pub proof fn lemma_check_iff_elim_left_forward(enc: nat)
    requires eval_comp(check_axiom_iff_elim_left(), enc) != 0,
    ensures is_axiom_iff_elim_left(decode_formula(enc)),
{
    iff_elim_left_structure(enc);
    //  enc = pair(5, pair(iff_enc, impl_enc)) where iff tag=6, impl tag=5, same content
    let iff_enc = unpair1(unpair2(enc));
    let impl_enc = unpair2(unpair2(enc));
    lemma_pair_surjective(unpair2(iff_enc));
    let phi = decode_formula(unpair1(unpair2(iff_enc)));
    let psi = decode_formula(unpair2(unpair2(iff_enc)));
    //  Decode outer Implies, inner Iff and Implies using bridge lemmas
    decode_implies(enc);
    decode_iff(iff_enc);
    decode_implies(impl_enc);
}

pub proof fn lemma_check_iff_elim_right_forward(enc: nat)
    requires eval_comp(check_axiom_iff_elim_right(), enc) != 0,
    ensures is_axiom_iff_elim_right(decode_formula(enc)),
{
    iff_elim_right_structure(enc);
    let iff_enc = unpair1(unpair2(enc));
    let impl_enc = unpair2(unpair2(enc));
    lemma_pair_surjective(unpair2(iff_enc));
    lemma_pair_surjective(unpair2(impl_enc));
    let phi = decode_formula(unpair1(unpair2(iff_enc)));
    let psi = decode_formula(unpair2(unpair2(iff_enc)));
    decode_implies(enc);
    decode_iff(iff_enc);
    decode_implies(impl_enc);
}

proof fn decode_forall(enc: nat)
    requires unpair1(enc) == 7,
    ensures decode_formula(enc) == mk_forall(
        unpair1(unpair2(enc)), decode_formula(unpair2(unpair2(enc)))),
{
    reveal(decode_formula);
    lemma_pair_surjective(enc);
}

pub proof fn lemma_check_hyp_syl_forward(enc: nat)
    requires eval_comp(check_axiom_hyp_syllogism(), enc) != 0,
    ensures is_axiom_hyp_syllogism(decode_formula(enc)),
{
    hide(decode_formula);
    crate::compspec_forward_structure3::hyp_syl_structure(enc);
    let l_enc = unpair1(unpair2(enc));
    let r_enc = unpair2(unpair2(enc));
    let m_enc = unpair1(unpair2(r_enc));
    let n_enc = unpair2(unpair2(r_enc));
    lemma_pair_surjective(unpair2(l_enc));
    lemma_pair_surjective(unpair2(m_enc));
    lemma_pair_surjective(unpair2(n_enc));
    let phi = decode_formula(unpair1(unpair2(l_enc)));
    let psi = decode_formula(unpair2(unpair2(l_enc)));
    let chi = decode_formula(unpair2(unpair2(m_enc)));
    decode_implies(enc);
    decode_implies(l_enc);
    decode_implies(r_enc);
    decode_implies(m_enc);
    decode_implies(n_enc);
}

pub proof fn lemma_check_quant_dist_forward(enc: nat)
    requires eval_comp(check_axiom_quantifier_dist(), enc) != 0,
    ensures is_axiom_quantifier_dist(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);
    crate::compspec_forward_structure3::quant_dist_structure(enc);
    let l_enc = unpair1(unpair2(enc));
    let v_val = unpair1(unpair2(l_enc));
    let body_enc = unpair2(unpair2(l_enc));
    let r_enc = unpair2(unpair2(enc));
    let phi_val = unpair1(unpair2(body_enc));
    let psi_val = unpair2(unpair2(body_enc));
    //  R.left == pair(7, pair(v, phi)), R.right == pair(7, pair(v, psi))
    //  Need unpair1 for decode_forall precondition on R.left and R.right
    lemma_unpair1_pair(7nat, pair(v_val, phi_val));
    lemma_unpair1_pair(7nat, pair(v_val, psi_val));
    lemma_unpair2_pair(7nat, pair(v_val, phi_val));
    lemma_unpair2_pair(7nat, pair(v_val, psi_val));
    lemma_unpair1_pair(v_val, phi_val);
    lemma_unpair2_pair(v_val, phi_val);
    lemma_unpair1_pair(v_val, psi_val);
    lemma_unpair2_pair(v_val, psi_val);
    let phi = decode_formula(phi_val);
    let psi = decode_formula(psi_val);
    //  Decode chain
    decode_implies(enc);
    decode_forall(l_enc);
    decode_implies(body_enc);
    decode_implies(r_enc);
    let r_left = unpair1(unpair2(r_enc));
    let r_right = unpair2(unpair2(r_enc));
    decode_forall(r_left);
    decode_forall(r_right);
}

} //  verus!
