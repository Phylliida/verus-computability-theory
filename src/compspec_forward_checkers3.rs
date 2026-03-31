use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_forward_structure::*;
use crate::proof_system::*;

verus! {

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

#[verifier::rlimit(1500)]
pub proof fn lemma_check_iff_intro_forward(enc: nat)
    requires eval_comp(check_axiom_iff_intro(), enc) != 0,
    ensures is_axiom_iff_intro(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);
    hide(check_axiom_iff_intro);
    iff_intro_structure(enc);
    let l_enc = unpair1(unpair2(enc));
    let r_enc = unpair2(unpair2(enc));
    lemma_pair_surjective(unpair2(l_enc));
    lemma_pair_surjective(unpair2(r_enc));
    let phi = decode_formula(unpair1(unpair2(l_enc)));
    let psi = decode_formula(unpair2(unpair2(l_enc)));
    decode_implies(enc);
    decode_implies(l_enc);
    decode_implies(r_enc);
    let r_left = unpair1(unpair2(r_enc));
    let r_right = unpair2(unpair2(r_enc));
    //  r_left == pair(5, pair(psi_v, phi_v)), r_right == pair(6, ...)
    //  Need unpair1 facts for bridge lemma preconditions
    let phi_v = unpair1(unpair2(l_enc));
    let psi_v = unpair2(unpair2(l_enc));
    lemma_unpair1_pair(5nat, pair(psi_v, phi_v));
    lemma_unpair1_pair(6nat, unpair2(l_enc));
    decode_implies(r_left);
    decode_iff(r_right);
}

} //  verus!
