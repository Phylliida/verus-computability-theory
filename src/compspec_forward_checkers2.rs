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

pub proof fn lemma_check_iff_intro_forward(enc: nat)
    requires eval_comp(check_axiom_iff_intro(), enc) != 0,
    ensures is_axiom_iff_intro(decode_formula(enc)),
{
    hide(decode_formula);
    iff_intro_structure(enc);
    let l_enc = unpair1(unpair2(enc));
    let r_enc = unpair2(unpair2(enc));
    lemma_pair_surjective(unpair2(l_enc));
    lemma_pair_surjective(unpair2(r_enc));
    let phi = decode_formula(unpair1(unpair2(l_enc)));
    let psi = decode_formula(unpair2(unpair2(l_enc)));
    //  Outer: Implies(L, R)
    decode_implies(enc);
    //  L = Implies(phi, psi)
    decode_implies(l_enc);
    //  R = Implies(Implies(psi, phi), Iff(phi, psi))
    decode_implies(r_enc);
    //  R.left = Implies(psi, phi), R.right = Iff(phi, psi)
    //  Need to decode R.left and R.right
    let r_left = unpair1(unpair2(r_enc));
    let r_right = unpair2(unpair2(r_enc));
    decode_implies(r_left);
    decode_iff(r_right);
}

} //  verus!
