use vstd::prelude::*;
use crate::pairing::*;
use crate::formula::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_axiom_eval::*;
use crate::compspec_forward_structure::*;
use crate::proof_system::*;
use crate::proof_encoding::*;
use crate::zfc::*;

verus! {

//  Simple forward checker proofs (low rlimit, no sibling pollution issues)

pub proof fn lemma_check_identity_forward(enc: nat)
    requires eval_comp(check_axiom_identity(), enc) != 0,
    ensures is_axiom_identity(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);
    identity_structure(enc);
    lemma_pair_surjective(enc);
    lemma_pair_surjective(unpair2(enc));
    let phi = decode_formula(unpair1(unpair2(enc)));
    assert(decode_formula(enc) == mk_implies(phi, phi)) by { reveal(decode_formula); }
}

pub proof fn lemma_check_eq_refl_forward(enc: nat)
    requires eval_comp(check_axiom_eq_refl(), enc) != 0,
    ensures is_axiom_eq_refl(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);
    eq_refl_structure(enc);
    lemma_pair_surjective(enc);
    lemma_pair_surjective(unpair2(enc));
    let t = decode_term(unpair1(unpair2(enc)));
    assert(decode_formula(enc) == mk_eq(t, t)) by { reveal(decode_formula); }
}

pub proof fn lemma_check_zfc_fixed_forward(enc: nat, axiom: Formula)
    requires
        axiom == extensionality_axiom() || axiom == pairing_axiom()
        || axiom == union_axiom() || axiom == powerset_axiom()
        || axiom == infinity_axiom() || axiom == foundation_axiom()
        || axiom == choice_axiom(),
        enc == encode(axiom),
    ensures
        is_zfc_axiom(decode_formula(enc)),
        decode_formula(enc) == axiom,
{
    lemma_decode_encode_formula(axiom);
    reveal(is_zfc_axiom);
}

} //  verus!
