use vstd::prelude::*;
use crate::pairing::*;
use crate::formula::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_axiom_eval::*;
use crate::proof_system::*;
use crate::proof_encoding::*;
use crate::zfc::*;

verus! {

//  ====================================================================
//  Forward direction: checker accepts → decoded formula has the property
//  Pattern: hide both eval_comp and decode_formula, reveal separately
//  ====================================================================

//  ---- Identity: φ → φ ----

pub proof fn lemma_check_identity_forward(enc: nat)
    requires eval_comp(check_axiom_identity(), enc) != 0,
    ensures is_axiom_identity(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);

    //  Step 1: Derive structural facts from checker acceptance
    assert(unpair1(enc) == 5 && unpair1(unpair2(enc)) == unpair2(unpair2(enc))) by {
        reveal(eval_comp);
        lemma_eval_cs_and(
            cs_eq(cs_fst(CompSpec::Id), cs_const(5)),
            cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))),
            enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
    }

    //  Step 2: Reconstruct encoding and decode
    lemma_pair_surjective(enc);
    lemma_pair_surjective(unpair2(enc));
    let left = unpair1(unpair2(enc));
    let phi = decode_formula(left);

    assert(decode_formula(enc) == mk_implies(phi, phi)) by {
        reveal(decode_formula);
    }

    assert(is_axiom_identity(decode_formula(enc)));
}

//  ---- Eq Refl: x = x ----

pub proof fn lemma_check_eq_refl_forward(enc: nat)
    requires eval_comp(check_axiom_eq_refl(), enc) != 0,
    ensures is_axiom_eq_refl(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);

    assert(unpair1(enc) == 0 && unpair1(unpair2(enc)) == unpair2(unpair2(enc))) by {
        reveal(eval_comp);
        lemma_eval_cs_and(
            cs_eq(cs_fst(CompSpec::Id), cs_const(0)),
            cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))),
            enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(0), enc);
        lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
    }

    lemma_pair_surjective(enc);
    lemma_pair_surjective(unpair2(enc));
    let left = unpair1(unpair2(enc));
    let t = decode_term(left);

    assert(decode_formula(enc) == mk_eq(t, t)) by {
        reveal(decode_formula);
    }

    assert(is_axiom_eq_refl(decode_formula(enc)));
}

//  ---- Iff Elim Left: (φ ↔ ψ) → (φ → ψ) ----

#[verifier::rlimit(1500)]
pub proof fn lemma_check_iff_elim_left_forward(enc: nat)
    requires eval_comp(check_axiom_iff_elim_left(), enc) != 0,
    ensures is_axiom_iff_elim_left(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);

    let outer_content = cs_snd(CompSpec::Id);
    let iff_part = cs_fst(outer_content);
    let impl_part = cs_snd(outer_content);

    //  Step 1a: Derive tags
    assert(unpair1(enc) == 5
        && unpair1(unpair1(unpair2(enc))) == 6
        && unpair1(unpair2(unpair2(enc))) == 5) by {
        reveal(eval_comp);
        let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
        let c2 = cs_eq(cs_fst(iff_part), cs_const(6));
        let c3 = cs_eq(cs_fst(impl_part), cs_const(5));
        let c4 = cs_eq(cs_snd(iff_part), cs_snd(impl_part));
        lemma_eval_cs_and(c3, c4, enc);
        lemma_eval_cs_and(c2, cs_and(c3, c4), enc);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c4)), enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(iff_part), cs_const(6), enc);
        lemma_eval_eq(cs_fst(impl_part), cs_const(5), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
        lemma_eval_fst(iff_part, enc);
        lemma_eval_fst(impl_part, enc);
    }

    //  Step 1b: Derive content equality
    assert(unpair2(unpair1(unpair2(enc))) == unpair2(unpair2(unpair2(enc)))) by {
        reveal(eval_comp);
        let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
        let c2 = cs_eq(cs_fst(iff_part), cs_const(6));
        let c3 = cs_eq(cs_fst(impl_part), cs_const(5));
        let c4 = cs_eq(cs_snd(iff_part), cs_snd(impl_part));
        lemma_eval_cs_and(c3, c4, enc);
        lemma_eval_cs_and(c2, cs_and(c3, c4), enc);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c4)), enc);
        lemma_eval_eq(cs_snd(iff_part), cs_snd(impl_part), enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(iff_part, enc);
        lemma_eval_snd(impl_part, enc);
    }

    //  Step 2: Decode
    lemma_pair_surjective(enc);
    lemma_pair_surjective(unpair2(enc));
    let iff_enc = unpair1(unpair2(enc));
    let impl_enc = unpair2(unpair2(enc));
    lemma_pair_surjective(iff_enc);
    lemma_pair_surjective(impl_enc);
    let content = unpair2(iff_enc);
    lemma_pair_surjective(content);
    let phi = decode_formula(unpair1(content));
    let psi = decode_formula(unpair2(content));

    assert(decode_formula(enc) == mk_implies(mk_iff(phi, psi), mk_implies(phi, psi))) by {
        reveal(decode_formula);
    }

    assert(is_axiom_iff_elim_left(decode_formula(enc)));
}

//  ---- Iff Elim Right: (φ ↔ ψ) → (ψ → φ) ----

#[verifier::rlimit(1500)]
pub proof fn lemma_check_iff_elim_right_forward(enc: nat)
    requires eval_comp(check_axiom_iff_elim_right(), enc) != 0,
    ensures is_axiom_iff_elim_right(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);

    let outer_content = cs_snd(CompSpec::Id);
    let iff_part = cs_fst(outer_content);
    let impl_part = cs_snd(outer_content);

    //  Step 1a: Tags
    assert(unpair1(enc) == 5
        && unpair1(unpair1(unpair2(enc))) == 6
        && unpair1(unpair2(unpair2(enc))) == 5) by {
        reveal(eval_comp);
        let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
        let c2 = cs_eq(cs_fst(iff_part), cs_const(6));
        let c3 = cs_eq(cs_fst(impl_part), cs_const(5));
        let c4 = cs_eq(cs_fst(cs_snd(impl_part)), cs_snd(cs_snd(iff_part)));
        let c5 = cs_eq(cs_snd(cs_snd(impl_part)), cs_fst(cs_snd(iff_part)));
        lemma_eval_cs_and(c4, c5, enc);
        lemma_eval_cs_and(c3, cs_and(c4, c5), enc);
        lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, c5)), enc);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(iff_part), cs_const(6), enc);
        lemma_eval_eq(cs_fst(impl_part), cs_const(5), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
        lemma_eval_fst(iff_part, enc);
        lemma_eval_fst(impl_part, enc);
    }

    //  Step 1b: Content cross-equalities
    assert(unpair1(unpair2(unpair2(unpair2(enc)))) == unpair2(unpair2(unpair1(unpair2(enc))))
        && unpair2(unpair2(unpair2(unpair2(enc)))) == unpair1(unpair2(unpair1(unpair2(enc))))) by {
        reveal(eval_comp);
        let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
        let c2 = cs_eq(cs_fst(iff_part), cs_const(6));
        let c3 = cs_eq(cs_fst(impl_part), cs_const(5));
        let c4 = cs_eq(cs_fst(cs_snd(impl_part)), cs_snd(cs_snd(iff_part)));
        let c5 = cs_eq(cs_snd(cs_snd(impl_part)), cs_fst(cs_snd(iff_part)));
        lemma_eval_cs_and(c4, c5, enc);
        lemma_eval_cs_and(c3, cs_and(c4, c5), enc);
        lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, c5)), enc);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), enc);
        lemma_eval_eq(cs_fst(cs_snd(impl_part)), cs_snd(cs_snd(iff_part)), enc);
        lemma_eval_eq(cs_snd(cs_snd(impl_part)), cs_fst(cs_snd(iff_part)), enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(iff_part, enc);
        lemma_eval_snd(impl_part, enc);
        lemma_eval_fst(cs_snd(iff_part), enc);
        lemma_eval_snd(cs_snd(iff_part), enc);
        lemma_eval_fst(cs_snd(impl_part), enc);
        lemma_eval_snd(cs_snd(impl_part), enc);
    }

    lemma_pair_surjective(enc);
    lemma_pair_surjective(unpair2(enc));
    let iff_enc = unpair1(unpair2(enc));
    let impl_enc = unpair2(unpair2(enc));
    lemma_pair_surjective(iff_enc);
    lemma_pair_surjective(impl_enc);
    let iff_content = unpair2(iff_enc);
    let impl_content = unpair2(impl_enc);
    lemma_pair_surjective(iff_content);
    lemma_pair_surjective(impl_content);

    let phi = decode_formula(unpair1(iff_content));
    let psi = decode_formula(unpair2(iff_content));

    assert(decode_formula(enc) == mk_implies(mk_iff(phi, psi), mk_implies(psi, phi))) by {
        reveal(decode_formula);
    }

    assert(is_axiom_iff_elim_right(decode_formula(enc)));
}

//  ---- Fixed ZFC axiom forward ----

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
