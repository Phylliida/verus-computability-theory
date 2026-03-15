use vstd::prelude::*;
use crate::ceer::*;
use verus_group_theory::word::*;
use verus_group_theory::presentation::*;

verus! {

// ============================================================
// Higman's Embedding Theorem for CEER Groups
// ============================================================
//
// Higman's theorem states that every recursively presented group
// embeds in a finitely presented group.
//
// The CEER group G = ⟨g₀, g₁, ... | gₐgᵦ⁻¹ for declared (a,b)⟩
// is recursively presented (the enumerator machine produces the
// declared pairs computably). By Higman's theorem, G embeds
// faithfully in some finitely presented group H.
//
// NOTE: An earlier version tried to route through a 2-generator
// intermediate group F₂/⟨⟨gens⟩⟩ using universal words y⁻ⁿxyⁿ.
// This approach is mathematically flawed: in ANY quotient of F₂
// where universal_word(0) ≡ universal_word(1), conjugation by y
// forces universal_word(n) ≡ universal_word(n+1) for ALL n,
// making all universal words equivalent. This means no quotient
// of F₂ can faithfully capture a non-trivial, non-universal CEER
// equivalence on universal words.
//
// The correct formulation states the embedding directly from
// the CEER equivalence to the finitely presented group, without
// going through a 2-generator intermediate.

/// A valid embedding of a CEER into a finitely presented group.
pub open spec fn is_ceer_fp_embedding(
    e: CEER, p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    presentation_valid(p) &&
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        ceer_equiv(e, n, m) <==>
        #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

/// Presentation p admits an embedding of CEER e.
pub open spec fn admits_ceer_embedding(e: CEER, p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_fp_embedding(e, p, emb)
}

/// Higman's Embedding Theorem for CEER groups:
/// The CEER group (recursively presented, possibly infinitely generated)
/// embeds faithfully in a finitely presented group.
///
/// There exist a finite presentation H and a map emb: N → H such that
/// ceer_equiv(n, m) ⟺ emb(n) ≡ emb(m) in H.
///
/// The construction follows Higman's original approach:
/// 1. The CEER enumerator is a register machine M
/// 2. M's computation is encoded into a finitely presented group
///    via HNN extensions and amalgamated free products
/// 3. The encoding preserves the equivalence relation faithfully
///
/// This axiom captures the full content of Higman's theorem applied
/// to computably enumerable equivalence relations.
#[verifier::external_body]
pub proof fn axiom_ceer_embeds_in_fp_group(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|p: Presentation| #[trigger] admits_ceer_embedding(e, p),
{
}

} // verus!
