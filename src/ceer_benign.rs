use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_benign_construction::*;
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
// The proof decomposes into:
// 1. axiom_ceer_relators_benign: the CEER image relators form a
//    benign subgroup of F_2 (Aanderaa-Cohen machine encoding)
// 2. lemma_rope_trick: benign subgroup of F_2 → f.p. embedding
//    (proved in verus-group-theory/higman_operations.rs)
// 3. Bridge lemmas connecting two-gen equivalence ↔ quotient
//    equivalence ↔ CEER equivalence

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
/// Proof: Uses the Aanderaa-Cohen machine group encoding +
/// benign subgroup construction + Rope Trick.
///
/// Remaining axioms in the proof chain:
/// - axiom_enumerator_machine_exists (Church-Turing thesis)
/// - axiom_ceer_relators_benign (CEER relators are benign in F_2)
/// - axiom_ceer_to_modular (register→modular machine conversion)
/// - axiom_machine_hnn_isomorphic (HNN associations form isomorphism)
/// - axiom_machine_group_backward (Britton-based backward direction)
/// - axiom_config_words_free_injective (free group normal forms)
/// - lemma_two_gen_to_quotient_equiv, lemma_quotient_to_two_gen_equiv,
///   lemma_two_gen_backward (bridge lemmas)
pub proof fn lemma_ceer_embeds_in_fp_group_main(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|p: Presentation| #[trigger] admits_ceer_embedding(e, p),
{
    // Delegate to the construction module
    lemma_ceer_embeds_in_fp_group(e);

    // Extract witnesses
    let p = choose|p: Presentation, emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_fp_embedding(e, p, emb);
    let emb = choose|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_fp_embedding(e, p, emb);

    // Prove admits_ceer_embedding
    assert(is_ceer_fp_embedding(e, p, emb));
    assert(admits_ceer_embedding(e, p));
}

} // verus!
