use vstd::prelude::*;
use crate::ceer::*;
use crate::zfc_ceer::*;
use verus_group_theory::presentation::*;
use verus_group_theory::word::*;

verus! {

/// An embedding of CEER e into presentation p via map emb is valid:
/// all images are valid words, and equivalence is preserved.
pub open spec fn is_ceer_group_embedding(
    e: CEER, p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        ceer_equiv(e, n, m) <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

/// An embedding of ZFC equivalence into presentation p via map emb is valid.
pub open spec fn is_zfc_group_embedding(
    p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        zfc_equiv_nat(n, m) <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

/// Presentation p admits a CEER embedding for e.
pub open spec fn admits_ceer_embedding(e: CEER, p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_group_embedding(e, p, emb)
}

/// Presentation p admits a ZFC equivalence embedding.
pub open spec fn admits_zfc_embedding(p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_zfc_group_embedding(p, emb)
}

/// Transfer: if a CEER embedding exists and ceer_equiv <==> zfc_equiv_nat,
/// then a ZFC embedding exists (same map works).
proof fn lemma_ceer_to_zfc_embedding(e: CEER, p: Presentation)
    requires
        admits_ceer_embedding(e, p),
        forall|n: nat, m: nat| ceer_equiv(e, n, m) <==> zfc_equiv_nat(n, m),
    ensures
        admits_zfc_embedding(p),
{
    let emb = choose|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_group_embedding(e, p, emb);

    assert forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators) by {};
    assert forall|n: nat, m: nat|
        zfc_equiv_nat(n, m) <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m))
    by {
        assert(ceer_equiv(e, n, m) <==> zfc_equiv_nat(n, m));
        assert(ceer_equiv(e, n, m) <==> equiv_in_presentation(p, emb(n), emb(m)));
    };
    assert(is_zfc_group_embedding(p, emb));
}

/// Higman's Embedding Theorem: every CEER embeds in the word problem
/// of a finitely presented group.
///
/// Construction (Mikaelian 2025): Given a CEER with enumerator machine,
/// build a recursively presented group G (one generator per natural,
/// relators from declared pairs). Embed G into a finitely presented
/// group via iterated HNN extensions and free products with amalgamation.
/// The embedding is injective, so the word problem of the f.p. group
/// restricted to the image exactly captures CEER equivalence.
///
/// The verus-group-theory crate has the infrastructure for this construction
/// (HNN extensions, free products, homomorphisms, Schreier theory), but
/// the full proof requires formalizing benign subgroups and the iterative
/// construction (~2000 lines across multiple sessions).
#[verifier::external_body]
pub proof fn axiom_higman_embedding(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|p: Presentation|
            presentation_valid(p) && #[trigger] admits_ceer_embedding(e, p)
{
}

/// ZFC provable equivalence on sentences embeds in the word problem
/// of a finitely presented group.
///
/// There exist a finite group presentation G and a map f: N -> G
/// such that two Gödel codes n, m encode ZFC-equivalent sentences
/// if and only if f(n) and f(m) represent the same element of G.
pub proof fn theorem_zfc_equiv_in_fp_group()
    ensures
        exists|p: Presentation|
            presentation_valid(p) && #[trigger] admits_zfc_embedding(p)
{
    // Step 1: ZFC equivalence is a CEER
    lemma_zfc_equiv_is_ceer();
    let e = choose|e: CEER| ceer_wf(e) &&
        forall|n: nat, m: nat| ceer_equiv(e, n, m) <==> zfc_equiv_nat(n, m);

    // Step 2: Apply Higman embedding to this CEER
    axiom_higman_embedding(e);
    let p = choose|p: Presentation|
        presentation_valid(p) && admits_ceer_embedding(e, p);

    // Step 3: Transfer CEER → ZFC embedding (same map works)
    lemma_ceer_to_zfc_embedding(e, p);
}

} // verus!
