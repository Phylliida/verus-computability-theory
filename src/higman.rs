use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_group::*;
use crate::ceer_group_backward::*;
use crate::ceer_two_gen::*;
use crate::ceer_benign::*;
use crate::zfc_ceer::*;
use verus_group_theory::presentation::*;
use verus_group_theory::word::*;
use verus_group_theory::benign::*;
use verus_group_theory::higman_operations::*;
use verus_group_theory::quotient::*;

verus! {

/// An embedding of CEER group equivalence into a finitely presented group.
/// Uses ceer_group_equiv (derivation-based) rather than ceer_equiv directly,
/// so the axiom only states the group-theoretic Higman embedding.
pub open spec fn is_ceer_group_fp_embedding(
    e: CEER, p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        ceer_group_equiv(e, generator_word(n), generator_word(m))
            <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

/// Presentation p admits a CEER group embedding for e.
pub open spec fn admits_ceer_group_embedding(e: CEER, p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_group_fp_embedding(e, p, emb)
}

/// An embedding of ZFC equivalence into presentation p via map emb is valid.
pub open spec fn is_zfc_group_embedding(
    p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        zfc_equiv_nat(n, m) <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

/// Presentation p admits a ZFC equivalence embedding.
pub open spec fn admits_zfc_embedding(p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_zfc_group_embedding(p, emb)
}

/// Transfer: CEER group embedding + ceer_equiv ↔ zfc_equiv → ZFC embedding.
proof fn lemma_ceer_group_to_zfc_embedding(e: CEER, p: Presentation)
    requires
        admits_ceer_group_embedding(e, p),
        forall|n: nat, m: nat| ceer_equiv(e, n, m) <==> zfc_equiv_nat(n, m),
    ensures
        admits_zfc_embedding(p),
{
    let emb = choose|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_group_fp_embedding(e, p, emb);

    assert forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators) by {};
    assert forall|n: nat, m: nat|
        zfc_equiv_nat(n, m) <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m))
    by {
        // Chain: zfc_equiv ↔ ceer_equiv ↔ ceer_group_equiv ↔ presentation equiv
        lemma_ceer_equiv_iff_group_equiv(e, n, m);
    };
    assert(is_zfc_group_embedding(p, emb));
}

/// Higman's Embedding Theorem: the CEER group (recursively presented)
/// embeds in a finitely presented group.
///
/// Proof chain:
/// 1. axiom_ceer_relators_benign: CEER relators form a benign subgroup of F₂
/// 2. axiom_rope_trick: benign subgroup → f.p. group via Higman's construction
/// 3. Compose: ceer_equiv ↔ equiv in quotient ↔ equiv in f.p. group
/// 4. Bridge: ceer_equiv ↔ ceer_group_equiv (lemma_ceer_equiv_iff_group_equiv)
pub proof fn lemma_higman_embedding(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|p: Presentation|
            presentation_valid(p) && #[trigger] admits_ceer_group_embedding(e, p),
{
    // Step 1: CEER relators form a benign subgroup of F₂
    axiom_ceer_relators_benign(e);

    let gens = choose|gens: Seq<Word>| exists|witness: BenignWitness|
        (forall|i: int| 0 <= i < gens.len() ==>
            word_valid(#[trigger] gens[i], 2)) &&
        #[trigger] benign_witness_valid(free_group(2), gens, witness) &&
        (forall|n: nat, m: nat|
            #[trigger] equiv_in_presentation(
                add_relators(free_group(2), gens),
                universal_word(n),
                universal_word(m),
            ) <==> ceer_equiv(e, n, m));

    let witness = choose|witness: BenignWitness|
        (forall|i: int| 0 <= i < gens.len() ==>
            word_valid(#[trigger] gens[i], 2)) &&
        #[trigger] benign_witness_valid(free_group(2), gens, witness) &&
        (forall|n: nat, m: nat|
            #[trigger] equiv_in_presentation(
                add_relators(free_group(2), gens),
                universal_word(n),
                universal_word(m),
            ) <==> ceer_equiv(e, n, m));

    // Step 2: Rope Trick — benign subgroup → f.p. group
    axiom_rope_trick(gens, witness);

    let fp = choose|p: Presentation| exists|emb: Seq<Word>|
        presentation_valid(p) &&
        emb.len() == 2 &&
        (forall|i: int| 0 <= i < emb.len() ==>
            word_valid(#[trigger] emb[i], p.num_generators)) &&
        (forall|w1: Word, w2: Word|
            word_valid(w1, 2) && word_valid(w2, 2) &&
            equiv_in_presentation(add_relators(free_group(2), gens), w1, w2)
            ==> #[trigger] equiv_in_presentation(p, apply_embedding(emb, w1), apply_embedding(emb, w2))) &&
        (forall|w1: Word, w2: Word|
            word_valid(w1, 2) && word_valid(w2, 2) &&
            equiv_in_presentation(p, apply_embedding(emb, w1), apply_embedding(emb, w2))
            ==> #[trigger] equiv_in_presentation(add_relators(free_group(2), gens), w1, w2));

    let emb_seq = choose|emb: Seq<Word>|
        presentation_valid(fp) &&
        emb.len() == 2 &&
        (forall|i: int| 0 <= i < emb.len() ==>
            word_valid(#[trigger] emb[i], fp.num_generators)) &&
        (forall|w1: Word, w2: Word|
            word_valid(w1, 2) && word_valid(w2, 2) &&
            equiv_in_presentation(add_relators(free_group(2), gens), w1, w2)
            ==> #[trigger] equiv_in_presentation(fp, apply_embedding(emb, w1), apply_embedding(emb, w2))) &&
        (forall|w1: Word, w2: Word|
            word_valid(w1, 2) && word_valid(w2, 2) &&
            equiv_in_presentation(fp, apply_embedding(emb, w1), apply_embedding(emb, w2))
            ==> #[trigger] equiv_in_presentation(add_relators(free_group(2), gens), w1, w2));

    // Step 3: Composed embedding n ↦ apply_embedding(emb_seq, universal_word(n))
    let emb_fn: spec_fn(nat) -> Word = |n: nat| apply_embedding(emb_seq, universal_word(n));

    // Step 4: Word validity of composed embedding
    assert forall|n: nat| #[trigger] word_valid(emb_fn(n), fp.num_generators) by {
        lemma_universal_word_valid(n);
        lemma_apply_embedding_valid(emb_seq, universal_word(n), fp.num_generators);
    };

    // Step 5: Biconditional — ceer_group_equiv ↔ equiv in f.p. group
    assert forall|n: nat, m: nat|
        ceer_group_equiv(e, generator_word(n), generator_word(m))
            <==> #[trigger] equiv_in_presentation(fp, emb_fn(n), emb_fn(m))
    by {
        // ceer_group_equiv ↔ ceer_equiv
        lemma_ceer_equiv_iff_group_equiv(e, n, m);
        // universal_words are valid 2-gen words (needed for rope trick quantifier preconditions)
        lemma_universal_word_valid(n);
        lemma_universal_word_valid(m);
        // Z3 chains:
        //   ceer_group_equiv ↔ ceer_equiv (lemma above)
        //   ceer_equiv ↔ equiv_in_quotient (axiom_ceer_relators_benign)
        //   equiv_in_quotient ↔ equiv_in_fp (axiom_rope_trick forward + backward)
    };

    assert(is_ceer_group_fp_embedding(e, fp, emb_fn));
    assert(admits_ceer_group_embedding(e, fp));
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

    // Step 2: Apply Higman embedding
    lemma_higman_embedding(e);
    let p = choose|p: Presentation|
        presentation_valid(p) && admits_ceer_group_embedding(e, p);

    // Step 3: Chain ceer_equiv ↔ group_equiv ↔ presentation equiv,
    //         then transfer to ZFC embedding
    lemma_ceer_group_to_zfc_embedding(e, p);
}

} // verus!
