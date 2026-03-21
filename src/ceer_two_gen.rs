use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_group::*;
use verus_group_theory::symbol::*;
use verus_group_theory::word::*;
use verus_group_theory::presentation::*;
use verus_group_theory::presentation_lemmas::*;

verus! {

// ============================================================
// Phase 3: Two-Generator Reduction
// ============================================================
//
// Embeds the infinitely-generated CEER group into a 2-generator
// recursively presented group using universal words:
//   gen(n) ↦ y⁻ⁿ x yⁿ
//
// The 2-generator group T_G = ⟨x, y | image relators⟩ where
// each CEER pair (a ≡ b) gives relator:
//   universal_word(a) · inverse_word(universal_word(b))
//
// Since Presentation uses finite Seq<Word> for relators, we
// define equivalence existentially: two words are equivalent in
// T_G if they are equivalent in some finite sub-presentation
// containing enough image relators.

// ============================================================
// Universal words
// ============================================================

/// y^n = Gen(1)^n
pub open spec fn y_power(n: nat) -> Word
{
    Seq::new(n, |_i: int| Symbol::Gen(1))
}

/// y^{-n} = Inv(1)^n
pub open spec fn y_inv_power(n: nat) -> Word
{
    Seq::new(n, |_i: int| Symbol::Inv(1))
}

/// Universal word: y⁻ⁿ x yⁿ
/// Maps generator n to a word in {x=Gen(0), y=Gen(1)}.
pub open spec fn universal_word(n: nat) -> Word
{
    y_inv_power(n) + seq![Symbol::Gen(0)] + y_power(n)
}

/// The image relator for CEER pair (a, b):
///   universal_word(a) · inverse_word(universal_word(b))
/// This is trivial in T_G when a ≡ b.
pub open spec fn image_relator(a: nat, b: nat) -> Word
{
    concat(universal_word(a), inverse_word(universal_word(b)))
}

// ============================================================
// Finite sub-presentations of T_G
// ============================================================

/// A pair record for building finite sub-presentations.
pub struct CeerPair {
    pub a: nat,
    pub b: nat,
    pub stage: nat,
}

/// A finite set of CEER pairs is valid: each pair is actually declared.
pub open spec fn pairs_valid(e: CEER, pairs: Seq<CeerPair>) -> bool {
    forall|i: int| 0 <= i < pairs.len() ==>
        stage_declares(e, (#[trigger] pairs[i]).stage, pairs[i].a, pairs[i].b)
}

/// Build the sequence of image relators from a sequence of CEER pairs.
pub open spec fn image_relators(pairs: Seq<CeerPair>) -> Seq<Word>
{
    Seq::new(pairs.len(), |i: int| image_relator(pairs[i].a, pairs[i].b))
}

/// The finite 2-generator presentation for a given set of CEER pairs.
pub open spec fn two_gen_presentation(pairs: Seq<CeerPair>) -> Presentation
{
    Presentation {
        num_generators: 2,
        relators: image_relators(pairs),
    }
}

// ============================================================
// Equivalence in T_G (existential over finite sub-presentations)
// ============================================================

/// Two words are equivalent in the 2-generator CEER group T_G if
/// there exists a finite set of valid CEER pairs such that the
/// words are equivalent in the corresponding finite presentation.
pub open spec fn equiv_in_two_gen(e: CEER, w1: Word, w2: Word) -> bool {
    exists|pairs: Seq<CeerPair>|
        pairs_valid(e, pairs) &&
        #[trigger] equiv_in_presentation(two_gen_presentation(pairs), w1, w2)
}

// ============================================================
// Helper lemmas
// ============================================================

/// y_power uses only valid symbols for 2 generators.
pub proof fn lemma_y_power_valid(n: nat)
    ensures
        word_valid(y_power(n), 2),
{
    assert forall|i: int| 0 <= i < y_power(n).len()
        implies symbol_valid(#[trigger] y_power(n)[i], 2)
    by {}
}

/// y_inv_power uses only valid symbols for 2 generators.
pub proof fn lemma_y_inv_power_valid(n: nat)
    ensures
        word_valid(y_inv_power(n), 2),
{
    assert forall|i: int| 0 <= i < y_inv_power(n).len()
        implies symbol_valid(#[trigger] y_inv_power(n)[i], 2)
    by {}
}

/// universal_word(n) is word_valid for 2 generators.
pub proof fn lemma_universal_word_valid(n: nat)
    ensures
        word_valid(universal_word(n), 2),
{
    lemma_y_inv_power_valid(n);
    lemma_y_power_valid(n);

    assert(word_valid(seq![Symbol::Gen(0)], 2)) by {
        assert forall|i: int| 0 <= i < seq![Symbol::Gen(0)].len()
            implies symbol_valid(#[trigger] seq![Symbol::Gen(0)][i], 2)
        by {}
    }

    lemma_concat_word_valid(y_inv_power(n), seq![Symbol::Gen(0)], 2);
    lemma_concat_word_valid(
        y_inv_power(n) + seq![Symbol::Gen(0)],
        y_power(n),
        2,
    );
    assert(universal_word(n) =~=
        (y_inv_power(n) + seq![Symbol::Gen(0)]) + y_power(n));
}

/// image_relator(a, b) is word_valid for 2 generators.
pub proof fn lemma_image_relator_valid(a: nat, b: nat)
    ensures
        word_valid(image_relator(a, b), 2),
{
    lemma_universal_word_valid(a);
    lemma_universal_word_valid(b);
    lemma_inverse_word_valid(universal_word(b), 2);
    lemma_concat_word_valid(
        universal_word(a),
        inverse_word(universal_word(b)),
        2,
    );
}

/// two_gen_presentation is presentation_valid when pairs are valid.
/// image_relators indexing: image_relators(pairs)[i] == image_relator(pairs[i].a, pairs[i].b).
pub proof fn lemma_image_relators_index(pairs: Seq<CeerPair>, i: int)
    requires
        0 <= i < pairs.len(),
    ensures
        image_relators(pairs)[i] == image_relator(pairs[i].a, pairs[i].b),
{
    let f = |j: int| image_relator(pairs[j].a, pairs[j].b);
    assert(Seq::new(pairs.len(), f)[i] == f(i));
}

/// two_gen_presentation relator indexing: directly gives p.relators[i].
proof fn lemma_two_gen_relator_index(pairs: Seq<CeerPair>, i: int)
    requires
        0 <= i < pairs.len(),
    ensures
        two_gen_presentation(pairs).relators[i] == image_relator(pairs[i].a, pairs[i].b),
        two_gen_presentation(pairs).relators.len() == pairs.len(),
        two_gen_presentation(pairs).num_generators == 2,
{
    lemma_image_relators_index(pairs, i);
}

pub proof fn lemma_two_gen_presentation_valid(e: CEER, pairs: Seq<CeerPair>)
    requires
        pairs_valid(e, pairs),
    ensures
        presentation_valid(two_gen_presentation(pairs)),
{
    reveal(presentation_valid);
    let p = two_gen_presentation(pairs);
    assert forall|i: int| 0 <= i < p.relators.len()
        implies word_valid(#[trigger] p.relators[i], p.num_generators)
    by {
        lemma_image_relators_index(pairs, i);
        lemma_image_relator_valid(pairs[i].a, pairs[i].b);
    }
}

/// two_gen_presentation(pairs1) extends to two_gen_presentation(pairs1 + pairs2).
/// (pairs1's relators are a prefix of (pairs1 + pairs2)'s relators.)
proof fn lemma_pairs_extends(
    pairs1: Seq<CeerPair>,
    pairs2: Seq<CeerPair>,
)
    ensures
        extends_presentation(
            two_gen_presentation(pairs1),
            two_gen_presentation(pairs1 + pairs2),
        ),
{
    let p1 = two_gen_presentation(pairs1);
    let p12 = two_gen_presentation(pairs1 + pairs2);

    // Show relators prefix match
    assert(p12.relators.subrange(0, p1.relators.len() as int) =~= p1.relators) by {
        assert(p12.relators.subrange(0, p1.relators.len() as int).len() == p1.relators.len());
        assert forall|i: int| 0 <= i < p1.relators.len()
            implies p12.relators.subrange(0, p1.relators.len() as int)[i] == #[trigger] p1.relators[i]
        by {
            assert(p12.relators.subrange(0, p1.relators.len() as int)[i] == p12.relators[i]);
            lemma_image_relators_index(pairs1, i);
            assert((pairs1 + pairs2)[i] == pairs1[i]);
            lemma_image_relators_index(pairs1 + pairs2, i);
        }
    }
}

/// Enlarging the pairs set preserves equivalence (monotonicity, left).
/// pairs1's relators are a prefix of (pairs1 + pairs2)'s relators.
pub proof fn lemma_pairs_monotone(
    e: CEER,
    pairs1: Seq<CeerPair>,
    pairs2: Seq<CeerPair>,
    w1: Word, w2: Word,
)
    requires
        pairs_valid(e, pairs1),
        pairs_valid(e, pairs2),
        equiv_in_presentation(two_gen_presentation(pairs1), w1, w2),
    ensures
        equiv_in_presentation(two_gen_presentation(pairs1 + pairs2), w1, w2),
{
    lemma_pairs_extends(pairs1, pairs2);
    lemma_quotient_preserves_equiv(
        two_gen_presentation(pairs1),
        two_gen_presentation(pairs1 + pairs2),
        w1, w2,
    );
}

/// Enlarging the pairs set preserves equivalence (monotonicity, right).
/// pairs2's relators appear at offset pairs1.len() in (pairs1 + pairs2)'s relators.
/// Uses relator_inclusion (not prefix-based extends_presentation).
pub proof fn lemma_pairs_monotone_right(
    e: CEER,
    pairs1: Seq<CeerPair>,
    pairs2: Seq<CeerPair>,
    w1: Word, w2: Word,
)
    requires
        pairs_valid(e, pairs1),
        pairs_valid(e, pairs2),
        equiv_in_presentation(two_gen_presentation(pairs2), w1, w2),
    ensures
        equiv_in_presentation(two_gen_presentation(pairs1 + pairs2), w1, w2),
{
    reveal(relators_included);
    let p2 = two_gen_presentation(pairs2);
    let p12 = two_gen_presentation(pairs1 + pairs2);
    let n1 = pairs1.len();

    // Show relators_included by witnessing j = n1 + i for each relator i
    assert forall|i: int| 0 <= i < p2.relators.len()
        implies exists|j: int| 0 <= j < p12.relators.len() &&
            p12.relators[j] == #[trigger] p2.relators[i]
    by {
        lemma_two_gen_relator_index(pairs2, i);
        let j = n1 as int + i;
        assert((pairs1 + pairs2)[j] == pairs2[i]);
        lemma_two_gen_relator_index(pairs1 + pairs2, j);
    }

    lemma_relator_inclusion_preserves_equiv(p2, p12, w1, w2);
}

// ============================================================
// Forward direction: CEER equiv → equiv in T_G
// ============================================================

/// A single CEER declaration (a ≡ b at stage s) gives
/// universal_word(a) ≡ universal_word(b) in the finite presentation
/// with that single pair.
pub proof fn lemma_declared_pair_gives_two_gen_equiv(
    e: CEER, a: nat, b: nat, stage: nat,
)
    requires
        stage_declares(e, stage, a, b),
    ensures
        equiv_in_two_gen(e, universal_word(a), universal_word(b)),
{
    let pair = CeerPair { a, b, stage };
    let pairs = seq![pair];

    assert(pairs_valid(e, pairs)) by {
        assert forall|i: int| 0 <= i < pairs.len()
            implies stage_declares(e, (#[trigger] pairs[i]).stage, pairs[i].a, pairs[i].b)
        by {}
    }

    let p = two_gen_presentation(pairs);
    let uw_a = universal_word(a);
    let uw_b = universal_word(b);
    let inv_uw_b = inverse_word(uw_b);

    // relator is image_relator(a, b) = uw_a · inv_uw_b
    lemma_image_relators_index(pairs, 0);
    assert(p.relators[0] =~= image_relator(a, b));

    // uw_a · inv_uw_b ≡ ε in p (relator is identity)
    lemma_relator_is_identity(p, 0);

    // Strategy: uw_a · inv_uw_b ≡ ε
    // uw_a · inv_uw_b · uw_b ≡ ε · uw_b = uw_b
    lemma_equiv_concat_left(p, concat(uw_a, inv_uw_b), empty_word(), uw_b);
    assert(concat(empty_word(), uw_b) =~= uw_b);
    lemma_equiv_refl(p, uw_b);
    lemma_equiv_transitive(p,
        concat(concat(uw_a, inv_uw_b), uw_b),
        concat(empty_word(), uw_b),
        uw_b,
    );
    // So: (uw_a · inv_uw_b) · uw_b ≡ uw_b

    // By associativity: (uw_a · inv_uw_b) · uw_b = uw_a · (inv_uw_b · uw_b)
    assert(concat(concat(uw_a, inv_uw_b), uw_b) =~=
        concat(uw_a, concat(inv_uw_b, uw_b)));
    // So: uw_a · (inv_uw_b · uw_b) ≡ uw_b

    // inv_uw_b · uw_b ≡ ε (left inverse)
    lemma_word_inverse_left(p, uw_b);

    // uw_a · (inv_uw_b · uw_b) ≡ uw_a · ε (by concat_right)
    lemma_equiv_concat_right(p, uw_a, concat(inv_uw_b, uw_b), empty_word());

    // uw_a · ε = uw_a
    assert(concat(uw_a, empty_word()) =~= uw_a);
    lemma_equiv_refl(p, uw_a);

    // Chain: uw_a = uw_a · ε ≡ uw_a · (inv_uw_b · uw_b) ≡ uw_b
    // Need: uw_a ≡ uw_a · ε = trivial
    // Need: uw_a · ε ≡ uw_a · (inv_uw_b · uw_b) → need symmetric direction
    // We have: uw_a · (inv_uw_b · uw_b) ≡ uw_a · ε
    // So: uw_a · ε ≡ uw_a · (inv_uw_b · uw_b) by symmetry
    lemma_two_gen_presentation_valid(e, pairs);
    lemma_universal_word_valid(a);
    lemma_universal_word_valid(b);
    lemma_inverse_word_valid(uw_b, 2);
    lemma_concat_word_valid(inv_uw_b, uw_b, 2);
    lemma_concat_word_valid(uw_a, concat(inv_uw_b, uw_b), 2);
    lemma_equiv_symmetric(p,
        concat(uw_a, concat(inv_uw_b, uw_b)),
        concat(uw_a, empty_word()),
    );

    // uw_a = uw_a · ε ≡ uw_a · (inv_uw_b · uw_b) ≡ uw_b
    lemma_equiv_transitive(p,
        uw_a,
        concat(uw_a, concat(inv_uw_b, uw_b)),
        uw_b,
    );
}

/// Transitivity of equiv_in_two_gen.
pub proof fn lemma_two_gen_equiv_transitive(
    e: CEER, w1: Word, w2: Word, w3: Word,
)
    requires
        equiv_in_two_gen(e, w1, w2),
        equiv_in_two_gen(e, w2, w3),
    ensures
        equiv_in_two_gen(e, w1, w3),
{
    let pairs1 = choose|pairs: Seq<CeerPair>|
        pairs_valid(e, pairs) &&
        equiv_in_presentation(two_gen_presentation(pairs), w1, w2);
    let pairs2 = choose|pairs: Seq<CeerPair>|
        pairs_valid(e, pairs) &&
        equiv_in_presentation(two_gen_presentation(pairs), w2, w3);

    let combined = pairs1 + pairs2;
    assert(pairs_valid(e, combined)) by {
        assert forall|i: int| 0 <= i < combined.len()
            implies stage_declares(e, (#[trigger] combined[i]).stage, combined[i].a, combined[i].b)
        by {
            if i < pairs1.len() as int {
                assert(combined[i] == pairs1[i]);
            } else {
                assert(combined[i] == pairs2[i - pairs1.len() as int]);
            }
        }
    }

    // Lift both equivalences to the combined presentation
    lemma_pairs_monotone(e, pairs1, pairs2, w1, w2);
    lemma_pairs_monotone_right(e, pairs1, pairs2, w2, w3);

    // Now both are in two_gen_presentation(combined) — apply transitivity
    lemma_equiv_transitive(
        two_gen_presentation(combined), w1, w2, w3,
    );
}

/// Reflexivity of equiv_in_two_gen.
pub proof fn lemma_two_gen_equiv_refl(e: CEER, w: Word)
    ensures
        equiv_in_two_gen(e, w, w),
{
    let pairs = Seq::<CeerPair>::empty();
    assert(pairs_valid(e, pairs)) by {
        assert forall|i: int| 0 <= i < pairs.len()
            implies stage_declares(e, (#[trigger] pairs[i]).stage, pairs[i].a, pairs[i].b)
        by {}
    }
    lemma_equiv_refl(two_gen_presentation(pairs), w);
}

/// Forward direction: ceer_equiv(n, m) → universal_word(n) ≡ universal_word(m) in T_G.
pub proof fn lemma_two_gen_forward(e: CEER, n: nat, m: nat)
    requires
        ceer_equiv(e, n, m),
    ensures
        equiv_in_two_gen(e, universal_word(n), universal_word(m)),
{
    let chain = choose|chain: Seq<nat>| ceer_equiv_chain(e, n, m, chain);
    lemma_two_gen_forward_chain(e, n, m, chain);
}

/// Helper: induction on chain for forward direction.
proof fn lemma_two_gen_forward_chain(e: CEER, n: nat, m: nat, chain: Seq<nat>)
    requires
        ceer_equiv_chain(e, n, m, chain),
    ensures
        equiv_in_two_gen(e, universal_word(n), universal_word(m)),
    decreases chain.len(),
{
    if chain.len() == 1 {
        lemma_two_gen_equiv_refl(e, universal_word(n));
    } else {
        let mid = chain[1];
        let s = choose|s: nat| stage_declares(e, s, n, mid);
        lemma_declared_pair_gives_two_gen_equiv(e, n, mid, s);
        lemma_two_gen_forward_chain(e, mid, m, chain.drop_first());
        lemma_two_gen_equiv_transitive(e,
            universal_word(n),
            universal_word(mid),
            universal_word(m),
        );
    }
}

} // verus!
