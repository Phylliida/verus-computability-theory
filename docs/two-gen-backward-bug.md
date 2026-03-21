# Bug: `lemma_two_gen_backward` is false

## Summary

`lemma_two_gen_backward` (and `lemma_quotient_to_two_gen_equiv`) in
`ceer_benign_construction.rs` are false as stated. The two-gen encoding
via image relators creates spurious identifications in F_2 that go
beyond the intended CEER equivalence.

## Counterexample

CEER `e` with a single declared pair `(0, 1)`:
- `ceer_equiv` identifies only 0 and 1 (plus reflexive closure).
- `ceer_equiv(e, 2, 3)` is **false** (no chain from 2 to 3).

But `equiv_in_two_gen(e, uw(2), uw(3))` is **true**:

```
image_relator(0, 1) = concat(uw(0), inverse_word(uw(1)))
                     = x · y⁻¹ x⁻¹ y
                     = [x, y⁻¹]     (the commutator)
```

Setting `[x, y⁻¹] = 1` makes x and y **commute** in the quotient
`F_2 / ⟨⟨image_relator(0,1)⟩⟩`. The quotient is Z × Z.

In Z × Z, every universal word `uw(n) = y⁻ⁿ x yⁿ = x` (since xy = yx).
So **all** universal words are identified — far more than the CEER declares.

Explicit witness: `uw(2) · inv(uw(3)) = y⁻² · (x y⁻¹ x⁻¹ y) · y²`
is a conjugate of the relator, hence identity in the quotient.

## Root cause

The image relator `uw(a) · inv(uw(b))` encodes "generator a = generator b"
in the CeerGroup (infinite generators). But in F_2 (two generators), it also
constrains the relationship between x and y. Specifically:

- `image_relator(a, b) = y⁻ᵃ x yᵃ · y⁻ᵇ x⁻¹ yᵇ = y⁻ᵃ x y^(a-b) x⁻¹ yᵇ`
- When `a - b = 1` (e.g., pair (0,1)): this is `x y⁻¹ x⁻¹ y = [x, y⁻¹]`
- When `|a - b| = k`: this says `x` commutes with `y^k`

These "side-effect" commutation relations identify universal words at
all indices congruent mod k, not just the declared pair.

The CeerGroup formulation (infinite generators, relator `[Gen{a}, Inv{b}]`)
does NOT have this problem — each relator only relates two specific generators
with no side effects.

## Affected items

1. **`lemma_two_gen_backward`** (`ceer_benign_construction.rs`):
   FALSE. `equiv_in_two_gen(e, uw(n), uw(m)) → ceer_equiv(e, n, m)` fails.

2. **`lemma_quotient_to_two_gen_equiv`** (`ceer_benign_construction.rs`):
   FALSE. `equiv_in_presentation(add_relators(free_group(2), gens), uw(n), uw(m)) → ceer_equiv(e, n, m)` fails because `in_ceer_normal_closure` (used in the biconditional precondition) is defined via `equiv_in_two_gen`, which is too permissive. The gens generate a subgroup that's too large, and the quotient identifies too many universal words.

3. **`in_ceer_normal_closure`** (`ceer_benign_construction.rs`):
   WRONG DEFINITION. Currently `equiv_in_two_gen(e, w, empty_word())`, which
   includes words like `uw(2) · inv(uw(3))` when only pair (0,1) is declared.
   The intended semantics is the normal closure of image relators for
   *actually declared* pairs, but the two-gen quotient creates additional
   identifications.

4. **`axiom_ceer_relators_benign`**: The biconditional
   `in_generated_subgroup ↔ in_ceer_normal_closure` references the wrong
   definition. The axiom itself may be true (gens DO generate the set
   `in_ceer_normal_closure` as defined), but the definition doesn't match
   the intended semantics.

## What still works

- **Forward direction** (`lemma_two_gen_forward`): CORRECT.
  `ceer_equiv → equiv_in_two_gen` is fine — the two-gen quotient identifies
  at least everything the CEER does (plus more).

- **`lemma_two_gen_to_quotient_equiv`**: CORRECT as proved.
  `equiv_in_two_gen → equiv_in_quotient` is valid (the quotient is an
  extension of the two-gen presentation).

- **CeerGroup backward** (`ceer_group_backward.rs`): CORRECT.
  `ceer_group_equiv → ceer_equiv` uses the word_count technique on
  infinite-generator CeerWords, which doesn't suffer from conjugation
  side effects.

- **`lemma_ceer_equiv_iff_group_equiv`**: CORRECT.
  The CeerGroup formulation is sound in both directions.

## Impact on theorem_zfc_equiv_in_fp_group

The backward direction of the embedding biconditional in
`lemma_ceer_embeds_in_fp_group` is unsound:

```
Forward:  ceer_equiv → two_gen_forward → two_gen_to_quotient → rope_trick → equiv in H  ✓
Backward: equiv in H → rope_trick → equiv in quotient → ??? → ceer_equiv               ✗
```

The "???" step uses `lemma_quotient_to_two_gen_equiv` (false) and
`lemma_two_gen_backward` (false, also redundant).

## Fix approach

The backward direction should bypass the two-gen encoding entirely and
use the CeerGroup (infinite generators) instead.

### Option A: Redefine in_ceer_normal_closure via CeerGroup

Replace `in_ceer_normal_closure` with a definition based on the CeerGroup:
a word `w` is in the CEER normal closure iff its "interpretation" as a
CeerWord (mapping x-occurrences at y-depth k to Gen{k}) is equivalent to
the empty word in the CeerGroup.

This requires:
1. Define `interpret: Word → CeerWord` (scanning left-to-right, tracking
   y-prefix, emitting Gen/Inv for x-occurrences)
2. Handle negative y-prefix (x-occurrences at negative depth don't
   correspond to any CEER generator — they represent "free" generators
   not subject to CEER identifications)
3. Show that `interpret` is compatible with free reductions
4. Redefine benignity biconditional accordingly

### Option B: Restructure the proof to avoid the two-gen backward direction

Keep the forward direction as-is (it works). For the backward direction
of the f.p. embedding, don't go through the two-gen quotient at all.
Instead:

1. The rope trick gives: equiv in H ↔ equiv in add_relators(free_group(2), gens)
2. For the backward direction, define gens to be the "correct" CEER normal
   closure (e.g., via CeerGroup) and prove benignity for that
3. Show equiv in quotient → ceer_equiv directly using a CeerGroup-based
   argument

### Option C: Use HNN extensions instead of naive F_2 quotient

The standard proof of Higman's theorem uses HNN extensions:
1. Base group B = CeerGroup (correctly defined, infinite generators)
2. HNN extension with stable letter t, associating g_n with g_{n+1}
   (identity association on all generators)
3. In the HNN extension: t⁻ⁿ g_0 tⁿ = g_n, recovering universal words
4. Britton's lemma guarantees faithfulness: the universal words in the
   HNN extension correctly reflect CeerGroup equivalence

The codebase already has Britton's lemma machinery (`britton.rs`,
`britton_proof.rs`), HNN extension definitions (`hnn.rs`), and
the HNN-based backward proof could leverage the existing
`ceer_group_backward` word_count technique.

This is the mathematically cleanest fix but requires the most refactoring.

## Recommended fix

**Option B** is likely the most practical:

1. Redefine `in_ceer_normal_closure(e, w)` using CeerGroup equivalence
   instead of `equiv_in_two_gen`
2. Update `axiom_ceer_relators_benign` biconditional accordingly
3. For the backward direction, prove: equiv in quotient → interpret →
   CeerGroup equiv → ceer_equiv (using existing ceer_group_backward)
4. Remove `lemma_two_gen_backward` (false and redundant)
5. Rewrite `lemma_quotient_to_two_gen_equiv` with correct definition

The forward direction (`lemma_two_gen_to_quotient_equiv`, just proved)
remains valid and doesn't need changes.
