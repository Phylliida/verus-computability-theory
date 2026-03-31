# Session Report — 2026-03-30 Session C (Replacement Axiom + Decoding Infrastructure)

## Summary

**ASSUME #3 fully lifted** — replacement axiom checker correctness proved, fixed-axiom restriction removed from `lemma_all_lines_check_backward`. The backward direction of `lemma_halts_comp_correct` is now fully verified with no restrictions.

**Decoding infrastructure built** for ASSUME #4 (forward direction). Phases 0-2 complete: pairing surjectivity, formula/term/justification/sequence/proof decoding with roundtrip lemmas.

**Forward checker soundness** started (Phase 4): identity, eq_refl, iff_elim_left/right, fixed ZFC axiom forward proofs.

## What Was Built

### Replacement Axiom (ASSUME #3 completion)

| File | Changes |
|------|---------|
| `compspec_replacement_helpers.rs` | Complete rewrite: 14 verified — encoding helpers, navigation, tag/var/phi/subst/distinct checks, compose, wrapper |
| `compspec_dispatchers.rs` | Added `lemma_check_zfc_axiom_correct` dispatching to fixed OR replacement |
| `compspec_check_line_helpers.rs` | Changed `check_line_assumption` to use `is_zfc_axiom` instead of fixed-axiom list |
| `compspec_halts.rs` | Removed fixed-axiom precondition from `lemma_all_lines_check_backward` |

### Decoding Infrastructure (Phases 0-2)

| File | Functions Added | Description |
|------|----------------|-------------|
| `pairing.rs` | 6 | lemma_unpair_sum, lemma_pair_surjective, lemma_unpair1_le, lemma_unpair2_le, lemma_unpair2_lt, lemma_unpair_content_lt |
| `formula.rs` | 5 | decode_term, decode_formula (with via termination proof), lemma_decode_encode_term, lemma_decode_encode_formula, lemma_encode_decode_formula |
| `proof_encoding.rs` | 8 | decode_justification, decode_line, decode_nat_seq (with via termination), decode_proof, roundtrip lemmas for all 4 |

### Forward Checker Soundness (Phase 4, partial)

| File | Functions | Description |
|------|-----------|-------------|
| `compspec_forward_checkers.rs` | 5 | identity, eq_refl, iff_elim_left, iff_elim_right, fixed ZFC axiom forward proofs |

## Key Techniques

### 1. Pairing Surjectivity for Decoding
`pair(unpair1(p), unpair2(p)) == p` — essential for proving `encode(decode_formula(n)) == n`. Proof uses the anti-diagonal uniqueness of the Cantor pairing.

### 2. `via` Clause for Termination of decode_formula
`decode_formula(n)` recurses on `unpair2(n)`. Termination requires `unpair2(n) < n` when `unpair1(n) >= 1`. Z3 can't derive this automatically — use `via decode_formula_decreases` with `lemma_unpair2_lt`.

### 3. Trivial encode-after-decode via choose
Instead of complex recursive proof for `encode(decode_formula(n)) == n`, use:
```rust
requires exists|f: Formula| encode(f) == n,
// Then: let f = choose|f| encode(f) == n;
// lemma_decode_encode_formula(f) gives decode(encode(f)) == f
// So encode(decode(n)) == encode(decode(encode(f))) == encode(f) == n
```

### 4. hide(eval_comp) + hide(decode_formula) for Forward Direction
Both `eval_comp` and `decode_formula` are complex open spec functions. Having both visible overwhelms Z3. Pattern: hide both, reveal(eval_comp) in one assert-by for checker facts, reveal(decode_formula) in another for decoding.

### 5. nonlinear_arith for nat multiplication
Z3 struggles with `a*b != 0 when a,b > 0` for nats. Use `by (nonlinear_arith) requires a > 0, b > 0, c == a*b;`.

## Remaining Work for ASSUME #4

### Phase 3: Strengthen eq_subst checkers (CRITICAL BLOCKER)
Current `check_axiom_eq_subst_left/right` only checks 3 tags — too permissive for forward direction soundness. Need parallel-walk BoundedRec checker + proofs in both directions. ~400-600 lines.

### Phase 4: More forward checker proofs needed
- iff_intro, hyp_syllogism, quantifier_dist forward
- universal_inst, vacuous_quant forward (need check_subst/has_free_var forward)
- eq_subst_left/right forward (after Phase 3)
- replacement axiom forward
- modus ponens, generalization forward
- sentence checker forward

### Phase 5: check_all_lines iteration forward (~200-300 lines)
### Phase 6: Assembly — wire into lemma_halts_comp_correct (~50-100 lines)

## Bugs Fixed

### decode_nat_seq_last latent termination bug
Adding pairing surjectivity lemmas exposed a pre-existing termination issue in `decode_nat_seq_last`: for `n = pair(0, 1) = 1`, `unpair2(1) = 1` (no decrease). Fixed by adding `unpair1(enc) == 0` guard + `via` termination proof.
