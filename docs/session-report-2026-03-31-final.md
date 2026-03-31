# Session Report — 2026-03-31 (Full Session)

## Summary

This was a massive session covering ASSUME #3 removal, full decoding infrastructure, forward checker proofs, and forward iteration. ~60 new verified functions across ~15 files.

**ASSUME #3**: Fully removed. Replacement axiom checker proved (14 verified), fixed-axiom restriction lifted.

**ASSUME #4 (forward direction)**: Phases 0, 1, 2, 5 complete. Phase 4 partial (8/11 checkers). Phase 3 CompSpec defined but backward proof broken. Phase 6 not started.

## What Was Built

### 1. Replacement Axiom (ASSUME #3 Completion)

**Files modified:**
- `compspec_replacement_helpers.rs` — Complete rewrite, 14 verified. Encoding helpers + navigation + all 33 checks (15 tag + 8 var + phi + subst + 8 distinct) + compose + wrapper.
- `compspec_dispatchers.rs` — Added `lemma_check_zfc_axiom_correct` dispatching to fixed OR replacement. Uses `reveal(is_zfc_axiom)` for the replacement branch.
- `compspec_check_line_helpers.rs` — Changed `check_line_assumption` requires from fixed-axiom list to `is_zfc_axiom(f)`.
- `compspec_halts.rs` — Removed fixed-axiom precondition from `lemma_all_lines_check_backward`.

**Key technique:** `nonlinear_arith` for nat multiplication in final cs_and composition: `assert(...) by (nonlinear_arith) requires a > 0, b > 0, c == a * b;`

### 2. Pairing Surjectivity (Phase 0)

**File:** `pairing.rs` — 6 new lemmas

| Lemma | Ensures |
|-------|---------|
| `lemma_unpair_sum` | `unpair1(p) + unpair2(p) == unpair_sum(p)` |
| `lemma_pair_surjective` | `pair(unpair1(p), unpair2(p)) == p` |
| `lemma_unpair1_le` | `unpair1(p) <= p` |
| `lemma_unpair2_le` | `unpair2(p) <= p` |
| `lemma_unpair2_lt` | `unpair1(p) >= 1 ==> unpair2(p) < p` |
| `lemma_unpair_content_lt` | Combined bounds for content components |

**Proof approach:** `pair_surjective` uses `unpair_sum` to show `unpair1 + unpair2 = k` (anti-diagonal), then `pair(a, b) = T(a+b) + a = T(k) + (p - T(k)) = p`.

**Side effect:** Adding these lemmas broke `decode_nat_seq_last`'s auto-termination. Fixed by adding `via` clause + `unpair1(enc) == 0` guard.

### 3. Formula Decoding (Phase 1)

**File:** `formula.rs` — 5 new functions

| Function | Type | Description |
|----------|------|-------------|
| `decode_term(n)` | spec | `Var { index: n }` |
| `decode_formula(n)` | spec | Recursive on `n`, dispatches on `unpair1(n)` tag (0-8) |
| `decode_formula_decreases` | via_fn | Termination proof using `lemma_unpair2_lt` |
| `lemma_decode_encode_formula(f)` | proof | `decode_formula(encode(f)) == f` |
| `lemma_encode_decode_formula(n)` | proof | `encode(decode_formula(n)) == n` when `exists f: encode(f) == n` |

**Key technique:** `via` clause for `decode_formula` termination. Z3 can't automatically derive `unpair2(n) < n` when `unpair1(n) >= 1`. The `via_fn` calls `lemma_unpair2_lt` + `lemma_unpair1_le` + `lemma_unpair2_le` to establish this for all recursive calls.

**Key technique:** `lemma_encode_decode_formula` is proved TRIVIALLY using `choose` + the encode→decode roundtrip, avoiding a complex recursive proof:
```rust
let f = choose|f: Formula| encode(f) == n;
lemma_decode_encode_formula(f);
// decode(encode(f)) == f, so encode(decode(n)) == encode(decode(encode(f))) == encode(f) == n
```

### 4. Proof Decoding (Phase 2)

**File:** `proof_encoding.rs` — 8 new functions + 1 fix

| Function | Type | Description |
|----------|------|-------------|
| `decode_justification(n)` | spec | Dispatch on tag (0-3), default LogicAxiom |
| `decode_line(n)` | spec | `(decode_formula(unpair1(n)), decode_justification(unpair2(n)))` |
| `decode_nat_seq(n)` | spec | Recursive with `via` termination, guards `unpair1(n) == 0` |
| `decode_proof(s)` | spec | `decode_nat_seq` + `decode_line` for each element |
| `lemma_decode_encode_justification` | proof | Roundtrip for justifications |
| `lemma_decode_encode_line` | proof | Roundtrip for lines |
| `lemma_decode_encode_nat_seq` | proof | Roundtrip for nat sequences |
| `lemma_decode_encode_proof` | proof | Roundtrip for proofs |

**Fix:** `decode_nat_seq_last` had latent termination issue (for `n = pair(0,1) = 1`, `unpair2(1) = 1` — no decrease). Fixed by adding `unpair1(enc) == 0` guard + `via` clause.

### 5. Forward Structural Extraction (Phase 4 — Structure Helpers)

**Architecture:** Each checker's forward proof is split into two parts:
1. **Structural extraction** (in structure module): Takes `eval_comp(checker, enc) != 0`, produces unpair facts about `enc`
2. **Forward proof** (in checkers module): Uses structural facts + `decode_formula` to show `is_axiom_X(decode_formula(enc))`

This separation is CRITICAL for rlimit management — eval_comp and decode_formula must NEVER be visible simultaneously.

**Files:**
- `compspec_forward_structure.rs` — 4 verified (identity, eq_refl, iff_elim_left, iff_intro)
- `compspec_forward_structure2.rs` — 5 verified (iff_elim_right + `lemma_cs_and_nonzero_left/right`)
- `compspec_forward_structure3.rs` — 2 verified (hyp_syllogism, quantifier_dist)

**Key technique: `lemma_cs_and_nonzero_left/right`**
Z3 cannot derive `a*b != 0 → a != 0` for nats inside complex eval_comp contexts. Extracted into standalone helpers:
```rust
pub proof fn lemma_cs_and_nonzero_left(a: CompSpec, b: CompSpec, s: nat)
    requires eval_comp(cs_and(a, b), s) != 0,
    ensures eval_comp(a, s) != 0,
{
    lemma_eval_cs_and(a, b, s);
    if eval_comp(a, s) == 0 {
        assert(eval_comp(a, s) * eval_comp(b, s) == 0) by (nonlinear_arith)
            requires eval_comp(a, s) == 0nat;
    }
}
```

These are called to extract individual check nonzero from cs_and chains WITHOUT revealing eval_comp.

**Key technique: cs_and_nonzero calls INSIDE assert-by blocks**
Calling all cs_and_nonzero extractions upfront (before any assert-by) floods the ambient context with eval_comp facts, causing Z3 to explore too many terms when eval_comp is later revealed. Instead, call only the needed extractions inside each assert-by block.

**Key technique: cs_eq argument order**
CompSpec equality is STRUCTURAL (tree shape), not semantic. `cs_eq(a, b)` builds `Eq{left:a, right:b}` which is a different tree from `cs_eq(b, a)` = `Eq{left:b, right:a}`. When defining local CompSpec variables that should match the checker definition, the argument order MUST be identical. This caused a multi-hour debugging session for iff_elim_right.

### 6. Forward Checker Proofs (Phase 4 — Final Proofs)

**Architecture:** Each forward proof calls the structural helper, then uses per-constructor decode bridges to reconstruct the formula without revealing the full `decode_formula` definition.

**Per-constructor decode bridges:**
```rust
proof fn decode_implies(enc: nat)
    requires unpair1(enc) == 5,
    ensures decode_formula(enc) == mk_implies(
        decode_formula(unpair1(unpair2(enc))), decode_formula(unpair2(unpair2(enc)))),
{ reveal(decode_formula); lemma_pair_surjective(enc); }
```

These one-level-unfold bridges avoid the rlimit explosion from revealing decode_formula's full 10-branch definition. Each forward proof calls 2-5 bridges to decode the formula tree level by level.

**Files:**
- `compspec_forward_checkers.rs` — 3 verified (identity, eq_refl, zfc_fixed)
- `compspec_forward_checkers2.rs` — 7 verified (iff_elim_left/right, hyp_syl, quant_dist + bridges)
- `compspec_forward_checkers3.rs` — 3 verified (iff_intro + bridges, rlimit(1500))

**Module isolation:** Complex forward proofs MUST be in separate files from each other. Even with hide/reveal, sibling function bodies pollute the SMT context. The iff_intro proof needed its own file + rlimit(1500).

### 7. Forward Iteration (Phase 5)

**File:** `compspec_forward_iteration.rs` — 10 verified

| Function | Type | Description |
|----------|------|-------------|
| `check_line_product(s, start, count)` | spec | Product of check_line results |
| `lemma_cal_iteration_product` | proof | BoundedRec computes `valid * product` |
| `lemma_product_nonzero_each` | proof | Nonzero product → each factor nonzero |
| `lemma_check_all_lines_forward` | proof | **Main:** check_all_lines nonzero → each check_line nonzero |

**Approach:** Define `check_line_product` as a recursive product of check_line evaluations. Prove by induction that the BoundedRec iteration computes `valid * product`. Then extract individual factor nonzero from product nonzero using contradiction + nonlinear_arith.

**Key details:**
- Base case needs `assert(valid * 1 == valid) by (nonlinear_arith)`
- `assert forall` needs `#[trigger]` annotation on `eval_comp(check_line(), pair(s, ...))`
- Bridge from `(0 + i)` to `i` needed for the final ensures

### 8. Phase 3: eq_subst Checker Strengthening (PARTIALLY DONE)

**CompSpec definitions added to `compspec_halts.rs`:**
- `check_eq_subst_step()` — Parallel-walk step function
- `check_eq_subst_pair()` — BoundedRec parallel walker

**Updated:** `check_axiom_eq_subst_left()` now includes the parallel-walk check:
```
cs_and(tag_checks, cs_comp(check_eq_subst_pair(), cs_pair(left_subst, cs_pair(right_subst, cs_pair(x, y)))))
```

**BROKEN:** `eq_subst_left_inner` in `compspec_logic_axiom_helpers.rs` — postcondition not satisfied. The old proof only proved the 3 tag checks, not the new parallel-walk check.

## What Remains

### Phase 3 Backward Proof (~150-200 lines)
**File:** New file (e.g., `compspec_eq_subst_backward.rs`)

Prove: for `subst(phi, var, x)` and `subst(phi, var, y)`, the parallel-walk checker `check_eq_subst_pair` accepts.

**Approach:** Structural induction on `phi` (9 Formula variants), similar to `lemma_subst_traversal`:
- Atomic (tags 0-1): At each term position, if phi has Var(var), left has x and right has y → swap check passes. Otherwise both have the same term → same check passes.
- Not (tag 2): Tags match, push sub-pair, recurse.
- Binary (tags 3-6): Tags match, push both child pairs, recurse.
- Forall/Exists (tags 7-8): If bound var == subst var, both subs are identical (no substitution inside), same check passes. Otherwise tags + bound vars match, push sub-pair, recurse.

### Phase 4 Remaining (~300 lines)
1. **universal_inst forward** — needs check_subst_comp forward soundness (BoundedRec traversal soundness)
2. **vacuous_quant forward** — needs has_free_var_comp forward soundness
3. **eq_subst_left/right forward** — needs Phase 3 parallel-walk forward soundness

### Phase 6: Assembly (~200-300 lines)
1. **MP/Gen forward proofs** — structural, uses seq_elem_correct for lookup correspondence
2. **check_line dispatch forward** — for each justification tag, connect checker nonzero to line_valid
3. **check_conclusion_iff_sentence forward** — connect conclusion checker to decoded proof conclusion
4. **Final assembly** — Wire into lemma_halts_comp_correct, replace the assume

## Bugs Found

1. **cs_eq argument order** (iff_elim_right): Arguments to cs_eq were swapped vs checker definition. CompSpec structural equality doesn't commute. Multi-hour debug.
2. **decode_nat_seq_last termination** (pairing.rs changes): Adding surjectivity lemmas broke auto-termination of pre-existing function. Fixed with `via` clause + guard.
3. **Ambient context pollution** (cs_and_nonzero): Calling all extractions upfront flooded ambient with eval_comp facts. Fixed by scoping inside assert-by blocks.

## Techniques Catalog

| Technique | When to Use | Example |
|-----------|------------|---------|
| `hide(eval_comp)` + `hide(decode_formula)` | Forward checker proofs | All forward proofs |
| Per-constructor decode bridges | Decoding without full reveal | `decode_implies`, `decode_iff`, `decode_forall` |
| `lemma_cs_and_nonzero_left/right` | Extracting factors from cs_and chain | Structure extraction for 5+ check chains |
| cs_and_nonzero inside assert-by | Limiting ambient context | hyp_syl_structure, quant_dist_structure |
| Module isolation | Avoiding sibling function body pollution | Each structure/checker proof in own file |
| `via` clause for termination | Recursive spec fns on nats | decode_formula, decode_nat_seq |
| `choose` for encode-decode roundtrip | Proving encode(decode(n)) == n | lemma_encode_decode_formula |
| `by (nonlinear_arith)` | nat multiplication properties | cs_and composition, product nonzero |
| `reveal(is_zfc_axiom)` | ZFC axiom disjunction visibility | replacement axiom dispatch |
| `#[trigger]` on `eval_comp(...)` | assert forall with eval_comp | iteration forward ensures |

## File Summary

| File | Verified | Status |
|------|----------|--------|
| `pairing.rs` | +6 | ✓ |
| `formula.rs` | +5 | ✓ |
| `proof_encoding.rs` | +8 | ✓ |
| `compspec_replacement_helpers.rs` | 14 | ✓ |
| `compspec_dispatchers.rs` | +1 | ✓ |
| `compspec_check_line_helpers.rs` | 6 | ✓ (modified) |
| `compspec_halts.rs` | 24 | ✓ (eq_subst CompSpec added) |
| `compspec_all_lines_helpers.rs` | verified | ✓ (made 3 fns pub) |
| `compspec_forward_structure.rs` | 4 | ✓ NEW |
| `compspec_forward_structure2.rs` | 5 | ✓ NEW |
| `compspec_forward_structure3.rs` | 2 | ✓ NEW |
| `compspec_forward_checkers.rs` | 3 | ✓ NEW |
| `compspec_forward_checkers2.rs` | 7 | ✓ NEW |
| `compspec_forward_checkers3.rs` | 3 | ✓ NEW |
| `compspec_forward_iteration.rs` | 10 | ✓ NEW |
| `compspec_logic_axiom_helpers.rs` | 33 verified, 1 error | ⚠ eq_subst_left_inner broken |
