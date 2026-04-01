# Session Report — 2026-04-01

## Summary

Massive session covering Phase 3 completion, Z3 axiom ordering discovery, has_free_var full soundness, vacuous_quant forward proof, and check_subst_atomic_terms strengthening. ~100+ new verified functions. Forward proof count: 8/11 → 9/11.

## What Was Built

### 1. Phase 3: eq_subst Checker Strengthening (COMPLETE)

**Files modified/created:**
- `compspec_halts.rs` — Refactored check_eq_subst_process with named sub-expressions (esb_*), fixed check_axiom_eq_subst_right (swapped x↔y walk), fixed check_eq_subst_step extraction depth
- `compspec_eq_subst_backward.rs` (NEW, 22 verified) — Full backward proof: dispatch, per-variant step helpers, structural induction traversal, BoundedRec unfold + wrapper
- `formula.rs` — eq_subst_compatible spec fn, lemma_subst_eq_subst_compatible, lemma_eq_subst_compatible_reflexive/same_size, lemma_subst_preserves_size, lemma_encode_ge_formula_size
- `compspec_logic_axiom_helpers.rs` — Updated eq_subst_left/right_inner (eq_subst_compatible precondition)
- `compspec_axiom_correct.rs` — Updated callers with assert-forall pattern for existential
- `compspec_dispatchers.rs` — Removed old shortcut

### 2. Z3 Axiom Ordering Discovery

**Critical finding:** Verus emits Z3 axioms in source definition order. Spec functions that reference other spec functions MUST be defined AFTER their dependencies. Otherwise Z3 cannot derive structural equality for the referencing function.

**Applied to:** Reordered all `has_free_var_*` functions (binary_or_quantifier → process_top → step → comp). This fixed a multi-session blocker where `lemma_hfv_unfold` couldn't prove structural equality.

### 3. has_free_var Detection Direction (COMPLETE)

**Files:**
- `compspec_halts.rs` — Fixed fuel to f_enc+1, reordered definitions
- `compspec_hfv_unfold.rs` (NEW, 1 verified) — BoundedRec unfold
- `compspec_free_var_induction.rs` — Updated for f_enc+1 fuel
- `compspec_free_var_detection.rs` (NEW, 6 verified) — Walk, detection wrapper, sound lemma
- `compspec_free_var_detection2.rs` (NEW, 2 verified) — Isolated Eq/In step helpers
- `compspec_free_var_helpers.rs` — Made step_to_process_top and step_found_nonzero pub

**Key result:** `lemma_has_free_var_comp_sound(f, v)` — NO preconditions. `comp == 0 → !has_free_var`.

### 4. vacuous_quant Forward Proof (COMPLETE)

**File:** `compspec_forward_checkers4.rs` (10 verified)

Pattern: `eval_comp(checker, enc) != 0 ∧ exists|f| encode(f) == enc → is_axiom_vacuous_quant(decode(enc))`

Uses structure extraction + decode bridges + has_free_var_comp_sound.

### 5. check_subst_atomic_terms Strengthening (IN PROGRESS)

**Problem found:** The old check_subst_atomic_terms only checked tags (not term positions). Forward soundness impossible without proper term checking.

**New infrastructure (9 verified across 5 files):**
- `check_subst_one_term` spec fn — proper per-term check with t_enc discover/verify
- `csa_*` named sub-expressions — Z3 matching support (like esb_* for eq_subst)
- `compspec_subst_term_eval.rs` (1 verified) — Per-term eval through IfZero chain
- `compspec_subst_extract.rs` (2 verified) — Value extraction for Eq and In
- `compspec_subst_step_helpers2.rs` (2 verified) — Dispatch + term check composition (Part 1)
- `compspec_subst_step_compose.rs` (4 verified) — Result composition (Part 2)
- `compspec_subst_induction2.rs` — Traversal spec functions (subst_state, invariant helper)

### 6. universal_inst Forward Skeleton

**File:** `compspec_forward_checkers5.rs` (7 verified)

Structure extraction + decode bridges done. Needs check_subst_comp forward soundness.

## Key Techniques Discovered

| Technique | When to Use |
|-----------|------------|
| Named spec fn sub-expressions (esb_*, csa_*) | When Z3 can't match complex CompSpec trees — breaks tree into named pieces |
| Definition ordering (dependencies first) | ALL spec fns must be ordered: leaves → composites. Fixes structural equality failures |
| Module isolation (1 function per file) | When rlimit exceeds despite correct proof — sibling body pollution |
| assert-by scoping | Scope intermediate eval facts to prevent ambient context explosion |
| Structural equality bridge | `assert(f() == tree); assert(eval_comp(f(), n) == eval_comp(tree, n));` |
| unpair2 chain for nested pairs | Need explicit `lemma_unpair2_pair` before `lemma_unpair1_pair` for inner components |
| `exists\|f\| encode(f) == enc` precondition | Forward proofs need valid encoding to use encode/decode roundtrips |
| assert-forall for existential extraction | Avoids choose trigger issues: `assert forall\|phi, var\| ... implies compatible by { lemma_subst_compatible(...); }` |
| f_enc + 1 fuel for BoundedRec | Ensures at least 1 traversal step even when encode(f) == 0 |

## What Remains

### Immediate: Extend atomic compose helpers (Step 2 extension)

The compose helpers (`lemma_subst_atomic_eq_result` / `_in_result`) currently prove:
- `unpair1(eval_comp(check_subst_atomic_terms(), n)) == rest`
- `unpair1(unpair2(eval_comp(check_subst_atomic_terms(), n))) != 0`

They need to ALSO prove the exact (te', ts') output matches `subst_state(f, var, encode_term(t), te, ts)`. This requires:
- Evaluating `cs_snd(csa_term2())` to get the state output
- Showing it matches the spec function `subst_state`

**Architecture:** Add a third ensures conjunct to the compose helpers, or write a separate "state extraction" helper.

### Step 3: New backward traversal (~120 lines)

`lemma_subst_traversal2` with ensures:
```rust
let (te', ts') = subst_state(f, var, encode_term(t), te, ts);
compspec_iterate(step, fuel, acc, s)
    == compspec_iterate(step, fuel - cost, pair(rest, pair(1, pair(te', ts'))), s)
```

- Eq/In: Use extended compose helpers (gives exact state)
- Compound: Use existing step helpers (step_not, step_binary, etc.) which preserve (te, ts)
- Quantifier bound: Use existing step helper (preserves te, ts)
- Quantifier free: Use existing step helper + recursive call

**Critical note:** step_eq and step_in from `compspec_subst_induction_steps.rs` have WRONG ensures for the strengthened check (they claim unchanged te/ts). Do NOT use them. Use the new compose helpers directly.

### Step 4: Update backward entry point (~20 lines)

Update `lemma_check_subst_comp_backward()` in `compspec_subst_helpers.rs` to call the new traversal.

### Step 5: Verify backward chain

Check: `compspec_subst_helpers.rs` → `compspec_logic_axiom_helpers.rs` → `compspec_axiom_correct.rs` → `compspec_dispatchers.rs`

### Step 6: Complete universal_inst forward (~30 lines)

Add check_subst_comp forward soundness to `compspec_forward_checkers5.rs`.

### Step 7: Build eq_subst forward (~200 lines)

### Step 8: Phase 6 Assembly (~200 lines)

## File Inventory

### New files this session:
| File | Verified | Purpose |
|------|----------|---------|
| compspec_eq_subst_backward.rs | 22 | eq_subst backward proof |
| compspec_hfv_unfold.rs | 1 | has_free_var_comp unfold |
| compspec_free_var_detection.rs | 6 | has_free_var detection + sound |
| compspec_free_var_detection2.rs | 2 | Isolated atomic step helpers |
| compspec_forward_checkers4.rs | 10 | vacuous_quant forward |
| compspec_forward_checkers5.rs | 7 | universal_inst skeleton |
| compspec_subst_term_eval.rs | 1 | Per-term eval |
| compspec_subst_extract.rs | 2 | Value extraction (Eq + In) |
| compspec_subst_step_helpers2.rs | 2 | Dispatch + term checks |
| compspec_subst_step_compose.rs | 4 | Result composition |
| compspec_subst_induction2.rs | 0+ | Traversal spec fns (in progress) |

### Modified files:
- compspec_halts.rs (24 verified) — Multiple strengthening changes
- formula.rs (34+ verified) — spec fns + lemmas
- compspec_logic_axiom_helpers.rs (36 verified)
- compspec_axiom_correct.rs (11 verified)
- compspec_dispatchers.rs (4 verified)
- compspec_free_var_induction.rs (7 verified)
- compspec_free_var_helpers.rs — Made 2 fns pub

## Bugs Found and Fixed

1. **check_eq_subst_step x_enc/y_enc extraction** — 2 levels too shallow (3 snds → 4 snds)
2. **check_axiom_eq_subst_right swap direction** — Was identical to left; right axiom needs (y,x) not (x,y)
3. **has_free_var_comp fuel** — Was f_enc (0 for Eq(Var(0),Var(0))); fixed to f_enc+1
4. **Z3 axiom ordering** — Spec fn definitions must follow dependency order
5. **check_subst_atomic_terms simplified** — Only checked tags, not terms; strengthened with check_subst_one_term
6. **check_subst_atomic_terms var extraction** — 3 snds → 4 snds (same bug pattern as #1)

## Estimated Remaining Work

~400 lines across Steps 2-extension through 8, spanning 1-2 focused sessions.
