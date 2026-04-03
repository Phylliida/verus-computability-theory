# Session Report — 2026-04-03

## Summary

Major session completing the backward traversal with exact state tracking, fixing a check_subst_comp soundness gap, and starting the forward soundness proof. The backward chain is now fully verified end-to-end.

## What Was Built

### 1. Exact State Tracking for Eq/In Backward Traversal (COMPLETE)

**Problem:** The old `step_eq`/`step_in` had WRONG ensures — they claimed state `(te, ts)` was preserved through Eq/In steps. But the strengthened `check_subst_atomic_terms` changes state via `check_subst_one_term` (discover/verify t_enc).

**Solution:**
- Parameterized all helpers over `i: nat` (was hardcoded to 0)
- Per-term eval strengthened: `v != 0` → `v == 1` for valid substitutions
- Compose helpers extended: exact result `pair(rest, pair(1, eval_comp(cs_snd(csa_term2()), n)))`
- New `step_eq_exact`/`step_in_exact` with `subst_state` output
- Backward traversal (`lemma_subst_traversal2`) fully verified: 3 verified, 0 errors

**Files modified:**
- `compspec_subst_extract.rs` — Added `i: nat` parameter to extract helpers
- `compspec_subst_step_helpers2.rs` — Added `i: nat`, strengthened ensures `== 1`
- `compspec_subst_step_compose.rs` — Added `i: nat`, exact result form ensures
- `compspec_subst_term_eval.rs` — Changed `!= 0` to `== 1` in ensures
- `compspec_subst_induction2.rs` — Fixed Eq/In arms to use new helpers

**New file:**
- `compspec_subst_atomic_exact.rs` (3 verified) — `step_eq_exact`, `step_in_exact`, `csi_chain`

### 2. Backward Entry Point Update (COMPLETE)

Updated `lemma_check_subst_comp_backward` to use `lemma_subst_traversal2` with exact state. Removed the old zero-fuel special case. 6 verified, 0 errors.

### 3. check_subst_comp Fuel Soundness Fix (COMPLETE)

**Bug found:** When `phi_enc == 0` (Eq(Var(0), Var(0))), fuel was 0 → 0 iterations → checker accepted ANY result_enc without checking. Same bug pattern as the has_free_var fuel issue.

**Fix:** Changed fuel from `phi_enc` to `phi_enc + 1` in `check_subst_comp()`, ensuring at least 1 step even for encode=0. Deleted dead `lemma_check_subst_comp_zero_fuel`.

**Files modified:**
- `compspec_halts.rs` — `check_subst_comp()` fuel = `phi_enc + 1`
- `compspec_subst_helpers.rs` — Updated unfold + backward entry point

**Full backward chain re-verified:** 24 + 36 + 22 + 11 + 4 + 5 = 102 verified, 0 errors.

### 4. Forward Soundness Skeleton (IN PROGRESS)

**File:** `compspec_subst_forward.rs`

Entry point `lemma_check_subst_comp_forward` + walk structure + Eq case skeleton. TODOs marked for per-step constraint analysis.

## Key Techniques

| Technique | Description |
|-----------|-------------|
| i-parameterization | Extract/compose helpers were hardcoded to i=0; parameterized to work with any iterate counter |
| v == 1 strengthening | Per-term eval always produces v=1 for valid subst (not just v != 0) |
| pair_surjective reconstruction | `pair(unpair1(x), unpair2(x)) == x` to reconstruct state pair from components |
| phi_enc + 1 fuel | Same pattern as has_free_var: ensures at least 1 iterate step |

## Verification Status

| File | Verified | Status |
|------|----------|--------|
| compspec_subst_atomic_exact.rs | 3 | NEW, complete |
| compspec_subst_step_compose.rs | 4 | Modified, verified |
| compspec_subst_step_helpers2.rs | 2 | Modified, verified |
| compspec_subst_extract.rs | 2 | Modified, verified |
| compspec_subst_term_eval.rs | 1 | Modified, verified |
| compspec_subst_induction2.rs | 3 | Fixed Eq/In arms |
| compspec_subst_helpers.rs | 5 | Updated backward entry |
| compspec_halts.rs | 24 | Fuel fix |
| compspec_logic_axiom_helpers.rs | 36 | Re-verified |
| compspec_eq_subst_backward.rs | 22 | Re-verified |
| compspec_axiom_correct.rs | 11 | Re-verified |
| compspec_dispatchers.rs | 4 | Re-verified |
| compspec_subst_forward.rs | — | Skeleton only |

## What Remains

### Step 1: Forward Per-Step Analysis (~200 lines)

The forward Eq case needs to EVALUATE check_subst_atomic_terms on a GENERAL input (arbitrary result_enc, not just valid substitution) and show:

1. **Dispatch** (step → atomic_terms): Already works for general input via `lemma_subst_step_dispatch`. Only depends on phi_tag and valid.

2. **Valid product**: `valid = tag_eq * v1 * v2` where:
   - `tag_eq = (phi_tag == result_tag) ? 1 : 0`
   - `v1 = per_term_check(phi_left, result_left, var, te, ts)`
   - `v2 = per_term_check(phi_right, result_right, var, te1, ts1)`

3. **Forward constraint**: If `valid != 0`:
   - `tag_eq != 0` → result has same tag → same Formula variant
   - `v1 != 0` → result_left matches subst property
   - `v2 != 0` → result_right matches subst property

**Architecture:** Create a "general extract" helper that evaluates sub-expressions for arbitrary `(phi_enc, result_enc)` entry (not just `(phi, subst(phi,var,t))`). Then a "general compose" that shows the factored valid product. Then per-term forward constraints.

### Step 2: Forward Walk (~100 lines)

Structural induction combining per-step results. Compound cases (Not, Binary, Quantifier) follow the backward walk's pattern but derive forward constraints.

### Step 3: Forward Entry Point (~30 lines)

Wire the walk into `lemma_check_subst_comp_forward`.

### Step 4: Complete universal_inst Forward (~30 lines)

Use check_subst_comp forward in `compspec_forward_checkers5.rs`.

### Step 5: Build eq_subst Forward (~200 lines)

Uses `check_eq_subst_pair` (different checker from check_subst_comp). Needs its own forward analysis.

### Step 6: Assembly (~200 lines)

- Forward logic axiom dispatcher
- Forward check_line
- Wire into `lemma_halts_comp_correct` forward direction
- Remove ASSUME #4

## Estimated Remaining: ~760 lines across 6 steps
