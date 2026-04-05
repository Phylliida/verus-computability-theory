# Session Report: 2026-04-05 — Forward Compound Walk Infrastructure

## Summary

Built the complete infrastructure for the iterate-level forward walk (check_subst forward soundness). All helper lemmas verified. The main walk function is structured with all 9 formula cases but needs rlimit optimization to verify.

## What Was Built (23+ verified functions)

### Utility Lemmas (`compspec_subst_forward_helpers.rs` — 6 verified)
- `lemma_subst_valid_zero_stable`: iterate with valid=0 preserves acc for ANY stack
- `lemma_subst_state_unchanged`: if ts stays 0, state is completely unchanged
- `lemma_subst_state_zero_identity`: ts=0 from (0,0) → subst is identity
- `lemma_subst_state_zero_identity_gen`: generalized for any initial te
- `lemma_subst_state_ts_independent`: ts component independent of te
- `lemma_subst_state_ts_monotonic`: ts never goes from 1 back to 0

### Forward Step Helpers (one per file for rlimit)
- `compspec_subst_forward_step_not.rs` — Not step output (1 verified)
- `compspec_subst_forward_step_binary.rs` — Binary step output (1 verified)
- `compspec_subst_forward_step_quant.rs` — Quantifier step (bound+free) (1 verified)

### Tag Match (iterate-level + check_subst_comp level)
- `compspec_subst_forward_eq_iter_tag.rs` — Eq + In iterate tag match (4 verified)
- `compspec_subst_forward_compound_tag.rs` — Not tag match (1 verified)
- `compspec_subst_forward_binary_tag.rs` — Binary tag match (1 verified)
- `compspec_subst_forward_quant_tag.rs` — Quantifier tag match (3 verified)

### Iterate-Level Term Evals
- `compspec_subst_forward_eq_iter_terms.rs` — v1/te1/ts1/v2 with general (te,ts) (2 verified)

### Iterate-Level Valid Product
- `compspec_subst_forward_eq_iter_valid.rs` — Eq valid product != 0 (3 verified)
- `compspec_subst_forward_in_iter_valid.rs` — In valid product != 0 (3 verified)

### Iterate-Level Atomic Walk
- `compspec_subst_forward_walk_atomic.rs` — Eq atomic forward (1 verified)
- `compspec_subst_forward_walk_atomic_in.rs` — In atomic forward (1 verified)

### Binary T-Consistency
- `compspec_subst_forward_binary_combine.rs` — t-consistency using subst_state (1 verified)

### Main Walk (WIP)
- `compspec_subst_forward_walk_iter.rs` — all 9 cases structured, times out at rlimit 5000

## Key Architectural Decisions

### Iterate-Level Walk (not check_subst_comp level)
The forward walk operates at the iterate level with arbitrary (te, ts) state parameters. This avoids the need for input independence when handling binary formulas — recursive calls pass the SAME (pe, re) input, so the sub-iterate's valid != 0 follows directly from the parent iterate's decomposition.

### Binary T-Consistency via subst_state
For Binary(left, right):
1. IH on left gives t_left with state (te_left, ts_left) = subst_state(left, ...)
2. Backward traversal decomposes iterate
3. IH on right gives t_right with ts_left != 0 → encode_term(t_right) == te_left
4. If ts_left != 0: t_right == t_left (from encode_term equality)
5. If ts_left == 0: left has no free var → subst_state_zero_identity_gen

### Per-File Isolation (rlimit tips)
Every CompSpec evaluation helper is in its own file. The main walk imports only function signatures, not bodies.

## Current Blocker: Walk Function rlimit

The main walk function (`lemma_forward_walk_iterate`) has all 9 formula cases:
- Eq/In: 3 calls each (tag match + atomic helper)
- Not: 7 calls (step + unfold + tag contradiction + IH + combine)
- Binary (or-pattern for 4 variants): 12 calls (step + unfold + tag contradiction + IH×2 + backward traversal + combine)
- Quantifier (or-pattern for 2 variants): 10 calls (step + unfold + bound/free split + IH + combine)

Total: ~45 lemma calls in one function. Times out at rlimit 5000.

### Potential Fixes
1. **Extract tag contradiction into helper**: The `if tag_eq == 0 { valid_zero_stable; unpair; unpair; }` pattern repeats in every branch. Extract into a one-call helper.
2. **Assert-by scoping**: Scope each branch's step + unfold into assert-by blocks to prevent cross-branch pollution.
3. **Split into two functions**: Handle {Eq, In, Not} in one function and {Binary, Quantifier} in another using `decreases phi, flag`.
4. **Reduce imports**: Currently importing many modules; try more targeted imports.

## Remaining Work to Remove ASSUME #4

1. **Get walk function to verify** (current blocker)
2. **Update check_subst_comp forward entry point** (`compspec_subst_forward.rs`) to call the iterate walk
3. **Wire into compspec_forward_checkers5.rs** (universal_inst forward)
4. **Build eq_subst forward** (~200 lines, uses different checker)
5. **Forward logic axiom dispatcher** (~100 lines)
6. **Assembly** (~200 lines) — forward check_line, wire into lemma_halts_comp_correct, remove ASSUME #4

## Files Modified (not in new files)
- `src/compspec_subst_step_helpers.rs`: made `lemma_subst_dispatch_compound` public
- `src/compspec_subst_induction2.rs`: made `lemma_subst_state_invariant` public
- `src/lib.rs`: registered ~15 new modules
