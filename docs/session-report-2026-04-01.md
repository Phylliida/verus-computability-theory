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

## What Remains (Precise Continuation Instructions)

### Immediate: Per-arm Eq/In helpers with exact subst_state output

The compose helpers (`lemma_subst_atomic_eq_result` / `_in_result` in `compspec_subst_step_compose.rs`) currently ensure:
- `unpair1(eval_comp(check_subst_atomic_terms(), n)) == rest`
- `unpair1(unpair2(eval_comp(check_subst_atomic_terms(), n))) != 0`
- `eval_comp(check_subst_step(), n) == eval_comp(check_subst_atomic_terms(), n)`

They need to ALSO ensure the EXACT result form:
```
eval_comp(check_subst_step(), n) == pair(rest, pair(1nat, pair(te2, ts2)))
```
where `(te2, ts2) = subst_state(Eq(l,r), var, encode_term(t), te, ts)`.

**Why this is needed:** The traversal chains iterate steps. Compound step helpers (step_not, step_binary, etc.) give exact `pair(rest, pair(1, pair(te, ts)))` form. The Eq/In arms need the same form for chaining.

**How to prove it:**
1. The per-term eval (`lemma_subst_one_term_valid`) already gives exact `(te_out, ts_out)` for each term
2. Term1 output feeds into term2 input (sequential state tracking)
3. `subst_state(Eq(l,r), var, t_enc, te, ts)` = `subst_term_state(r, var, t_enc, subst_term_state(l, var, t_enc, te, ts))`
4. Show: `valid = 1 * (1 * 1) = 1` (each term check returns 1 for valid subst, tags match returns 1)
5. Show: state = `pair(te2, ts2)` from term2's output

**Architecture:** New file `compspec_subst_atomic_exact.rs` (per rlimit tips — isolation). Calls the existing compose helper + adds the exact state extraction.

### Then: Traversal verifies

`lemma_subst_traversal2` in `compspec_subst_induction2.rs`:
- Compound arms (Not, And, Or, Implies, Iff, Forall, Exists): use existing step helpers (step_not, step_binary, etc.) — these preserve (te, ts) and are CORRECT
- Atomic arms (Eq, In): use new per-arm helpers with exact subst_state output
- Ensures: `iterate(fuel, acc, s) == iterate(fuel-cost, pair(rest, pair(1, pair(te2, ts2))), s)`
- rlimit likely needs 800-1500 for the 9-arm function; may need arm extraction per rlimit tips

**CRITICAL: Do NOT use step_eq/step_in from compspec_subst_induction_steps.rs** — they have WRONG ensures for the strengthened check (claim unchanged te/ts). They "verify" only by calling broken helpers.

### Then: Backward entry point + chain verification

Update `lemma_check_subst_comp_backward()` in `compspec_subst_helpers.rs` to call new traversal. Verify chain: `compspec_subst_helpers.rs` → `compspec_logic_axiom_helpers.rs` → `compspec_axiom_correct.rs` → `compspec_dispatchers.rs`.

### Then: Forward proofs + assembly

1. Complete universal_inst forward (`compspec_forward_checkers5.rs`) — structure already done (7 verified)
2. Build eq_subst forward (~200 lines)
3. Phase 6 assembly (~200 lines) → remove the last `assume`

## Key Knowledge for Continuation

| Topic | Detail |
|-------|--------|
| **Definition ordering** | Spec fns MUST be defined AFTER dependencies for Z3 structural equality |
| **Module isolation** | 1 heavy function per file — sibling bodies pollute Z3 context |
| **Named sub-expressions** | csa_* for check_subst, esb_* for eq_subst — enables Z3 matching |
| **Structural equality bridge** | `assert(f() == tree); assert(eval_comp(f(), n) == eval_comp(tree, n));` |
| **unpair2 chain** | Need explicit `lemma_unpair2_pair` before `lemma_unpair1_pair` for inner pair components |
| **step_eq/step_in UNSOUND** | Old helpers in compspec_subst_induction_steps.rs have wrong ensures — DO NOT USE |
| **f_enc+1 fuel** | has_free_var_comp uses f_enc+1 for soundness at encode=0 |
| **exists\|f\| encode(f) == enc** | Forward proofs need valid encoding precondition |
| **subst_state spec fn** | Computes exact (te, ts) after traversal — defined in compspec_subst_induction2.rs |
| **Per-term eval exact state** | lemma_subst_one_term_valid gives `if phi==var { if ts==0 { t_val } else { te } } else { te }` |

## Full File Inventory

### New files (this session):
| File | Verified | Purpose |
|------|----------|---------|
| compspec_eq_subst_backward.rs | 22 | eq_subst backward proof (Phase 3) |
| compspec_hfv_unfold.rs | 1 | has_free_var_comp BoundedRec unfold |
| compspec_free_var_detection.rs | 6 | has_free_var detection + sound (no preconditions) |
| compspec_free_var_detection2.rs | 2 | Isolated Eq/In atomic step helpers for detection |
| compspec_forward_checkers4.rs | 10 | vacuous_quant forward proof |
| compspec_forward_checkers5.rs | 7 | universal_inst forward skeleton |
| compspec_subst_term_eval.rs | 1 | Per-term eval with exact state output |
| compspec_subst_extract.rs | 2 | Value extraction (Eq + In) |
| compspec_subst_step_helpers2.rs | 2 | Dispatch + term checks (Part 1) |
| compspec_subst_step_compose.rs | 4 | Result composition (Part 2) |
| compspec_subst_induction2.rs | 2 | Traversal spec fns + skeleton |

### Bugs found: 6 (all fixed)
1. check_eq_subst_step x_enc/y_enc extraction (3→4 snds)
2. check_axiom_eq_subst_right swap direction ((x,y)→(y,x))
3. has_free_var_comp fuel (f_enc→f_enc+1)
4. Z3 axiom ordering (definition order matters)
5. check_subst_atomic_terms simplified (tags only→full term check)
6. check_subst_atomic_terms var extraction (3→4 snds)
