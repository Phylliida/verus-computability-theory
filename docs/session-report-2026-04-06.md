# Session Report: 2026-04-05 to 2026-04-06 — Forward Compound Walk

## Summary

Built complete iterate-level forward walk infrastructure (27+ verified functions, 18+ files). The walk handles all 9 Formula variants for `check_subst_comp` forward soundness. The binary case (And/Or/Implies/Iff) is the final remaining piece — all helpers are verified but connecting them hits Z3 wall-clock time limits.

## Architecture

### Iterate-Level Forward Walk

The forward walk operates at the `compspec_iterate` level with arbitrary `(te, ts)` state parameters:

```
proof fn lemma_forward_walk_iterate(
    phi: Formula, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
) -> (t: Term)
    requires
        fuel >= subst_traversal_cost(phi, var),
        unpair1(unpair2(compspec_iterate(check_subst_step(), fuel, entry_state, input))) != 0,
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0 ==> encode_term(t) == te,
    decreases phi, 1nat,
```

Key design: `(te, ts)` threading enables binary t-consistency. The `ts != 0 ==> encode_term(t) == te` postcondition chains left → right in binary formulas.

### Mutual Recursion Structure

```
walk_iterate (decreases phi, 1)
  ├── Eq/In: atomic helpers (no recursion)
  ├── Not: step + unfold + IH on *sub (self-recursion)
  ├── Binary: delegates to walk_binary (decreases phi, 0)
  │     └── backward traversal + IH on *right + combine
  └── Quantifier: step + unfold + IH on *sub (self-recursion)
```

### Critical Discovery: Formula Params in Mutual Recursion

**Passing `left: Formula, right: Formula` as parameters to walk_binary causes Z3 termination encoding blowup.** Even with an empty proof body, the function times out at rlimit 100 if it takes Formula sub-term params alongside `phi: Formula` in a mutual recursion group.

**Fix:** walk_binary takes only `phi: Formula` and extracts `*left`/`*right` via `match` inside the body. This way Z3's termination encoding only involves ONE Formula variable per function.

## What's Verified (27+ functions)

### Utility Lemmas (7 verified, `compspec_subst_forward_helpers.rs`)
- `lemma_iterate_valid_zero_contradiction`: combines valid_zero_stable + unpair extraction
- `lemma_subst_valid_zero_stable`: iterate with valid=0, any stack
- `lemma_subst_state_unchanged`: if ts stays 0, state completely unchanged
- `lemma_subst_state_zero_identity`: ts=0 from (0,0) → subst is identity
- `lemma_subst_state_zero_identity_gen`: generalized for any initial te
- `lemma_subst_state_ts_independent`: ts component independent of te
- `lemma_subst_state_ts_monotonic`: ts never goes 1→0

### Step Helpers (3 verified, one file each)
- `lemma_forward_step_not` — Not step evaluation
- `lemma_forward_step_binary` — Binary step evaluation
- `lemma_forward_step_quant` — Quantifier step (bound + free)

### Tag Match (9 verified across 4 files)
- Eq/In iterate-level tag match (4 verified)
- Not tag match (1 verified)
- Binary tag match (1 verified)
- Quantifier tag match (3 verified)

### Iterate-Level Term Evals (2 verified)
- `lemma_forward_term1_iter` — first term with general (te, ts)
- `lemma_forward_term2_iter` — second term

### Iterate-Level Valid Product (6 verified across 2 files)
- Eq valid product != 0 (3 verified)
- In valid product != 0 (3 verified)

### Iterate-Level Atomic Walk (2 verified)
- `lemma_forward_atomic_eq_iter` — Eq case
- `lemma_forward_atomic_in_iter` — In case

### Binary T-Consistency (1 verified)
- `lemma_binary_combine` — uses subst_state invariant + zero_identity + ts_monotonic

### Walk Functions (2 verified)
- `lemma_forward_walk_iterate` — all 9 cases (binary delegated)
- `lemma_forward_walk_binary` — right IH + combine (takes `t_l` as param)

## The Binary Connection Problem

### The Deadlock

The walk architecture requires:
1. `walk_iter` computes `t_l` (left IH) in its binary branch
2. `walk_binary` takes `t_l` and does right IH + combine

**Problem:** Computing `t_l` requires step + unfold + tag check + left IH call (~15 lines) in walk_iter's binary branch. This pushes walk_iter from ~85 lines (verified at rlimit 5000) to ~100 lines → times out.

### What Was Tried

| Approach | Result | Why |
|----------|--------|-----|
| All 9 cases inline in one function | Timeout at rlimit 5000-15000 | ~110 lines, ~50+ assertions |
| Binary in separate file with `left, right: Formula` params | Timeout at rlimit 100 (empty body!) | Formula params in mutual recursion causes Z3 termination encoding blowup |
| Binary in separate file, no Formula params, full iterate requires | Timeout at rlimit 5000-10000 | `compspec_iterate` in requires of BOTH mutual recursive functions doubles Z3 matching work |
| Binary with `t_l` param + match-based requires | **VERIFIED at rlimit 5000** | Iterate only inside `match` block, no Formula params |
| Walk_iter with lean 2-line binary delegation | **VERIFIED at rlimit 5000** | But walk_binary signature must match (t_l param version) |
| Walk_iter with 15-line binary branch (step+unfold+tag+leftIH) | Timeout at rlimit 8000 | Too many `compspec_iterate` terms in Z3 context |
| binary_unfold helper (step+unfold+tag in own file) | Timeout at rlimit 1500+ | Z3 wall-clock slow on `compspec_iterate` terms (~500 rlimit needed but >10min wall clock) |
| binary_unfold with `hide(compspec_iterate)` | Still timeout | The `lemma_compspec_iterate_unfold` call reveals it anyway |
| binary_unfold with pair decomposition hint in requires | Still timeout | Same Z3 wall-clock issue |
| 3-way mutual recursion (walk_iter ↔ walk_binary ↔ binary_right) | Timeout | 3-way recursion makes Z3 encoding even larger |

### Root Cause Analysis

The fundamental issue is **Z3 wall-clock time on `compspec_iterate` terms**:

1. `compspec_iterate(check_subst_step(), fuel, pair(pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)), pair(tag_eq, pair(te, ts))), pair(pe, pair(re, var)))` has **8+ nested `pair` calls** and **12+ free variables**

2. Z3's E-matching engine tries to match this expression against ALL quantified axioms. With `pair` being a heavily-used function, there are many potential matches

3. Each rlimit unit takes longer because Z3 processes complex terms slower — a function needing rlimit ~500-1000 takes >10 minutes of wall-clock time

4. The mutual recursion encoding adds the `compspec_iterate` expression to BOTH functions' Z3 contexts, doubling the matching work

### Key Insight: Why walk_binary with `t_l` Works

The version that verified has:
```
requires
    ({
        match phi {
            And { left, right } | ... => {
                rl == encode(subst(*left, var, t_l)) &&
                ...
                compspec_iterate(...*left...*right...) != 0
            },
            _ => false,
        }
    }),
```

The `compspec_iterate` is INSIDE a `match` block in the requires. Verus/Z3 may encode this differently than a top-level `compspec_iterate` — possibly as a conditional that's only active when the match succeeds. This reduces the number of terms Z3 needs to match against.

## Ideas for Fixing

### 1. Hide `compspec_iterate` globally with selective reveal
Make `compspec_iterate` opaque in the formula/computable module. The iterate unfold lemma reveals it. Functions that just PASS iterate facts between calls don't trigger Z3 matching.

**Risk:** May require changes to the backward direction proofs that currently rely on `compspec_iterate` being transparent.

### 2. Wrapper spec fn for the iterate precondition
Define a spec fn that wraps the iterate validity check:
```
spec fn iterate_valid(phi_enc: nat, result_enc: nat, rest: nat, te: nat, ts: nat, pe: nat, re: nat, var: nat, fuel: nat) -> bool {
    unpair1(unpair2(compspec_iterate(...))) != 0
}
```
Functions use `iterate_valid(...)` instead of the raw expression. This creates a single term that Z3 matches against, rather than the deeply nested pair expression.

**Risk:** May prevent Z3 from seeing the internal structure needed for the proof.

### 3. Move left IH into walk_binary (put everything in one place)
Have walk_binary do step+unfold+tag+leftIH+rightIH+combine. Its requires is the raw iterate (same as walk_iter). But put the iterate in a `match` block (which seemed to help Z3).

The version with `match`-based requires and NO Formula params verified. Maybe the version with the raw iterate in a `match` block also verifies:
```
requires
    phi matches And{..} || ...,
    ({
        match phi {
            And{..} | ... => { fuel >= cost && iterate != 0 },
            _ => false,
        }
    }),
```

This puts ALL preconditions inside the match, possibly reducing Z3's encoding.

### 4. Increase MCP timeout
The binary_unfold function needs rlimit ~500-1000, which should take seconds. The timeout is wall-clock, suggesting Z3's per-step processing is slow on these terms. A 15-20 minute MCP timeout would likely work.

### 5. Run verification outside MCP
Use the check.sh script or direct cargo verus with a longer timeout. The MCP 10-minute limit is the bottleneck, not the rlimit.

### 6. Reduce term complexity
Replace the deeply nested `pair(pair(pair(...)))` stack expression with a single nat parameter `stack_val` and let Z3 work with the abstract value. The step helpers already produce the stack as a single nat — threading it as-is avoids Z3 having to reason about the internal pair structure.

## Files Created/Modified

### New Files (18)
```
compspec_subst_forward_helpers.rs           (7 verified)
compspec_subst_forward_step_not.rs          (1 verified)
compspec_subst_forward_step_binary.rs       (1 verified)
compspec_subst_forward_step_quant.rs        (1 verified)
compspec_subst_forward_compound_tag.rs      (1 verified)
compspec_subst_forward_binary_tag.rs        (1 verified)
compspec_subst_forward_quant_tag.rs         (3 verified)
compspec_subst_forward_eq_iter_terms.rs     (2 verified)
compspec_subst_forward_eq_iter_valid.rs     (3 verified)
compspec_subst_forward_in_iter_valid.rs     (3 verified)
compspec_subst_forward_eq_iter_tag.rs       (4 verified)
compspec_subst_forward_walk_atomic.rs       (1 verified)
compspec_subst_forward_walk_atomic_in.rs    (1 verified)
compspec_subst_forward_binary_combine.rs    (1 verified)
compspec_subst_forward_walk_iter.rs         (1 verified — with lean binary delegation)
compspec_subst_forward_walk_binary.rs       (1 verified — with t_l param)
compspec_subst_forward_walk_binary_right.rs (WIP — may not be needed)
compspec_subst_forward_binary_unfold.rs     (WIP — step+unfold+tag helper)
```

### Modified Files
- `compspec_subst_step_helpers.rs`: made `lemma_subst_dispatch_compound` public
- `compspec_subst_induction2.rs`: made `lemma_subst_state_invariant` public
- `lib.rs`: registered 18+ new modules

## Remaining Work After Binary Fix

1. **Update `compspec_subst_forward.rs`** — wire iterate walk to check_subst_comp entry point
2. **Wire into `compspec_forward_checkers5.rs`** — universal_inst forward
3. **Build eq_subst forward** (~200 lines, different checker)
4. **Forward logic axiom dispatcher** (~100 lines)
5. **Assembly** (~200 lines) — forward check_line, wire into lemma_halts_comp_correct, remove ASSUME #4
