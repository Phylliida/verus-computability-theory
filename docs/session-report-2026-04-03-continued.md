# Session Report — 2026-04-03 (Continued)

## Summary

Major session completing the backward chain, fixing a checker soundness gap, and building the forward soundness proof for atomic formulas (Eq/In). ~20 new verified functions across 10 isolated files. The hardest part of the forward soundness (per-term constraint analysis at the CompSpec evaluation level) is done.

## What Was Built

### 1. Backward Chain Completion

- **Exact state tracking** — Parameterized all helpers over `i: nat` (was hardcoded 0), strengthened per-term eval to `v == 1` (was `!= 0`), extended compose helpers with exact result `pair(rest, pair(1, state))`.
- **step_eq_exact / step_in_exact** (compspec_subst_atomic_exact.rs, 3 verified) — One iterate step for Eq/In with exact `subst_state` output.
- **Backward traversal** (compspec_subst_induction2.rs, 3 verified) — Fixed Eq/In arms.
- **Backward entry point** (compspec_subst_helpers.rs, 5→7 verified) — Updated for exact state + general stability.

### 2. check_subst_comp Fuel Soundness Fix

**Bug:** When `phi_enc == 0` (Eq(Var(0), Var(0))), fuel was 0 → 0 iterations → checker accepted ANY result without checking. Same bug pattern as has_free_var.

**Fix:** Changed fuel from `phi_enc` to `phi_enc + 1` in check_subst_comp definition. Deleted dead `lemma_check_subst_comp_zero_fuel`. Made `lemma_check_subst_unfold` pub. Full backward chain re-verified (102 functions, 0 errors).

### 3. Forward Soundness — Atomic Eq/In (COMPLETE)

The forward soundness for check_subst_comp proves: if the checker accepts `(phi_enc, result_enc, var)`, then `result == subst(phi, var, t)` for some `t`. Built for atomic formulas (Eq and In).

**Architecture — 10 isolated files:**

| File | Verified | Purpose |
|------|----------|---------|
| `compspec_subst_forward_extract.rs` | 1 | General sub-expression eval for any (phi_node, result_node) entry |
| `compspec_subst_forward_term_eval.rs` | 1 | General per-term IfZero chain eval (no correctness requirements) |
| `compspec_subst_forward_eq_terms.rs` | 1 | Evaluates v1/te1/ts1/v2 for atomic case |
| `compspec_subst_forward_eq_valid.rs` | 1 | Valid product + empty-stack stability → valid != 0 |
| `compspec_subst_forward_eq.rs` | 1 | Main Eq constraints: v!=0 → (a!=var→ra==a), etc. |
| `compspec_subst_forward_in.rs` | 1 | Main In constraints (reuses Eq helpers with tag=1) |
| `compspec_subst_forward_tag.rs` | 2 | Tag mismatch contradiction for Eq (tag 0) and In (tag 1) |
| `compspec_subst_forward_atomic.rs` | 2 | Formula-level Eq/In wrappers using decode roundtrip |
| `compspec_subst_forward.rs` | — | Entry point + walk skeleton (compound cases PLACEHOLDER) |

### 4. General Helpers Added

- **General empty-stack stability** (compspec_subst_helpers.rs) — `lemma_subst_empty_stable_general`: works for any valid including 0. Needed for the forward contradiction argument (valid=0 case).
- **Valid-zero step** — `lemma_subst_step_valid_zero`: when valid==0, step returns acc unchanged via first IfZero.

## Key Techniques Learned

### Module Splitting is Essential for CompSpec Evaluation

**The single most important rlimit lesson.** Each function that evaluates CompSpec IfZero chains MUST be in its own file. Sibling function bodies pollute the SMT context with eval_comp facts from deep CompSpec trees, causing exponential blowup.

**Evidence:** The initial monolithic `lemma_forward_eq_constraints` (all evaluation in one function) timed out at 10 minutes. After splitting into 5 files with 1 function each, every file verified at rlimit ≤ 1200 within seconds.

### assert-by Scoping for Multi-Phase Proofs

When a proof function calls multiple heavy helpers, scope each phase in `assert(fact) by { ... }`. Only the asserted fact leaks out; intermediate eval_comp facts stay scoped.

**Pattern:**
```rust
assert(dispatch_result) by { /* dispatch lemma calls */ }
assert(v1 == ... && te1 == ...) by { /* term eval calls */ }
assert(full_valid != 0) by { /* stability + unpair calls */ }
// Now use v1, te1, full_valid in the outer context
```

### decode_formula Roundtrip Avoids Match Explosion

Instead of matching on `result: Formula` (which requires handling 9 variants and proving 8 contradictions), use decode_formula:

```rust
lemma_decode_encode_formula(result);   // result == decode(result_enc)
reveal(decode_formula);                // Z3 sees decode unfolds by tag
lemma_forward_eq_tag_match(phi_enc, result_enc, var);  // tag == 0
// Z3 now knows: result == Eq(Var(ra), Var(rb)) via decode definition
```

This completely avoids the match and the tag contradiction branches.

### General Per-Term Eval (Forward Direction)

The backward per-term eval (`lemma_subst_one_term_valid`) requires correctness preconditions (phi_term == var → result_term == t_val). For the forward direction, these aren't available.

Solution: create a GENERAL eval (`lemma_subst_one_term_eval_general`) with the same proof structure but without correctness requirements. The ensures gives the v/te/ts values as if-else expressions over the input values. The caller then derives constraints from `v != 0`.

### Tag Match via Contradiction

To prove tags match (forward direction), use contradiction: if tags differ, the cs_eq factor in the valid product is 0, making the full valid 0. Then empty-stack stability preserves valid=0, making the checker return 0. This contradicts acceptance.

**Key helper:** General empty-stack stability that works for ANY valid (including 0). The existing `lemma_subst_empty_stable` required valid > 0.

## What Remains

### 1. Compound Forward Walk (~200-300 lines)

The compound cases (Not, Binary, Quantifier) are PLACEHOLDER in the forward walk. They require a **state-parameterized iterate analysis**.

**The challenge:** The checker's `(te, ts)` state propagates between sub-formulas. For binary formulas like `And(left, right)`, the left sub-formula may discover `te` (setting `ts=1`), then the right sub-formula verifies against the discovered `te`. This means recursive calls CAN'T use `check_subst_comp` directly (which resets state to `(0, 0)`).

**Required approach:** The forward walk should operate on the ITERATE, not on check_subst_comp:

```rust
proof fn lemma_forward_walk_iterate(
    phi: Formula, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
)
    requires
        fuel >= subst_traversal_cost(phi, var),
        ts == 0 || te == some_consistent_value,
        // After processing, valid != 0
        unpair1(unpair2(compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(phi), result_enc)+1, rest), pair(1, pair(te, ts))),
            pair(pe, pair(re, var))))) != 0,
        exists|f: Formula| encode(f) == result_enc,
    ensures
        exists|t: Term| result_enc == encode(subst(phi, var, t))
        // AND state propagation properties for chaining
```

**Per-variant details:**

- **Quantifier bound (v == var):** Checker requires exact match → result == phi → trivial. `subst(Forall(v, sub), var, t) == Forall(v, sub)` when `v == var`.

- **Not / Quantifier free (v != var):** One step pushes `(sub_enc, result_sub_enc)`. Remaining fuel processes sub. By induction on sub, `result_sub == subst(sub, var, t)`. So `result == Not(subst(sub, var, t)) == subst(Not(sub), var, t)`.

- **Binary (And, Or, Implies, Iff):** One step pushes two sub-pairs: `(left_enc, result_left_enc)` and `(right_enc, result_right_enc)`. Left processed first, then right. The te/ts state propagates from left to right. By induction on both: `result == Binary(subst(left, var, t), subst(right, var, t)) == subst(Binary(left, right), var, t)`.

**Key subtlety:** The t must be THE SAME for both left and right. This follows from the te/ts state propagation: if left discovers `te=v`, right verifies against `te=v`. So both use the same t.

**Fuel adequacy:** After 1 step consuming the parent node, remaining fuel = phi_enc (for top-level) or less (for nested). Need: `phi_enc >= subst_traversal_cost(sub, var)`. This follows from `encode(Not(sub)) = pair(2, sub_enc) >= 2 + sub_enc >= subst_traversal_cost(sub, var)` (since cost ≤ encode for non-degenerate formulas).

**Architecture suggestion:** Create the iterate-level walk as a SINGLE function (not per-variant), since the backward walk (`lemma_subst_traversal2`) is structured this way. Use assert-by scoping for each variant's step analysis. The function will be large (~150 lines) but self-contained.

### 2. Complete universal_inst Forward (~30 lines)

In `compspec_forward_checkers5.rs`, the TODO at line 208-220 needs:
```rust
lemma_check_subst_comp_forward(encode(phi), encode(result), var);
let t: Term = choose|t: Term| result == subst(phi, var, t);
assert(decode_formula(enc) == mk_implies(mk_forall(var, phi), subst(phi, var, t)));
assert(is_axiom_universal_inst(decode_formula(enc)));
```

### 3. Build eq_subst Forward (~200 lines)

Uses `check_eq_subst_pair()` (different checker from check_subst_comp). The eq_subst parallel walk checks that two formulas differ only at x↔y positions. Needs its own forward analysis, but structurally similar to check_subst_comp forward.

### 4. Forward Logic Axiom Dispatcher (~100 lines)

Reverse of the backward dispatcher: `check_logic_axiom(enc) != 0 → is_logic_axiom(decode(enc))`. Uses cs_or chain unfolding to identify which checker accepted, then calls the appropriate forward proof.

### 5. Assembly (~200 lines)

Wire everything together:
1. Forward check_line: checker accepts → line is valid
2. Use forward check_all_lines (already done)
3. Forward conclusion check
4. Remove ASSUME #4 from `lemma_halts_comp_correct`

## File Inventory

### New files this session (verified):
| File | Verified | Purpose |
|------|----------|---------|
| compspec_subst_atomic_exact.rs | 3 | step_eq/in_exact with subst_state |
| compspec_subst_forward_extract.rs | 1 | General extract for any entry |
| compspec_subst_forward_term_eval.rs | 1 | General per-term eval |
| compspec_subst_forward_eq_terms.rs | 1 | v1/te1/ts1/v2 atomic eval |
| compspec_subst_forward_eq_valid.rs | 1 | Valid product + stability |
| compspec_subst_forward_eq.rs | 1 | Eq constraints |
| compspec_subst_forward_in.rs | 1 | In constraints |
| compspec_subst_forward_tag.rs | 2 | Tag match contradiction |
| compspec_subst_forward_atomic.rs | 2 | Formula-level Eq/In wrappers |
| compspec_subst_forward.rs | — | Walk skeleton (compound PLACEHOLDER) |

### Modified files:
| File | Change |
|------|--------|
| compspec_halts.rs | check_subst_comp fuel = phi_enc + 1 |
| compspec_subst_helpers.rs | pub unfold, general stability, valid-zero step |
| compspec_subst_extract.rs | i parameterization |
| compspec_subst_step_helpers2.rs | i parameterization, v == 1 |
| compspec_subst_step_compose.rs | i parameterization, exact result |
| compspec_subst_term_eval.rs | v == 1 strengthening |
| compspec_subst_induction2.rs | Fixed Eq/In arms |
| lib.rs | New module registrations |
