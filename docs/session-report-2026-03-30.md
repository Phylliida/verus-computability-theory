# Session Report — 2026-03-30 (updated end of session)

## Accomplishments

### 1. Britton's Lemma (verus-group-theory) — COMPLETE
- **194 verified, 0 errors** — Miller's Theorem 3.10 fully formalized
- Removed all placeholders from `britton_lemma_full`
- Key fixes: Tier 2 preconditions changed to `hnn_canonical_state`, RelatorInsert/Delete dispatch, subrange bridging
- Audited clean: zero `assume`, `admit`, or `external_body` on the dependency path

### 2. compspec_halts.rs — 4 assumes → 2 assumes

**ASSUME #1 (has_free_var_sentence) — REMOVED**
- Proved `has_free_var_comp()` returns 0 for sentences (formulas with no free variables)
- Structural induction on Formula with per-tag step correctness (Eq, In, Not, Binary, Quantifier)
- `traversal_cost(f, v)` spec for accurate fuel accounting (quantifier short-circuiting)
- `encode(f) >= traversal_cost(f, v)` for sentences via pairing arithmetic
- 22 verified helpers across 3 new files

**ASSUME #2 (check_is_sentence_backward) — REMOVED**
- Solved fundamental Verus `spec_fn` closure identity problem
- Refactored `eval_comp` to use `compspec_iterate` (closure-free mutual recursion with lex decreases)
- `lemma_eval_bounded_rec` trivially bridges eval_comp to compspec_iterate
- Pattern reusable for ALL BoundedRec-based proofs

### 3. ASSUME #3 (check_all_lines) — Framework built
- 19 verified helpers in `compspec_all_lines_helpers.rs`
- Complete BoundedRec iteration framework
- `seq_elem_comp` correctness (element extraction from encoded sequences)
- ModusPonens and Generalization sub-checker correctness VERIFIED
- `ci_formula/just_content/seq/idx` accessor lemmas VERIFIED

### 4. Rlimit optimization (verus-group-theory)
- Split 3 hot functions, fixed 1 pre-existing error
- **Crate: 2,824M → ~1,500M rlimit (-47%), 208s → ~120s wall time (-42%)**
- `lemma_g2_subgroup_prepend` (501M → eliminated)
- `lemma_one_shot_subgroup_prepend` (290M → eliminated)
- `lemma_k3_rd_inside_inv` (159M → ~48M per case)
- `lemma_k3_freeexpand_inside_inv` (pre-existing 30M FAIL → fixed with rlimit(40))

## Key infrastructure built

### computable.rs
- `compspec_iterate(step, count, acc, input)` — closure-free BoundedRec iteration via mutual recursion
- `lemma_eval_bounded_rec` — bridges eval_comp(BoundedRec{...}) to compspec_iterate
- `lemma_compspec_iterate_unfold` — one-step unfolding
- `lemma_iterate_ext` — extensional equality for iterate

### formula.rs
- `has_free_var(f, v)` spec + decomposition lemmas (Not, Binary, Quantifier, Atomic)
- `traversal_cost(f, v)` — actual BoundedRec steps needed (accounts for quantifier skipping)
- `lemma_sentence_encode_ge_cost` — encode(f) >= traversal_cost for sentences
- `lemma_pair_ge_sum` (pairing.rs) — pair(a,b) >= a+b

### compspec_halts.rs
- 6 eval helpers: `lemma_eval_ifzero_then/else`, `lemma_eval_pair`, `lemma_eval_add`, `lemma_eval_pred`, `lemma_eval_lt`

### compspec_free_var_helpers.rs (16 verified)
- `lemma_eval_br_acc` — accumulator extraction
- `lemma_step_to_process_top` — dispatch to process_top when stack non-empty
- `lemma_process_top_tag0/1/2` — Eq, In, Not cases
- `lemma_step_eq/in/not/binary/quantifier_bound/quantifier_free` — complete step correctness

### compspec_free_var_induction.rs (6 verified)
- `lemma_traversal_no_free_var` — structural induction on Formula
- `lemma_csi_empty_stable` — empty stack stability
- `lemma_hfv_found_zero` — found flag stays 0
- `lemma_hfv_unfold` — has_free_var_comp → compspec_iterate
- `lemma_has_free_var_sentence_core` — top-level sentence proof

### compspec_all_lines_helpers.rs (19 verified)
- `lemma_cal_step_done/advance` — step evaluation for empty/non-empty remaining
- `lemma_cal_empty_stable` — iteration stability
- `lemma_cal_iteration` — main iteration (assumes per-line check_line correctness)
- `lemma_cal_unfold` — check_all_lines BoundedRec → compspec_iterate
- `lemma_seq_elem_correct` — sequence element extraction
- `lemma_proof_line_formula` — proof line formula extraction
- `lemma_check_mp_correct` — ModusPonens sub-checker
- `lemma_check_gen_correct` — Generalization sub-checker
- `lemma_ci_formula/just_content/seq/idx_eval` — accessor lemmas

### compspec_axiom_eval.rs (1 verified)
- `lemma_enc_extensionality_eval` — extensionality axiom encoding via `by(compute_only)`

## What remains for zero assumes in verus-computability-theory

### ASSUME #3 — check_all_lines (~150-200 lines remaining)

The iteration framework is done. What's missing is per-line `check_line` correctness:

**check_line tag dispatch** (~30 lines)
- Connect `seq_elem_comp(pair(s, i))` to the encoded proof line
- Route to correct sub-checker based on justification tag (0-3)
- Uses existing `lemma_seq_elem_correct` + IfZero evaluation helpers

**check_logic_axiom correctness** (~80 lines, hardest piece)
- 11 axiom schemas (identity, eq_refl, iff_elim_left/right, iff_intro, hyp_syllogism, quantifier_dist, universal_inst, vacuous_quant, eq_subst_left/right)
- Each schema's `check_axiom_*` CompSpec needs evaluation correctness
- Pattern: for each schema, show the CompSpec pattern matcher recognizes valid instances
- May need per-schema helpers in isolated files (trigger pollution)

**check_zfc_axiom correctness** (~40 lines)
- 7 fixed axioms: eval_comp(enc_X(), input) == encode(X_axiom())
- Pattern proved for extensionality via `by(compute_only)`
- Remaining 6 may need either longer timeout or manual bottom-up evaluation
- `check_replacement_axiom` — most complex, involves substitution checking

**check_line tag dispatch wiring** (~20 lines)
- Connect seq_elem extraction to check_line's IfZero chain
- Route to correct sub-checker and verify nonzero result

**Top-level wiring** (~15 lines)
- Wire cal_unfold + cal_iteration + check_line_valid into lemma_all_lines_check_backward
- Replace the assume

### ASSUME #4 — forward direction of halts_comp_correct (~100 lines)

Fundamentally different from #3: this is a DECODING problem.

Given `eval_comp(halts_comp_term(), s) != 0`, extract that `s` encodes a valid proof.

Approach:
1. `halts_comp_term() = cs_and(cs_nonzero(), cs_and(check_all_lines(), check_conclusion_iff_sentence()))`
2. If the product is nonzero, each factor is nonzero
3. `cs_nonzero(s) != 0` → `s != 0` → non-empty encoding
4. `check_all_lines(s) != 0` → each line validates → valid proof (decode direction)
5. `check_conclusion_iff_sentence(s) != 0` → conclusion is Iff of sentences

Step 4 is hardest: show check_line returning nonzero implies the line IS valid (reverse of ASSUME #3). Needs decoding lemmas for each sub-checker.

### Additional progress (late session)

**ZFC axiom encoding evaluation — 7/7 fixed axioms PROVED**
- All 7 `lemma_enc_X_eval` lemmas verify via `by(compute_only)` individually
- Key: run them ONE AT A TIME (all 7 together times out)
- `compspec_axiom_eval.rs`: extensionality + pairing verified (others need to be added back individually)

**verus-group-theory cleanup**
- Removed 4 dead files: `britton_proof.rs`, `britton_proof_helpers.rs`, `britton_proof_helpers2.rs`, `britton_proof_helpers3.rs` (~23,000 lines)
- Created `britton_infra.rs` with the 5 infrastructure lemmas needed by `britton_via_tower.rs`
- Removed dead `axiom_britton_lemma` + `lemma_hnn_injective` + `lemma_hnn_separates` from `britton.rs`

**verus-group-theory rlimit optimization — 89% reduction**
- Split `lemma_g2_subgroup_prepend` (501M → eliminated), `lemma_one_shot_subgroup_prepend` (290M → eliminated), `lemma_k3_rd_inside_inv` (159M → 48M), `lemma_act_sym_preserves_canonical` (80M → 48M), `lemma_g2_one_shot_step` (51M → 35M)
- Scoped `reveal(presentation_valid)` in `lemma_act_word_eq_g2_one_shot` (50M → 21M)
- Fixed pre-existing `lemma_k3_freeexpand_inside_inv` rlimit failure
- **Final: 2,824M → 308M rlimit, 208s → 37s, 6 errors → 0**

---

## What remains for zero assumes in verus-computability-theory

### Current state: 2 assumes in compspec_halts.rs

```
Line 1752: assume(eval_comp(check_all_lines(), s) != 0);     // ASSUME #3
Line 1809: assume(is_valid_iff_proof_code(s));                // ASSUME #4
```

### ASSUME #3 — check_all_lines (~120 lines remaining)

**What's done (19 verified helpers in compspec_all_lines_helpers.rs):**
- BoundedRec iteration framework: `lemma_cal_unfold`, `lemma_cal_iteration`, `lemma_cal_step_done/advance`, `lemma_cal_empty_stable`
- Sequence element extraction: `lemma_seq_elem_correct`, `lemma_seq_advance_iter`
- Per-line sub-checkers: `lemma_check_mp_correct` (ModusPonens), `lemma_check_gen_correct` (Generalization)
- Accessor lemmas: `lemma_ci_formula/just_content/seq/idx_eval`, `lemma_proof_line_formula`, `lemma_lookup_formula_correct`
- ZFC axiom encoding: 2/7 verified in `compspec_axiom_eval.rs` via `by(compute_only)` (all 7 work individually)

**What remains:**

1. **Add remaining 5 ZFC axiom eval lemmas** to `compspec_axiom_eval.rs` (~10 lines, easy)
   - union, powerset, infinity, foundation, choice — all use same `by(compute_only)` pattern
   - Must add ONE AT A TIME to avoid timeout (each is ~1 line)

2. **`lemma_check_zfc_fixed_axiom`** (~15 lines, easy)
   - Combines all 7 eval lemmas + cs_or chain to show check_zfc_axiom returns nonzero
   - Pattern: for matching axiom, cs_eq returns 1, cs_or chain gives >= 1

3. **`check_replacement_axiom` correctness** (~30 lines, medium)
   - Handles the replacement axiom schema (parameterized, not fixed)
   - `is_replacement_axiom(f)` checks formula matches the replacement schema
   - Needs pattern matching CompSpec evaluation

4. **`check_logic_axiom` correctness** (~50 lines, hard)
   - 11 axiom schemas in check_logic_axiom() = cs_or chain of check_axiom_* functions
   - Each check_axiom_* is a pattern matcher on formula encoding
   - `is_logic_axiom(f)` matches against 11 schemas
   - Same cs_or pattern as ZFC but schemas are more complex (pattern matching, not equality)
   - Key difficulty: each schema involves nested formula structure matching

5. **`check_line` tag dispatch** (~20 lines, medium)
   - Connect `seq_elem_comp(pair(s, i))` → encoded line → tag extraction → sub-checker routing
   - Uses IfZero evaluation helpers (already built)
   - Needs to handle all 4 justification tags (0=LogicAxiom, 1=Assumption, 2=MP, 3=Gen)

6. **Top-level wiring** (~10 lines, easy)
   - In compspec_halts.rs: replace assume with call to cal_unfold + cal_iteration
   - Establish per-line check_line correctness via forall quantifier
   - Uses existing iteration framework

### ASSUME #4 — forward direction (~100 lines)

**Fundamentally different** from #3. Given `eval_comp(halts_comp_term(), s) != 0`, extract that `s` encodes a valid proof.

`halts_comp_term() = cs_and(cs_nonzero(), cs_and(check_all_lines(), check_conclusion_iff_sentence()))`

If the product is nonzero, each factor is nonzero. Need to show each factor being nonzero implies the corresponding property:
- `cs_nonzero(s) != 0` → `s != 0` (trivial)
- `check_all_lines(s) != 0` → valid proof lines (HARD: reverse of #3)
- `check_conclusion_iff_sentence(s) != 0` → conclusion is Iff of sentences

The reverse direction of check_all_lines is the hard part: show that if the CompSpec checker accepts, the proof IS valid. This requires decoding lemmas showing each sub-checker only returns nonzero for genuinely valid justifications.

### Recommended attack order

1. **Add remaining ZFC eval lemmas** (5 min, mechanical)
2. **Wire check_zfc_fixed_axiom** (10 min)
3. **check_line tag dispatch** (30 min)
4. **check_logic_axiom correctness** (1-2 hours, the big one)
5. **check_replacement_axiom** (30 min)
6. **ASSUME #3 top-level wiring** (10 min)
7. **ASSUME #4 forward direction** (2-3 hours, separate technique)

### Key techniques to reuse

- **`by(compute_only)`** for constant CompSpec evaluation (ZFC axioms)
- **`lemma_eval_ifzero_then/else`** for tag dispatch decomposition
- **`lemma_eval_bounded_rec` + `compspec_iterate`** for any BoundedRec unfolding
- **Module isolation** for trigger pollution (put new helpers in separate files)
- **`assert-by` scoping** for `reveal(presentation_valid)` and `assert forall` (rlimit optimization)

### Key lessons learned

1. **Verus spec_fn closures are intensional** — two closures at different program points are different SMT objects. Solution: `compspec_iterate` mutual recursion eliminates closures entirely.

2. **Module trigger pollution is real** — moving proofs to isolated files can fix rlimit/verification failures that seem impossible in the main module.

3. **`by(compute_only)` works for constant CompSpec evaluation** — but only one axiom at a time (combined verification times out).

4. **Function splitting is the #1 rlimit optimization** — superlinear SMT scaling means 3x smaller = 10x faster. Scoping `reveal` and `assert forall` via `assert-by` gives similar wins without structural changes.

5. **`pair(a, b) >= a + b`** is the key pairing arithmetic lemma for fuel adequacy proofs.
