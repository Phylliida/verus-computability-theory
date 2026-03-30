# Session Report — 2026-03-30

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

### Summary of remaining work

| Item | Lines | Difficulty |
|------|-------|------------|
| check_logic_axiom correctness | ~80 | Hard (11 schemas) |
| check_zfc_axiom correctness | ~40 | Medium (7 equality + replacement) |
| check_line dispatch | ~30 | Medium |
| ASSUME #3 wiring | ~15 | Easy |
| ASSUME #4 forward direction | ~100 | Hard (decoding) |
| **Total** | **~265** | |

### Key lessons learned

1. **Verus spec_fn closures are intensional** — two closures at different program points are different SMT objects. Solution: `compspec_iterate` mutual recursion eliminates closures entirely.

2. **Module trigger pollution is real** — moving proofs to isolated files can fix rlimit/verification failures that seem impossible in the main module.

3. **`by(compute_only)` works for constant CompSpec evaluation** — proved for extensionality axiom. But deeply nested formulas may timeout.

4. **Function splitting is the #1 rlimit optimization** — three splits eliminated 1.3B rlimit (-47%). The SMT solver's superlinear scaling means splitting a 100-line function into 3x 35-line functions can be 10x cheaper.

5. **`pair(a, b) >= a + b`** is the key pairing arithmetic lemma for fuel adequacy proofs.
