# Session Report — 2026-03-31 (ASSUME #3 Removed + Forward Direction Infrastructure)

## Summary

**ASSUME #3 fully removed** — replacement axiom checker proved, fixed-axiom restriction lifted. The backward direction of `lemma_halts_comp_correct` is now fully verified.

**Forward direction (ASSUME #4) infrastructure largely built**: decoding (Phases 0-2), 8/11 checker forward proofs (Phase 4), iteration forward (Phase 5). Remaining: eq_subst checker strengthening (Phase 3) + 3 checker forward proofs + assembly.

## New Verified Functions (~50 total this session)

### ASSUME #3 Removal
| File | Verified | Description |
|------|----------|-------------|
| `compspec_replacement_helpers.rs` | 14 | Replacement axiom checker correctness (33 checks) |
| `compspec_dispatchers.rs` | +1 | `lemma_check_zfc_axiom_correct` (full ZFC dispatch) |
| `compspec_check_line_helpers.rs` | 6 (modified) | Removed fixed-axiom restriction |
| `compspec_halts.rs` | 24 (modified) | Removed fixed-axiom precondition |

### Decoding Infrastructure (Phases 0-2)
| File | Verified | Description |
|------|----------|-------------|
| `pairing.rs` | +6 | pair_surjective, unpair bounds |
| `formula.rs` | +5 | decode_formula (via termination), roundtrips |
| `proof_encoding.rs` | +8 | decode_justification/line/nat_seq/proof, roundtrips |

### Forward Checker Proofs (Phase 4)
| File | Verified | Description |
|------|----------|-------------|
| `compspec_forward_structure.rs` | 4 | Structure extraction: identity, eq_refl, iff_elim_left, iff_intro |
| `compspec_forward_structure2.rs` | 5 | iff_elim_right + cs_and_nonzero helpers |
| `compspec_forward_structure3.rs` | 2 | hyp_syllogism, quantifier_dist |
| `compspec_forward_checkers.rs` | 3 | identity, eq_refl, zfc_fixed forward |
| `compspec_forward_checkers2.rs` | 7 | iff_elim_left/right, hyp_syl, quant_dist + bridges |
| `compspec_forward_checkers3.rs` | 3 | iff_intro forward + bridges |

### Forward Iteration (Phase 5)
| File | Verified | Description |
|------|----------|-------------|
| `compspec_forward_iteration.rs` | 10 | check_all_lines nonzero → each check_line nonzero |

## Key Techniques Discovered

### 1. `lemma_cs_and_nonzero_left/right` for product nonzero propagation
Z3 can't derive `a*b != 0 → a != 0` for nats inside complex SMT contexts. Extract into standalone helpers using `nonlinear_arith` contradiction.

### 2. Per-constructor decode bridges
`reveal(decode_formula)` unfolds ALL 10 branches, overwhelming Z3. Instead, write per-constructor bridge lemmas (e.g., `decode_implies`, `decode_iff`, `decode_forall`) that reveal only one level.

### 3. Module isolation pattern
Every sibling function body pollutes the SMT context. Each structural helper and each forward proof goes in its own file. The `rlimit tips.md` principle in practice.

### 4. cs_and_nonzero calls scoped to assert-by blocks
Calling all cs_and_nonzero extractions upfront creates too many ambient eval_comp facts. Call them inside assert-by blocks where needed.

### 5. cs_eq argument order matters
CompSpec equality is structural (tree shape), not semantic. `cs_eq(a, b)` is a different CompSpec tree from `cs_eq(b, a)`. Must match the checker definition EXACTLY.

### 6. check_line_product for iteration forward
Define product of check_line results as spec function. Prove iteration computes valid*product by induction. Extract individual factors from nonzero product.

## Remaining Work for ASSUME #4

### Phase 3: Strengthen eq_subst checkers (~300-400 lines)
Build `check_eq_subst_pair` BoundedRec parallel walker. Verify two formula trees differ only at term positions where one has x and other has y. No t_enc accumulator needed.

### Phase 4 remaining (~300-500 lines)
- universal_inst forward (needs check_subst_comp soundness proof)
- vacuous_quant forward (needs has_free_var_comp soundness proof)
- eq_subst_left/right forward (needs Phase 3)

### Phase 6: Assembly (~200-300 lines)
- MP/Gen forward proofs
- check_line dispatch forward (4 justification types)
- check_conclusion_iff_sentence forward
- Wire into lemma_halts_comp_correct
