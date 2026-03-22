# Road to Zero: Proof Status

## Axioms Fully Proved (no assumes, no external_body)

### 1. `axiom_conditional_halt_on_reg0` (computable.rs)
**Proved in:** `conditional_halt.rs` (~350 lines)

Construction: `build_cond_halt(rm)` adds a scratch register, replaces all Halt
with `DecJump{scratch, N}`, appends `DecJump{0, N}` (conditional loop) + `Halt`.

Key techniques:
- Step-by-step simulation (`lemma_step_sim`, `lemma_sim`)
- Reaching-N lemma (`lemma_reaches_n`) — when original halts, new machine reaches pc=N
- At-N behavior: `lemma_at_n_halts` (reg[0]>0 → halts in 2 steps) and
  `lemma_at_n_loops` (reg[0]==0 → infinite loop)
- Fuel composition (`lemma_run_halts_split`, `lemma_run_split`) from conditional_halt.rs

### 2. `axiom_config_words_free_injective` (machine_group_faithful.rs)
**Proved in:** `machine_group_faithful.rs` (~160 lines added)

Bridge lemma: `equiv_in_presentation` (empty relators) → `freely_equivalent`
via derivation induction. Each step is FreeReduce or FreeExpand (RelatorInsert/Delete
impossible with no relators), both preserve `freely_equivalent`.

Config words are reduced (all Gen symbols → no inverse pairs), so
`normal_form(config_word) == config_word`. Equal normal forms → equal sequences →
equal parameters (first symbol gives state, alpha/beta boundary gives counts).

### 3. `axiom_total_multi_output_machine` (computable.rs)
**Proved in:** `multi_output_primitives.rs` + `multi_output_machine.rs` (~950 lines total)

Construction: `build_multi_output(rm_h, rm_1, rm_2)` with triple-distribute
input phase, three embedded sub-machines with register banking, three destructive
copy phases, and final Halt.

Key techniques:
- `mk_dj`/`mk_inc` spec constructors to avoid Verus struct-literal parsing issues
- Triple distribute loop proof (`lemma_triple_dist_inner`)
- Destructive copy loop proof (`lemma_copy_loop_inner`)
- Embedded machine simulation (`lemma_embed_step_sim`, `lemma_embed_reaches_target`)
- 8-phase composition with fuel chaining via `lemma_run_halts_split`/`lemma_run_split`
- File split (primitives vs machine) to avoid Z3 nondeterminism from module trigger pollution

### 4. `axiom_output1_is_prim_rec` (enumerator_computable.rs)
### 5. `axiom_output2_is_prim_rec` (enumerator_computable.rs)
**Proved in:** `compspec_decode.rs` (~300 lines)

CompSpec terms `output1_comp_term()` and `output2_comp_term()` extract the left/right
formula encoding from a valid proof code by:
1. BoundedRec scan to find last element in encoded nat sequence
2. Cantor unpairing chain to extract formula from line, then Iff components

Key infrastructure built:
- `lemma_unpair1_pair`, `lemma_unpair2_pair` in pairing.rs (Cantor pairing round-trip)
- `decode_nat_seq_last`, `lemma_decode_nat_seq_last` in proof_encoding.rs
- BoundedRec scan correctness: input-independence, fuel-sufficiency, convergence
- `lemma_output_eval_chain` traces eval_comp through the full unpairing chain
- `lemma_eval_last_formula_enc` in compspec_eval_helpers.rs (isolated for rlimit)

## Axiom In Progress: `axiom_halts_is_prim_rec`

**Status:** CompSpec term fully constructed (~1200 lines in `compspec_halts.rs`).
Backward direction composition proved. 5 assumes remain in helper lemmas.

### What's built

The CompSpec `halts_comp_term()` checks:
- `cs_nonzero()` — s ≠ 0 (non-empty sequence)
- `check_all_lines()` — BoundedRec iteration validating each proof line
- `check_conclusion_iff_sentence()` — last formula is Iff with sentence sub-formulas

Per-line check (`check_line()`) dispatches on justification tag:
- Tag 0 (LogicAxiom): `check_logic_axiom()` — OR of all 11 axiom schema checks
- Tag 1 (Assumption): `check_zfc_axiom()` — 7 fixed axiom encoding comparisons + Replacement pattern match
- Tag 2 (ModusPonens): `check_modus_ponens()` — line lookup + formula comparison
- Tag 3 (Generalization): `check_generalization()` — line lookup + Forall structure check

Axiom schema checks implemented:
- Pattern-only (7): identity, eq_refl, iff_elim_left, iff_elim_right, iff_intro, hyp_syllogism, quantifier_dist
- With substitution check (2): universal_inst, vacuous_quant (using `check_subst_comp`)
- Partial (2): eq_subst_left, eq_subst_right (structural tag check only — see known issues)

Supporting CompSpec infrastructure:
- `has_free_var_comp()` — stack-based tree traversal for free variable detection
- `check_subst_comp()` — stack-based parallel tree walk for substitution verification
- `check_is_sentence()` — BoundedRec over variables calling has_free_var
- `seq_elem_comp()` — BoundedRec index-based sequence element access
- `cs_and`, `cs_or`, `cs_not`, `cs_eq`, `cs_lt`, `cs_comp`, `cs_pair` — CompSpec combinators
- `enc_extensionality`, `enc_pairing`, ..., `enc_choice` — ZFC axiom encoding constants
- `check_replacement_axiom()` — deep pattern match on Replacement schema structure
- General eval_comp rewriting lemmas (`lemma_eval_fst`, `lemma_eval_snd`, `lemma_eval_comp`, `lemma_eval_eq`, `lemma_eval_cs_and`, `lemma_eval_cs_nonzero`)

### Correctness proof structure

```
lemma_halts_comp_correct()
  ensures is_halts_comp(halts_comp_term())
{
  assert forall|s| eval_comp(halts_comp_term(), s) != 0 <==> is_valid_iff_proof_code(s) by {
    // BACKWARD (valid → nonzero): COMPOSITION PROVED (no assumes)
    //   (a) s != 0: lemma_encode_nat_seq_nonempty ✓
    //   (b) all lines valid: lemma_all_lines_check_backward [ASSUME]
    //   (c) conclusion check: lemma_conclusion_check_backward ✓ (no assumes in this fn)
    //       uses: lemma_eval_last_formula_enc ✓ (in compspec_eval_helpers.rs)
    //       uses: lemma_check_is_sentence_backward [ASSUME chain]
    //   (d) cs_and composition with nonlinear_arith ✓

    // FORWARD (nonzero → valid): [ASSUME]
  }
}
```

### 4 Remaining assumes (down from 5)

**Eliminated:** Assume #2 (`lemma_check_is_sentence_iter`) — fully proved via inductive proof
with `lemma_cis_step_preserves` in `compspec_sentence_helpers.rs`. Key techniques: opaque
`check_is_sentence_step()` + `has_free_var_comp()` to prevent rlimit explosion, eval rewriting
lemmas (`lemma_eval_comp`, `lemma_eval_cs_not`, `lemma_eval_cs_and`) with `assert by` isolation,
and splitting the proof into 4 focused sub-lemmas across a separate module.

| # | Function | Line | What it needs |
|---|----------|------|---------------|
| 1 | `lemma_has_free_var_sentence` | 1453 | Show stack-based tree traversal returns 0 for sentences. Requires inductive argument on formula structure connecting the BoundedRec stack walk to mathematical `free_vars`. |
| 2 | `lemma_check_is_sentence_backward` | 1513 | Connect `eval_comp(check_is_sentence(), f_enc)` to the iterate result. The iterate is PROVEN nonzero (via lemma_check_is_sentence_iter). Only gap: Z3 closure identity — can't match the closure from eval_comp's BoundedRec unfolding with the one in iterate ensures. Possible fix: change eval_comp's BoundedRec case to avoid closures (requires updating compspec_decode proofs). |
| 3 | `lemma_all_lines_check_backward` | 1619 | Show BoundedRec iteration over all proof lines returns nonzero for valid proofs. Requires showing each `check_line` call returns nonzero for each valid justification type. The hardest remaining piece — needs per-justification-type correctness. |
| 4 | Forward direction | 1676 | Show CompSpec returning nonzero implies mathematical validity. Requires showing CompSpec checks are SUFFICIENT (not just necessary). The eq_subst partial check (known issue) blocks this. |

### Known issues

1. **eq_subst_left/right partial check**: Uses structural tag matching only (`cs_const(1)` after verifying Implies(Eq, Implies) tags). Does NOT verify the two substitutions use the same phi and var. This makes the forward direction unsound for formulas matching the tag pattern but not being actual eq_subst axioms.

2. **Module trigger pollution**: The ~1200 lines of CompSpec spec fns in compspec_halts.rs pollute Z3's search space. Solutions used:
   - `compspec_eval_helpers.rs` for eval_comp connecting lemmas
   - `compspec_sentence_helpers.rs` for sentence checking proofs (reduces proof fn body pollution)
   - `#[verifier::opaque]` on `check_is_sentence_step()` and `has_free_var_comp()` to prevent Z3 from diving into BoundedRec trees
   - `assert by { reveal(...); }` for isolated reveal scoping
   - Split proofs into 4+ focused sub-lemmas (`lemma_cis_check_eval`, `lemma_cis_acc_eval`, `lemma_cis_and_eval`, `lemma_cis_step_eval_raw`)
   - Eval rewriting lemmas (`lemma_eval_fst`, `lemma_eval_snd`, `lemma_eval_comp`, `lemma_eval_cs_not`, `lemma_eval_cs_and`) for one-step eval_comp unfolding without deep recursion

3. **Closure identity in iterate**: `iterate` takes a `spec_fn(nat) -> nat` parameter. Two closures `|x| eval_comp(step, x)` written in different locations are not automatically identified as equal by Z3. This prevents connecting `eval_comp(BoundedRec{...}, input)` to `iterate(step_fn, ...)` across function boundaries. Even making `step` opaque doesn't help — Z3 treats each lambda as a unique function symbol regardless. The `bounded_rec_iterate` approach (closure-free iterate) was developed but the connection `eval_comp(BoundedRec{...}) == bounded_rec_iterate(...)` still requires the same closure matching.

## Remaining Critical-Path Axioms

### `axiom_halts_is_prim_rec` (enumerator_computable.rs)
**Status:** In progress (5 assumes remaining, see above)
**Estimated remaining:** ~150 lines of connecting lemmas

### `axiom_comp_spec_total` (computable.rs)
**Status:** Not started. `#[verifier::external_body]`
**Estimated:** ~500-800 lines

Says: Every CompSpec defines a total computable function — there exists a
RegisterMachine that always halts with output = eval_comp(c, input).

How to prove: Build a CompSpec → RegisterMachine compiler by structural induction
on CompSpec. Each case constructs a concrete machine (see ROAD TO ZERO.md for details).

This is the CompSpec-to-machine compiler — systematic but large. Each CompSpec
variant needs its own machine construction + correctness proof. The register
machine infrastructure from axiom_total_multi_output_machine (embedding, copy loops,
simulation) can be reused.

### `axiom_ceer_fp_embedding` (ceer_benign.rs)
**Status:** Not started. `#[verifier::external_body]`
**Estimated:** ~2000+ lines

Higman's Embedding Theorem — the CEER group embeds faithfully in a finitely
presented group. This is the deepest axiom and should be tackled last.

## Off Critical Path (Dead Code)

These axioms have NO callers in the codebase:

- `axiom_machine_hnn_isomorphic` (machine_group.rs) — HNN association isomorphism
- `axiom_machine_group_backward` (machine_group_faithful.rs) — Britton for machine groups

## Key Patterns Learned

### Verus/Z3 patterns
- **Struct literal parsing**: Use `mk_dj`/`mk_inc` spec constructors instead of `Instruction::DecJump{...}` in requires/assert to avoid Verus macro parsing errors
- **Module trigger pollution**: Large spec fn files pollute Z3's search space. Isolate eval_comp proofs in separate small files (compspec_eval_helpers.rs)
- **eval_comp unfolding**: Z3 can't automatically unfold eval_comp through nested CompSpec composition. Build explicit one-step rewriting lemmas (lemma_eval_fst, lemma_eval_snd, etc.)
- **BoundedRec fuel arithmetic**: Add explicit `assert(N * remaining + 1 == N + (N * ((remaining - 1) as nat) + 1))` for Z3
- **nonlinear_arith requires**: `by(nonlinear_arith) requires a >= 1, b >= 1` to prove `a * b >= 1`
- **Closure identity**: Two `|x| f(x)` closures in different locations are not automatically equal. Avoid cross-function iterate matching.

### Architecture patterns
- **File splitting for Z3 stability**: Split large proofs into primitives + composition files (multi_output_primitives.rs + multi_output_machine.rs)
- **BoundedRec for tree recursion**: Use stack-encoded-as-nat + BoundedRec for tree traversal (has_free_var_comp, check_subst_comp)
- **Encoding-level pattern matching**: Check axiom schemas directly on Cantor-paired encodings rather than decoding to Formula structures
- **Fuel composition**: Chain phases via `!run_halts` + `lemma_run_halts_split` for multi-phase register machine proofs

## Files Created/Modified

### New files (verus-computability-theory)
- `src/conditional_halt.rs` — conditional halt construction + proof
- `src/multi_output_primitives.rs` — register machine embedding primitives
- `src/multi_output_machine.rs` — three-machine merge construction + proof
- `src/compspec_decode.rs` — CompSpec output extraction + BoundedRec scan
- `src/compspec_eval_helpers.rs` — isolated eval_comp connecting lemmas
- `src/compspec_halts.rs` — CompSpec proof validator (~1700 lines)
- `src/compspec_sentence_helpers.rs` — sentence checking eval proofs (isolated for rlimit)

### Modified files (verus-computability-theory)
- `src/computable.rs` — removed external_body from axiom_conditional_halt_on_reg0, axiom_total_multi_output_machine
- `src/enumerator_computable.rs` — removed external_body from axiom_output1/2_is_prim_rec
- `src/pairing.rs` — added lemma_unpair1_pair, lemma_unpair2_pair
- `src/proof_encoding.rs` — added decode_nat_seq_last, lemma_decode_nat_seq_last, lemma_encode_nat_seq_structure
- `src/lib.rs` — added module declarations

### Modified files (verus-group-theory)
- `src/machine_group_faithful.rs` — removed external_body from axiom_config_words_free_injective, added free group bridge lemmas
