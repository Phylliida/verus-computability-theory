# Road to Zero Assumes

All `external_body` and `assume(false)` items across verus-computability-theory
and verus-group-theory (excluding britton_proof.rs assume(false) items which
are tracked separately in the Britton peak elimination work).

## verus-computability-theory: Critical Path

These are on the critical path for `theorem_zfc_equiv_in_fp_group`.

### 1. `axiom_comp_spec_total` (computable.rs)

**Says:** Every CompSpec defines a total computable function — there exists
a RegisterMachine that always halts with output = eval_comp(c, input).

**Difficulty:** Medium-hard (~500-800 lines)

**How to prove:** Build a CompSpec → RegisterMachine compiler by structural
induction on CompSpec. Each case constructs a concrete machine:

| Operation | Machine construction |
|-----------|---------------------|
| Const(v) | Inc reg 0 v times, Halt |
| Id | Copy reg 0 to output, Halt |
| Succ | Inc output, Halt |
| Pred | DecJump (if 0 jump to halt, else dec), Halt |
| Add | Dec one reg, Inc other, loop |
| Mul | Nested loops (add repeated) |
| Comp | Run inner machine, feed result to outer |
| CantorPair | Compute triangular(a+b) + a via loops |
| CantorFst/Snd | Bounded search for triangular inverse |
| IfZero | Branch on register value |
| Eq | Dec both in parallel, check both reach 0 |
| Lt | Dec both, check which reaches 0 first |
| BoundedRec | Loop with counter + accumulator |

Needs helper infrastructure:
- `compile_comp(c: CompSpec) -> RegisterMachine` (spec function)
- Register allocation scheme (each sub-computation uses disjoint registers)
- Instruction offset management for sequential composition
- Correctness proof by structural induction on CompSpec

The hardest cases are CantorPair/Fst/Snd (need triangular number
arithmetic in registers) and BoundedRec (need loop with accumulator).

### 2. `axiom_total_multi_output_machine` (computable.rs)

**Says:** Three total register machines can be merged into one that
places all three results in registers 0, 1, 2.

**Difficulty:** Medium (~150 lines)

**How to prove:** Concrete construction:
1. Allocate disjoint register banks for each sub-machine
2. Copy input to each sub-machine's reg 0
3. Embed instructions sequentially (shift targets by offset)
4. After each sub-machine halts, copy its output to the target register
5. Halt

Needs:
- `shift_instructions(instrs, pc_offset, reg_offset)` helper
- Copy-register subroutine (dec source, inc dest, loop)
- Proof that the composed machine simulates each sub-machine

### 3. `axiom_conditional_halt_on_reg0` (computable.rs)

**Says:** Given a total multi-output machine, construct a partial machine
that halts iff register 0 is nonzero, preserving registers 1 and 2.

**Difficulty:** Easy (~100 lines)

**How to prove:** Append 2 instructions after the total machine:
```
[original instructions...]
N:   DecJump { register: 0, target: N+1 }  //  if reg0 > 0: dec, goto N+1
N+1: Halt                                    //  halt with reg0 decremented
```
Wait, that changes reg0. Better:
```
[original instructions..., replacing all Halt with jump to N]
N:   DecJump { register: 0, target: N }     //  if reg0 == 0: infinite loop
N+1: Halt                                    //  if reg0 > 0: halt
```
Need to show: reg0 != 0 → machine halts at N+1; reg0 == 0 → infinite loop at N.
Registers 1, 2 are untouched by the appended instructions.

### 4. `axiom_halts_is_prim_rec` (enumerator_computable.rs)

**Says:** `is_valid_iff_proof_code` is primitive recursive — there exists
a CompSpec c with eval_comp(c, s) != 0 ⟺ is_valid_iff_proof_code(s).

**Difficulty:** Hard (~300 lines)

**How to prove:** Build a CompSpec term that:
1. Decodes s via Cantor unpairing into a sequence of (formula, justification) pairs
2. For each line, checks the justification:
   - LogicAxiom: check formula matches an axiom schema
   - Assumption: always valid
   - ModusPonens: check referenced lines exist and match
   - Generalization: check referenced line exists
3. Checks the conclusion is Formula::Iff with sentence sub-formulas
4. Returns 1 if all checks pass, 0 otherwise

Requires building CompSpec sub-terms for:
- `decode_nat_seq`: BoundedRec + CantorFst/Snd (inverse of encode_nat_seq)
- `decode_formula`: recursive tag-dispatch via CantorFst (inverse of encode)
- `is_valid_justification`: conditional checks on decoded justification fields
- `is_sentence`: bounded recursion checking free variables
- `conclusion_is_iff_of_sentences`: decode + pattern match

Each sub-term needs a correctness proof showing eval_comp matches the spec function.

### 5. `axiom_output1_is_prim_rec` (enumerator_computable.rs)

**Says:** The first output of enumerator_spec is primitive recursive.

**Difficulty:** Medium (~100 lines, shares infrastructure with #4)

**How to prove:** CompSpec term that decodes s, extracts the conclusion
(last line's formula), pattern-matches Iff{left, right}, and returns
encode(*left). Reuses the decoding infrastructure from #4.

### 6. `axiom_output2_is_prim_rec` (enumerator_computable.rs)

**Says:** The second output of enumerator_spec is primitive recursive.

**Difficulty:** Easy (~50 lines, same as #5 but extracts right instead of left)

### 7. `axiom_ceer_fp_embedding` (ceer_benign.rs)

**Says:** Higman's Embedding Theorem — the CEER group embeds faithfully
in a finitely presented group.

**Difficulty:** Very hard (~2000+ lines)

**How to prove:** Full Higman theorem construction:
1. Build the machine group G_M for the CEER's modular machine
   (already partially done in machine_group.rs)
2. Construct the overgroup K = G_M * F_2 / identification relators
3. Show the CEER subgroup is benign in K
4. Apply the Rope Trick (already proved in higman_operations.rs)
5. Prove faithfulness via Britton's lemma

Major dependencies:
- Working Britton's lemma (britton_proof.rs — has assume(false) items)
- Machine group faithfulness (needs axiom_machine_group_backward)
- HNN association isomorphism (needs axiom_machine_hnn_isomorphic)

This is the deepest axiom and should be tackled last.

## verus-computability-theory: Off Critical Path

These are NOT on the critical path for theorem_zfc_equiv_in_fp_group.

### `axiom_register_to_modular` (modular_machine.rs)

**Says:** Any register machine can be simulated by a modular machine.

**Status:** Unused (dead code). Could be deleted or kept for future use.

**How to prove:** Encode register states as (state, α, β) triples using
prime factorization. Requires number theory library.

### `axiom_ceer_to_modular` (modular_machine.rs)

**Says:** CEER enumerator simulated by modular machine.

**Status:** Unused (dead code). Follows from axiom_register_to_modular.

### `axiom_ceer_relators_benign` (ceer_benign_construction.rs)

**Status:** Off critical path (was part of the old broken decomposition).
Still mathematically interesting but not needed for the main theorem.

### `lemma_quotient_to_two_gen_equiv` (ceer_benign_construction.rs)

**Status:** KNOWN FALSE. See docs/two-gen-backward-bug.md.

### `lemma_two_gen_backward` (ceer_benign_construction.rs)

**Status:** KNOWN FALSE. See docs/two-gen-backward-bug.md.

## verus-group-theory: Non-Britton Items

### `axiom_machine_hnn_isomorphic` (machine_group.rs)

**Says:** The HNN associations for the machine group form isomorphisms
between the associated subgroups.

**Difficulty:** Medium (~200 lines)

**How to prove:** The associations map config_word(s, α, β) to
config_word(s', α', β') via the modular machine's quadruples.
Need to show the map is a well-defined group isomorphism on the
associated subgroups. Requires understanding of the machine_group
construction and HNN extension theory.

### `axiom_config_words_free_injective` (machine_group_faithful.rs)

**Says:** Config words q_s · a^α · b^β are distinct in the free group
when (s, α, β) differ.

**Difficulty:** Easy-medium (~100 lines)

**How to prove:** Config words have the form [Gen(s), Gen(a)^α, Gen(b)^β]
where s, a, b are distinct generator indices. In the free group (no
relators), words with different generator sequences are not equivalent.
This follows from free group normal forms.

### `axiom_machine_group_backward` (machine_group_faithful.rs)

**Says:** If two config words are equivalent in the machine group
presentation, there exists a valid computation trace connecting them.

**Difficulty:** Hard (~500 lines)

**How to prove:** Britton's lemma for the HNN tower of the machine group.
Each HNN level adds one stable letter. Equivalence of config words
implies a "pinch-free" derivation, which corresponds to a valid
computation trace. Requires:
- Working Britton's lemma (from britton_proof.rs)
- Analysis of the specific HNN structure of the machine group
- Extraction of computation trace from the pinch-free derivation

## verus-group-theory: Britton proof helpers

### `britton_proof_helpers2.rs` — 3 assume(false)

Inside-relator edge cases in T-free commutation lemmas
(`lemma_k4_tfree_ri_commute_fe`, `_ri`, `_rd`).

These handle the case where a relator insertion/deletion
overlaps with a T-free step's position (the inserted relator
straddles the boundary). Need careful index arithmetic to show
the steps can still be commuted.

## Recommended Order

Easiest to hardest (excluding britton_proof.rs):

1. **`axiom_conditional_halt_on_reg0`** — ~100 lines, concrete 2-instruction append
2. **`axiom_config_words_free_injective`** — ~100 lines, free group normal form
3. **`axiom_total_multi_output_machine`** — ~150 lines, machine sequencing
4. **`axiom_machine_hnn_isomorphic`** — ~200 lines, HNN association check
5. **`axiom_output2_is_prim_rec`** — ~50 lines (with #4's infra)
6. **`axiom_output1_is_prim_rec`** — ~100 lines (with #4's infra)
7. **`axiom_halts_is_prim_rec`** — ~300 lines, proof decoding in CompSpec
8. **`axiom_comp_spec_total`** — ~500-800 lines, full CompSpec compiler
9. **`axiom_machine_group_backward`** — ~500 lines, Britton for machine groups
10. **`axiom_ceer_fp_embedding`** — ~2000+ lines, full Higman theorem

Items 1-3 are concrete register machine constructions.
Items 4-7 are domain-specific primitive recursiveness proofs.
Item 8 is the CompSpec compiler (systematic but large).
Items 9-10 are deep group theory requiring Britton's lemma.
