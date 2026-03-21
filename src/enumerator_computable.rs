use vstd::prelude::*;
use crate::machine::*;
use crate::computable::*;
use crate::zfc_enumerator::*;

verus! {

// ============================================================
// Deriving axiom_enumerator_machine_exists from CompSpec
// ============================================================
//
// We show that enumerator_spec is CompSpec-definable, then
// apply axiom_computable_partial_fn to get a register machine.
//
// Phase 1: CompSpec terms are placeholders with assume(false)
// matching proofs. The derivation structure is verified.
//
// Phase 2 (future): Build real CompSpec terms decomposing
// enumerator_spec into primitive recursive operations:
//   - Cantor unpairing (inverse of pair)
//   - Proof decoding (inverse of encode_proof)
//   - Proof validation (is_valid_proof check)
//   - Conclusion checking + pair extraction

/// The halting predicate as a CompSpec.
/// When verified (Phase 2): eval_comp(enumerator_halts_comp(), s) != 0
/// iff is_valid_iff_proof_code(s).
///
/// Phase 1: placeholder.
pub open spec fn enumerator_halts_comp() -> CompSpec {
    // TODO Phase 2: build real CompSpec for is_valid_iff_proof_code
    CompSpec::Const { value: 0 }
}

/// First output component as a CompSpec.
/// When verified (Phase 2): eval_comp(enumerator_output1_comp(), s) == encode(phi)
/// where phi is the left side of the proven iff.
///
/// Phase 1: placeholder.
pub open spec fn enumerator_output1_comp() -> CompSpec {
    // TODO Phase 2: build real CompSpec for output extraction
    CompSpec::Const { value: 0 }
}

/// Second output component as a CompSpec.
/// When verified (Phase 2): eval_comp(enumerator_output2_comp(), s) == encode(psi)
/// where psi is the right side of the proven iff.
///
/// Phase 1: placeholder.
pub open spec fn enumerator_output2_comp() -> CompSpec {
    // TODO Phase 2: build real CompSpec for output extraction
    CompSpec::Const { value: 0 }
}

/// Phase 2 proof obligation: halts_comp matches is_valid_iff_proof_code.
#[verifier::external_body]
proof fn lemma_halts_comp_matches()
    ensures
        forall|s: nat| eval_comp(enumerator_halts_comp(), s) != 0
            <==> is_valid_iff_proof_code(s),
{
    // Phase 2: replace with real proof once CompSpec terms are built
}

/// Phase 2 proof obligation: output comps match enumerator_spec outputs.
#[verifier::external_body]
proof fn lemma_output_comp_matches()
    ensures
        forall|s: nat| is_valid_iff_proof_code(s) ==> {
            let spec_out = enumerator_spec(s).unwrap();
            &&& eval_comp(enumerator_output1_comp(), s) == spec_out.0
            &&& eval_comp(enumerator_output2_comp(), s) == spec_out.1
        },
{
    // Phase 2: replace with real proof once CompSpec terms are built
}

/// Derive axiom_enumerator_machine_exists from the reduced CTT axiom.
pub proof fn lemma_derive_enumerator_machine()
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> enumerator_spec(s).is_some()) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==>
                enumerator_spec(s) == Some((
                    run(rm, initial_config(rm, s), fuel).registers[1],
                    run(rm, initial_config(rm, s), fuel).registers[2]
                ))),
{
    // Step 1: Get the register machine from the reduced axiom
    axiom_computable_partial_fn(
        enumerator_halts_comp(),
        enumerator_output1_comp(),
        enumerator_output2_comp(),
    );

    let rm = choose|rm: RegisterMachine|
        machine_wf(rm) && rm.num_regs >= 3 &&
        (forall|s: nat| halts(rm, s) <==> eval_comp(enumerator_halts_comp(), s) != 0) &&
        (forall|s: nat, fuel: nat|
            run_halts(rm, initial_config(rm, s), fuel) ==> (
                run(rm, initial_config(rm, s), fuel).registers[1] == eval_comp(enumerator_output1_comp(), s) &&
                run(rm, initial_config(rm, s), fuel).registers[2] == eval_comp(enumerator_output2_comp(), s)
            ));

    // Step 2: Bridge to enumerator_spec
    lemma_halts_comp_matches();
    lemma_output_comp_matches();

    // Step 3: Show the machine satisfies the enumerator_spec ensures
    assert forall|s: nat| halts(rm, s) <==> enumerator_spec(s).is_some() by {
        // halts(rm, s) <==> eval_comp(halts_comp, s) != 0 <==> is_valid_iff_proof_code(s)
        // enumerator_spec(s).is_some() <==> is_valid_iff_proof_code(s)
    };

    assert forall|s: nat, fuel: nat|
        run_halts(rm, initial_config(rm, s), fuel) ==>
        enumerator_spec(s) == Some((
            run(rm, initial_config(rm, s), fuel).registers[1],
            run(rm, initial_config(rm, s), fuel).registers[2]
        ))
    by {
        if run_halts(rm, initial_config(rm, s), fuel) {
            // rm halts → halts(rm, s) → enumerator_spec(s).is_some()
            assert(halts(rm, s));
            assert(enumerator_spec(s).is_some());
            let spec_out = enumerator_spec(s).unwrap();
            // registers match eval_comp, which matches spec_out
            assert(run(rm, initial_config(rm, s), fuel).registers[1] == eval_comp(enumerator_output1_comp(), s));
            assert(run(rm, initial_config(rm, s), fuel).registers[2] == eval_comp(enumerator_output2_comp(), s));
            assert(eval_comp(enumerator_output1_comp(), s) == spec_out.0);
            assert(eval_comp(enumerator_output2_comp(), s) == spec_out.1);
        }
    };
}

} // verus!
