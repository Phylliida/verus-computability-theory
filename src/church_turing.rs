use vstd::prelude::*;
use crate::machine::*;
use crate::zfc_enumerator::*;

verus! {

/// Reduced Church-Turing axiom: a register machine exists that implements
/// the proof-checking enumerator.
///
/// Justification: `enumerator_spec` checks a decidable predicate (proof validity
/// is a finite syntactic check) and performs primitive recursive operations
/// (Cantor pairing, formula encoding). Any such function is implementable
/// by a register machine per the Church-Turing thesis.
///
/// This replaces the previous `axiom_zfc_ceer` which bundled both the
/// mathematical fact (proof enumeration captures ZFC equivalence) and
/// the computational claim (a register machine can do it). Now the
/// mathematical part is fully verified, and only the computational part
/// remains axiomatic.
#[verifier::external_body]
pub proof fn axiom_enumerator_machine_exists()
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            // Halts iff enumerator_spec produces output
            (forall|s: nat| halts(rm, s) <==> enumerator_spec(s).is_some()) &&
            // When it halts, registers match the spec output
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==>
                enumerator_spec(s) == Some((
                    run(rm, initial_config(rm, s), fuel).registers[1],
                    run(rm, initial_config(rm, s), fuel).registers[2]
                ))),
{
}

} // verus!
