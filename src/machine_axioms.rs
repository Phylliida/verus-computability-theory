use vstd::prelude::*;
use crate::machine::*;
use crate::computation::*;
use crate::ceer::*;
use crate::zfc_ceer::*;

verus! {

/// Axiom 1: Sequential composition of register machines.
///
/// Given two machines m1 and m2, there exists m3 that halts on n iff BOTH m1 and m2 halt on n.
///
/// Construction sketch: Allocate registers for both machines plus a spare for the saved input.
/// Copy input to spare register. Run m1's instructions (with register offsets adjusted).
/// If m1 halts (pc falls off end), restore saved input to m2's input register, clear m2's
/// other registers, then run m2's instructions. m3 halts iff both sub-computations halt.
#[verifier::external_body]
pub proof fn axiom_sequential_composition(m1: RegisterMachine, m2: RegisterMachine)
    requires
        m1.num_regs > 0,
        m2.num_regs > 0,
    ensures
        exists|m3: RegisterMachine| m3.num_regs > 0 &&
            forall|n: nat| #[trigger] halts(m3, n) <==> (halts(m1, n) && halts(m2, n)),
{
}

/// Axiom 2: Dovetailing (interleaved simulation) of register machines.
///
/// Given two machines m1 and m2, there exists m3 that halts on n iff EITHER m1 or m2 halts on n.
///
/// Construction sketch: Maintain a step counter and two sets of simulated registers.
/// Use a dispatch table to alternate: run one step of m1, then one step of m2.
/// After each step, check if the sub-machine has halted. Halt m3 when either halts.
/// The step counter increments each round, ensuring progress.
#[verifier::external_body]
pub proof fn axiom_dovetail(m1: RegisterMachine, m2: RegisterMachine)
    requires
        m1.num_regs > 0,
        m2.num_regs > 0,
    ensures
        exists|m3: RegisterMachine| m3.num_regs > 0 &&
            forall|n: nat| #[trigger] halts(m3, n) <==> (halts(m1, n) || halts(m2, n)),
{
}

/// Axiom 3: ZFC proof enumeration generates a CEER.
///
/// There exists a well-formed CEER whose declared_equiv relation exactly matches
/// ZFC provable equivalence on Gödel codes of sentences (for distinct codes).
///
/// Construction sketch: Systematically enumerate all finite strings over the proof alphabet.
/// For each string, check if it constitutes a valid ZFC proof (this is decidable — just
/// verify each inference step). If the proven formula has the form φ ↔ ψ where φ and ψ
/// are sentences, output the pair (encode(φ), encode(ψ)). This enumerates exactly the
/// pairs of Gödel codes of ZFC-equivalent sentences.
#[verifier::external_body]
pub proof fn axiom_zfc_ceer()
    ensures
        exists|e: CEER| ceer_wf(e) &&
            (forall|n: nat, m: nat| n != m && zfc_equiv_nat(n, m) ==> declared_equiv(e, n, m)) &&
            (forall|n: nat, m: nat| declared_equiv(e, n, m) ==> zfc_equiv_nat(n, m)),
{
}

/// Axiom 4: CEER nontrivial class projection is CE.
///
/// For any well-formed CEER e, the set {n | ∃m≠n. declared_equiv(e, n, m)} is CE.
///
/// Construction sketch: Enumerate stages s = 0, 1, 2, ... On input n, run the enumerator
/// on each stage. If stage s halts with declared pair (a, b) where a ≠ b, record both a
/// and b as having nontrivial equivalence classes. Halt on input n when n is recorded.
/// This is a standard dovetailing argument over the stage enumeration.
#[verifier::external_body]
pub proof fn axiom_ceer_nontrivial_ce(e: CEER)
    requires
        ceer_wf(e),
    ensures
        is_ce(|n: nat| exists|m: nat| m != n && declared_equiv(e, n, m)),
{
}

} // verus!
