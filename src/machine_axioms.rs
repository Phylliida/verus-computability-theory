use vstd::prelude::*;
use crate::ceer::*;
use crate::zfc_ceer::*;

verus! {

/// Axiom: ZFC proof enumeration generates a CEER.
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

} // verus!
