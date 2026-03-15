use vstd::prelude::*;
use crate::formula::*;
use crate::proof_system::*;
use crate::zfc::*;
use crate::computation::*;
use crate::ceer::*;

verus! {

// ============================================================
// ZFC provable equivalence on formulas
// ============================================================

/// Two formulas are ZFC-equivalent if their biconditional is provable in ZFC.
pub open spec fn zfc_equiv(phi: Formula, psi: Formula) -> bool {
    provable_in_zfc(mk_iff(phi, psi))
}

/// Helper predicate for the nat-level witness (used as trigger).
pub open spec fn zfc_equiv_witness(n: nat, m: nat, phi: Formula, psi: Formula) -> bool {
    encode(phi) == n && encode(psi) == m &&
    is_sentence(phi) && is_sentence(psi) &&
    zfc_equiv(phi, psi)
}

/// Trigger-friendly wrapper for tuple-based existential.
pub open spec fn zfc_witness_pair(n: nat, m: nat, pair: (Formula, Formula)) -> bool {
    zfc_equiv_witness(n, m, pair.0, pair.1)
}

/// ZFC equivalence lifted to natural numbers via Gödel encoding.
/// For codes of sentences: n ~ m iff the decoded sentences are ZFC-equivalent.
/// For invalid codes or non-sentences: n ~ m iff n == m (identity fallback).
pub open spec fn zfc_equiv_nat(n: nat, m: nat) -> bool {
    if n == m {
        true
    } else {
        exists|pair: (Formula, Formula)|
            #[trigger] zfc_witness_pair(n, m, pair)
    }
}

// ============================================================
// Equivalence relation proofs (formula level)
// ============================================================

/// ZFC equivalence is reflexive: φ ↔ φ is provable in ZFC.
pub proof fn lemma_zfc_equiv_reflexive(phi: Formula)
    ensures
        zfc_equiv(phi, phi),
{
    lemma_provable_iff_refl(phi, |f: Formula| is_zfc_axiom(f));
}

/// ZFC equivalence is symmetric: if φ ↔ ψ provable, then ψ ↔ φ provable.
pub proof fn lemma_zfc_equiv_symmetric(phi: Formula, psi: Formula)
    requires
        zfc_equiv(phi, psi),
    ensures
        zfc_equiv(psi, phi),
{
    lemma_provable_iff_sym(phi, psi, |f: Formula| is_zfc_axiom(f));
}

/// ZFC equivalence is transitive.
pub proof fn lemma_zfc_equiv_transitive(phi: Formula, psi: Formula, chi: Formula)
    requires
        zfc_equiv(phi, psi),
        zfc_equiv(psi, chi),
    ensures
        zfc_equiv(phi, chi),
{
    lemma_provable_iff_trans(phi, psi, chi, |f: Formula| is_zfc_axiom(f));
}

// ============================================================
// Equivalence relation proofs (nat level)
// ============================================================

/// ZFC equivalence on nats is reflexive.
pub proof fn lemma_zfc_equiv_nat_reflexive(n: nat)
    ensures
        zfc_equiv_nat(n, n),
{
}

/// ZFC equivalence on nats is symmetric.
pub proof fn lemma_zfc_equiv_nat_symmetric(n: nat, m: nat)
    requires
        zfc_equiv_nat(n, m),
    ensures
        zfc_equiv_nat(m, n),
{
    if n == m {
        return;
    }
    let ghost p = choose|pair: (Formula, Formula)|
        #[trigger] zfc_witness_pair(n, m, pair);
    let ghost phi = p.0;
    let ghost psi = p.1;

    lemma_zfc_equiv_symmetric(phi, psi);
    let ghost q: (Formula, Formula) = (psi, phi);
    assert(zfc_witness_pair(m, n, q));
}

/// ZFC equivalence on nats is transitive.
pub proof fn lemma_zfc_equiv_nat_transitive(n: nat, m: nat, k: nat)
    requires
        zfc_equiv_nat(n, m),
        zfc_equiv_nat(m, k),
    ensures
        zfc_equiv_nat(n, k),
{
    if n == k {
        return;
    }
    if n == m {
        return;
    }
    if m == k {
        return;
    }
    let ghost p1 = choose|pair: (Formula, Formula)|
        #[trigger] zfc_witness_pair(n, m, pair);
    let ghost phi = p1.0;
    let ghost psi_nm = p1.1;

    let ghost p2 = choose|pair: (Formula, Formula)|
        #[trigger] zfc_witness_pair(m, k, pair);
    let ghost psi_mk = p2.0;
    let ghost chi = p2.1;

    // Both psi_nm and psi_mk encode to m
    lemma_encode_injective(psi_nm, psi_mk);

    lemma_zfc_equiv_transitive(phi, psi_nm, chi);
    let ghost q: (Formula, Formula) = (phi, chi);
    assert(zfc_witness_pair(n, k, q));
}

// ============================================================
// Deferred: ZFC equivalence is a CEER
// ============================================================

/// ZFC provable equivalence is computably enumerable.
/// Proof deferred: requires building a register machine that systematically
/// enumerates all valid ZFC proofs and outputs pairs (encode(φ), encode(ψ))
/// when it finds a proof of φ ↔ ψ.
#[verifier::external_body]
pub proof fn lemma_zfc_equiv_is_ce()
    ensures
        is_ce(|n: nat| exists|m: nat| m != n && zfc_equiv_nat(n, m)),
{
    assume(false);
}

/// ZFC provable equivalence is a CEER.
/// Proof deferred: depends on lemma_zfc_equiv_is_ce above.
#[verifier::external_body]
pub proof fn lemma_zfc_equiv_is_ceer()
    ensures
        exists|e: CEER| ceer_wf(e) &&
            forall|n: nat, m: nat| ceer_equiv(e, n, m) <==> zfc_equiv_nat(n, m),
{
    assume(false);
}

} // verus!
