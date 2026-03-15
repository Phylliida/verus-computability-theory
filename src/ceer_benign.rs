use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_group::*;
use crate::ceer_two_gen::*;
use verus_group_theory::symbol::*;
use verus_group_theory::word::*;
use verus_group_theory::presentation::*;
use verus_group_theory::presentation_lemmas::*;
use verus_group_theory::benign::*;
use verus_group_theory::quotient::*;
use verus_group_theory::higman_operations::*;

verus! {

// ============================================================
// CEER Relators as Benign Subgroup of F₂
// ============================================================
//
// The CEER image relators (universal_word(a) · inverse(universal_word(b))
// for each declared pair (a,b)) form a recursively enumerable set
// of words in the 2-generator free group F₂ = ⟨x, y⟩.
//
// By Higman's characterization, any R.E. set of relators generates
// a benign subgroup of the free group. This is the core of
// Higman's embedding theorem.
//
// We axiomatize this result since the full proof requires:
// 1. Encoding the CEER enumerator as Higman operations
// 2. Proving each Higman operation preserves benignness
// 3. Composing the operations to get the full R.E. set

/// The image relators of a CEER form a benign subgroup of F₂.
///
/// Specifically: the set of all image_relator(a, b) for declared
/// CEER pairs (a, b) generates a benign subgroup of the
/// 2-generator free group.
///
/// This follows from Higman's characterization: the CEER enumerator
/// is a register machine that recursively enumerates the declared
/// pairs. The corresponding image relators form an R.E. subset of
/// F₂'s word semigroup, and Higman's operations show that R.E.
/// subsets correspond to benign subgroups.
#[verifier::external_body]
pub proof fn axiom_ceer_relators_benign(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|gens: Seq<Word>, witness: BenignWitness|
            // The generators are valid 2-gen words
            (forall|i: int| 0 <= i < gens.len() ==>
                word_valid(#[trigger] gens[i], 2)) &&
            // The witness is valid
            #[trigger] benign_witness_valid(free_group(2), gens, witness) &&
            // The quotient F₂/⟨⟨gens⟩⟩ faithfully captures T_G:
            // Two universal words are equiv in the quotient iff
            // they are equiv in T_G (i.e., iff ceer_equiv holds)
            (forall|n: nat, m: nat|
                #[trigger] equiv_in_presentation(
                    add_relators(free_group(2), gens),
                    universal_word(n),
                    universal_word(m),
                ) <==> ceer_equiv(e, n, m)),
{
}

} // verus!
