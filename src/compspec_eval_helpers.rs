use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::proof_system::*;
use crate::proof_encoding::*;
use crate::zfc::*;
use crate::zfc_enumerator::*;
use crate::compspec_decode::*;

verus! {

/// eval_comp(last_formula_enc(), s) extracts the conclusion formula encoding.
/// Same proof chain as lemma_output_eval_chain steps 1-4.
/// Isolated in its own file to avoid module trigger pollution from
/// the large CompSpec definitions in compspec_halts.rs.
pub proof fn lemma_eval_last_formula_enc(s: nat, p: Proof)
    requires
        encode_proof(p) == s,
        p.lines.len() > 0,
        conclusion_is_iff_of_sentences(proof_conclusion(p)),
    ensures
        eval_comp(last_formula_enc(), s) == encode(proof_conclusion(p)),
{
    let n = p.lines.len();
    let conclusion = proof_conclusion(p);
    let last_line = p.lines[n - 1];
    assert(last_line.0 == conclusion);
    let line_encs = Seq::new(n, |i: int| encode_line(p.lines[i]));
    assert(s == encode_nat_seq(line_encs));
    lemma_get_last_pair_correct(line_encs);
    let last_enc_line = line_encs[n - 1];
    assert(last_enc_line == encode_line(last_line));
    lemma_encode_nat_seq_structure(seq![last_enc_line]);
    lemma_unpair1_pair(encode(conclusion), encode_justification(last_line.1));
}

} // verus!
