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

/// Step 1: eval_comp of get_last_pair on an encoded proof gives the last pair.
proof fn lemma_eval_get_last_pair(s: nat, p: Proof)
    requires
        encode_proof(p) == s,
        p.lines.len() > 0,
    ensures ({
        let line_encs = Seq::new(p.lines.len(), |i: int| encode_line(p.lines[i]));
        eval_comp(get_last_pair(), s) == encode_nat_seq(seq![line_encs[p.lines.len() - 1]])
    }),
{
    let line_encs = Seq::new(p.lines.len(), |i: int| encode_line(p.lines[i]));
    assert(s == encode_nat_seq(line_encs));
    lemma_get_last_pair_correct(line_encs);
}

/// Step 2: eval_comp of last_seq_elem gives the last encoded line.
proof fn lemma_eval_last_seq_elem(s: nat, p: Proof)
    requires
        encode_proof(p) == s,
        p.lines.len() > 0,
    ensures ({
        let n = p.lines.len();
        let last_line = p.lines[n - 1];
        eval_comp(last_seq_elem(), s) == encode_line(last_line)
    }),
{
    let n = p.lines.len();
    let last_line = p.lines[n - 1];
    let line_encs = Seq::new(n, |i: int| encode_line(p.lines[i]));
    let last_enc_line = encode_line(last_line);
    assert(line_encs[n - 1] == last_enc_line);

    // From step 1
    lemma_eval_get_last_pair(s, p);
    let last_pair = encode_nat_seq(seq![last_enc_line]);
    assert(eval_comp(get_last_pair(), s) == last_pair);

    // last_pair = pair(last_enc_line + 1, 0)
    lemma_encode_nat_seq_structure(seq![last_enc_line]);
    lemma_unpair1_pair(last_enc_line + 1, 0nat);
    // unpair1(last_pair) = last_enc_line + 1
    // Pred(last_enc_line + 1) = last_enc_line

    // Explicit intermediate: CantorFst(get_last_pair) = unpair1(last_pair) = last_enc_line + 1
    let fst_val = eval_comp(CompSpec::CantorFst { inner: Box::new(get_last_pair()) }, s);
    assert(fst_val == unpair1(last_pair));
    assert(fst_val == last_enc_line + 1);

    // Comp(Pred, CantorFst(get_last_pair)) = Pred(fst_val) = last_enc_line
    assert(eval_comp(last_seq_elem(), s) == eval_comp(CompSpec::Pred, fst_val));
}

/// Step 3: eval_comp of last_formula_enc gives the conclusion encoding.
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

    // From step 2
    lemma_eval_last_seq_elem(s, p);
    assert(eval_comp(last_seq_elem(), s) == encode_line(last_line));

    // encode_line(last_line) = pair(encode(conclusion), encode_justification(last_line.1))
    lemma_unpair1_pair(encode(conclusion), encode_justification(last_line.1));
    // unpair1(encode_line(last_line)) = encode(conclusion)

    // last_formula_enc = CantorFst(last_seq_elem)
    // eval = unpair1(eval(last_seq_elem, s))
    //      = unpair1(encode_line(last_line))
    //      = encode(conclusion)
}

} // verus!
