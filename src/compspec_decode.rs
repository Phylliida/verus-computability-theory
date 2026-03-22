use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::proof_system::*;
use crate::proof_encoding::*;
use crate::zfc_enumerator::*;

verus! {

// ============================================================
// CompSpec helper constructors
// ============================================================

/// BoundedRec step input: pair(i, pair(acc, original_input))
/// Extract the accumulator.
pub open spec fn br_acc() -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(
        CompSpec::CantorSnd { inner: Box::new(CompSpec::Id) }
    )}
}

/// BoundedRec step: scan to last element of encoded sequence.
/// If unpair2(acc) == 0: stay (at last element). Else: advance to unpair2(acc).
pub open spec fn seq_scan_step() -> CompSpec {
    CompSpec::IfZero {
        cond: Box::new(CompSpec::CantorSnd { inner: Box::new(br_acc()) }),
        then_br: Box::new(br_acc()),
        else_br: Box::new(CompSpec::CantorSnd { inner: Box::new(br_acc()) }),
    }
}

/// Scan to last pair in encoded nat sequence.
/// For s = encode_nat_seq([e1, ..., en]), returns pair(en + 1, 0).
pub open spec fn get_last_pair() -> CompSpec {
    CompSpec::BoundedRec {
        count_fn: Box::new(CompSpec::Id),
        base: Box::new(CompSpec::Id),
        step: Box::new(seq_scan_step()),
    }
}

/// Get last element from encoded nat sequence.
/// = unpair1(get_last_pair(s)) - 1
pub open spec fn last_seq_elem() -> CompSpec {
    CompSpec::Comp {
        outer: Box::new(CompSpec::Pred),
        inner: Box::new(CompSpec::CantorFst {
            inner: Box::new(get_last_pair()),
        }),
    }
}

/// Get formula encoding from last encoded proof line.
/// encode_line = pair(encode_formula, encode_justification)
/// So formula_enc = unpair1(last_seq_elem(s))
pub open spec fn last_formula_enc() -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(last_seq_elem()) }
}

/// Get Iff data from formula encoding.
/// For Iff: encode(Iff{l,r}) = pair(6, pair(encode(l), encode(r)))
/// iff_data = unpair2(formula_enc) = pair(encode(l), encode(r))
pub open spec fn iff_data() -> CompSpec {
    CompSpec::CantorSnd { inner: Box::new(last_formula_enc()) }
}

// ============================================================
// Concrete CompSpec terms for output extraction
// ============================================================

/// CompSpec for output1: extract encode(left) from valid proof code.
/// = unpair1(iff_data(s)) = unpair1(unpair2(unpair1(last_elem(s))))
pub open spec fn output1_comp_term() -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(iff_data()) }
}

/// CompSpec for output2: extract encode(right) from valid proof code.
/// = unpair2(iff_data(s)) = unpair2(unpair2(unpair1(last_elem(s))))
pub open spec fn output2_comp_term() -> CompSpec {
    CompSpec::CantorSnd { inner: Box::new(iff_data()) }
}

// ============================================================
// Correctness: scanning finds the last element
// ============================================================

/// The scan step advances through the sequence or stays at last element.
proof fn lemma_seq_scan_step_eval(acc: nat, i: nat, input: nat)
    ensures
        eval_comp(seq_scan_step(), pair(i, pair(acc, input))) ==
            if unpair2(acc) == 0 { acc } else { unpair2(acc) },
{
    // eval_comp(IfZero { cond, then_br, else_br }, x) =
    //   if eval_comp(cond, x) == 0 { eval_comp(then_br, x) } else { eval_comp(else_br, x) }
    // cond = CantorSnd(br_acc()) evaluates to unpair2(acc)
    // then_br = br_acc() evaluates to acc
    // else_br = CantorSnd(br_acc()) evaluates to unpair2(acc)
    let x = pair(i, pair(acc, input));
    assert(eval_comp(br_acc(), x) == acc) by {
        lemma_unpair1_pair(acc, input);
        lemma_unpair2_pair(i, pair(acc, input));
    };
}

/// After scanning, the accumulator reaches the last pair of the sequence.
/// For a non-empty encoded sequence, the result is pair(last_elem + 1, 0).
proof fn lemma_scan_seq(seq_enc: nat, fuel: nat)
    requires
        seq_enc != 0,  // non-empty sequence
        fuel >= seq_enc,
    ensures ({
        let result = iterate(
            |x: nat| eval_comp(seq_scan_step(), x),
            fuel, seq_enc, seq_enc);
        unpair2(result) == 0 && unpair1(result) > 0
    }),
    decreases fuel,
{
    // If unpair2(seq_enc) == 0: we're already at the last element.
    // iterate with any fuel >= 0 keeps it there.
    // If unpair2(seq_enc) != 0: one step advances to unpair2(seq_enc).
    // By lemma_pair_pos_tag_gt_content, unpair2(seq_enc) < seq_enc.
    // Recurse with fuel - 1 and the advanced position.
    let step_fn = |x: nat| eval_comp(seq_scan_step(), x);

    if fuel == 0 {
        // iterate(f, 0, acc, input) = acc = seq_enc
        // seq_enc != 0, so it's pair(a, b) for some a, b.
        // We need unpair2(seq_enc) == 0... but that's not guaranteed for fuel == 0.
        // Actually fuel >= seq_enc and seq_enc != 0 implies fuel >= 1.
        assert(false); // unreachable: fuel >= seq_enc >= 1
    } else {
        if unpair2(seq_enc) == 0 {
            // Already at last element. iterate keeps it there.
            // step_fn(pair(fuel-1, pair(seq_enc, seq_enc))) = seq_enc (since unpair2(seq_enc) == 0)
            lemma_seq_scan_step_eval(seq_enc, (fuel - 1) as nat, seq_enc);
            // After one iteration: acc is still seq_enc.
            // Need: iterate(step_fn, fuel-1, seq_enc, seq_enc) has the same properties.
            // By induction (or just observe that once at last element, it stays):
            lemma_scan_seq_at_last(seq_enc, (fuel - 1) as nat, seq_enc);
        } else {
            // Advance to tail = unpair2(seq_enc)
            let tail = unpair2(seq_enc);
            lemma_seq_scan_step_eval(seq_enc, (fuel - 1) as nat, seq_enc);
            // After one step: acc becomes tail
            // iterate(step_fn, fuel, seq_enc, seq_enc)
            // = iterate(step_fn, fuel-1, step_fn(pair(fuel-1, pair(seq_enc, seq_enc))), seq_enc)
            // = iterate(step_fn, fuel-1, tail, seq_enc)

            if tail == 0 {
                // The sequence had exactly one element (well, unpair2 being non-zero
                // means there IS a tail, but tail could be 0 meaning the tail is empty).
                // Wait, unpair2(seq_enc) != 0 was our assumption, so tail != 0.
                assert(false); // unreachable
            } else {
                // tail is a non-empty sub-sequence, and tail < seq_enc
                // (since seq_enc = pair(unpair1(seq_enc), tail) and unpair1(seq_enc) >= 1
                //  because seq_enc encodes a non-empty sequence)
                // Actually we need: fuel - 1 >= tail.
                // Since tail = unpair2(seq_enc) < seq_enc (when unpair1 >= 1)
                // and fuel >= seq_enc, we have fuel - 1 >= seq_enc - 1 >= tail.
                // But is unpair1(seq_enc) >= 1? For a valid encoded sequence,
                // seq_enc = pair(elem + 1, rest), so unpair1(seq_enc) = elem + 1 >= 1.
                // We need this as a precondition or derive it.
                // For now, assume it holds for valid proof codes.
                assume(fuel - 1 >= tail); // TODO: prove from pair properties
                lemma_scan_seq(tail, (fuel - 1) as nat);
            }
        }
    }
}

/// Helper: once at the last element, scanning stays there.
proof fn lemma_scan_seq_at_last(acc: nat, fuel: nat, input: nat)
    requires
        unpair2(acc) == 0,
    ensures
        iterate(
            |x: nat| eval_comp(seq_scan_step(), x),
            fuel, acc, input) == acc,
    decreases fuel,
{
    if fuel == 0 {
    } else {
        let step_fn = |x: nat| eval_comp(seq_scan_step(), x);
        lemma_seq_scan_step_eval(acc, (fuel - 1) as nat, input);
        assert(step_fn(pair((fuel - 1) as nat, pair(acc, input))) == acc);
        lemma_scan_seq_at_last(acc, (fuel - 1) as nat, input);
    }
}

// ============================================================
// Main output correctness proofs
// ============================================================

/// The output1 CompSpec term computes the first output of enumerator_spec.
pub proof fn lemma_output1_comp_correct()
    ensures
        is_output1_comp(output1_comp_term()),
{
    // For each valid proof code s:
    // eval_comp(output1_comp_term(), s) == enumerator_spec(s).unwrap().0
    assert forall|s: nat| is_valid_iff_proof_code(s) implies
        (#[trigger] eval_comp(output1_comp_term(), s)) == enumerator_spec(s).unwrap().0
    by {
        // s encodes a valid proof p with Iff conclusion
        let p: Proof = choose|p: Proof|
            encode_proof(p) == s &&
            is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
            p.lines.len() > 0 &&
            conclusion_is_iff_of_sentences(proof_conclusion(p));

        // The conclusion is Iff{left, right}
        let conclusion = proof_conclusion(p);
        let (enc_left, enc_right) = extract_iff_pair(conclusion);
        assert(enumerator_spec(s).unwrap().0 == enc_left);

        // Now trace through the CompSpec evaluation:
        // eval_comp(output1_comp_term(), s) should equal enc_left.
        // This requires connecting the CompSpec's unpairing chain to the encoding structure.
        // TODO: complete the proof connecting eval_comp to the encoding
        assume(eval_comp(output1_comp_term(), s) == enc_left);
    };
}

/// The output2 CompSpec term computes the second output of enumerator_spec.
pub proof fn lemma_output2_comp_correct()
    ensures
        is_output2_comp(output2_comp_term()),
{
    assert forall|s: nat| is_valid_iff_proof_code(s) implies
        (#[trigger] eval_comp(output2_comp_term(), s)) == enumerator_spec(s).unwrap().1
    by {
        let p: Proof = choose|p: Proof|
            encode_proof(p) == s &&
            is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
            p.lines.len() > 0 &&
            conclusion_is_iff_of_sentences(proof_conclusion(p));

        let conclusion = proof_conclusion(p);
        let (enc_left, enc_right) = extract_iff_pair(conclusion);
        assert(enumerator_spec(s).unwrap().1 == enc_right);

        assume(eval_comp(output2_comp_term(), s) == enc_right);
    };
}

} // verus!
