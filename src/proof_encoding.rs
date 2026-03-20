use vstd::prelude::*;
use crate::pairing::*;
use crate::formula::*;
use crate::proof_system::*;

verus! {

// ============================================================
// Proof encoding: Gödel-encode proofs as natural numbers
// ============================================================

/// Encode a justification as a natural number.
/// Tags: 0=LogicAxiom, 1=Assumption, 2=ModusPonens, 3=Generalization
pub open spec fn encode_justification(j: Justification) -> nat {
    match j {
        Justification::LogicAxiom => pair(0, 0),
        Justification::Assumption => pair(1, 0),
        Justification::ModusPonens { premise_line, implication_line } =>
            pair(2, pair(premise_line, implication_line)),
        Justification::Generalization { premise_line, var } =>
            pair(3, pair(premise_line, var)),
    }
}

/// Encode a proof line (formula, justification) as a natural number.
pub open spec fn encode_line(line: (Formula, Justification)) -> nat {
    pair(encode(line.0), encode_justification(line.1))
}

/// Encode a sequence of natural numbers.
/// Empty → 0, non-empty → pair(head + 1, encode_nat_seq(tail)).
pub open spec fn encode_nat_seq(s: Seq<nat>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        pair(s[0] + 1, encode_nat_seq(s.subrange(1, s.len() as int)))
    }
}

/// Encode a proof as a natural number.
pub open spec fn encode_proof(p: Proof) -> nat {
    encode_nat_seq(
        Seq::new(p.lines.len(), |i: int| encode_line(p.lines[i]))
    )
}

// ============================================================
// Injectivity lemmas
// ============================================================

/// Tag of a justification encoding.
spec fn justification_tag(j: Justification) -> nat {
    match j {
        Justification::LogicAxiom => 0,
        Justification::Assumption => 1,
        Justification::ModusPonens { .. } => 2,
        Justification::Generalization { .. } => 3,
    }
}

/// Content of a justification encoding.
spec fn justification_content(j: Justification) -> nat {
    match j {
        Justification::LogicAxiom => 0,
        Justification::Assumption => 0,
        Justification::ModusPonens { premise_line, implication_line } =>
            pair(premise_line, implication_line),
        Justification::Generalization { premise_line, var } =>
            pair(premise_line, var),
    }
}

/// Justification encoding is injective.
pub proof fn lemma_encode_justification_injective(j1: Justification, j2: Justification)
    requires
        encode_justification(j1) == encode_justification(j2),
    ensures
        j1 == j2,
{
    lemma_pair_injective(
        justification_tag(j1), justification_content(j1),
        justification_tag(j2), justification_content(j2),
    );
    match j1 {
        Justification::LogicAxiom => {
            match j2 {
                Justification::LogicAxiom => {},
                _ => { assert(false); },
            }
        },
        Justification::Assumption => {
            match j2 {
                Justification::Assumption => {},
                _ => { assert(false); },
            }
        },
        Justification::ModusPonens { premise_line: p1, implication_line: i1 } => {
            match j2 {
                Justification::ModusPonens { premise_line: p2, implication_line: i2 } => {
                    lemma_pair_injective(p1, i1, p2, i2);
                },
                _ => { assert(false); },
            }
        },
        Justification::Generalization { premise_line: p1, var: v1 } => {
            match j2 {
                Justification::Generalization { premise_line: p2, var: v2 } => {
                    lemma_pair_injective(p1, v1, p2, v2);
                },
                _ => { assert(false); },
            }
        },
    }
}

/// Proof line encoding is injective.
pub proof fn lemma_encode_line_injective(l1: (Formula, Justification), l2: (Formula, Justification))
    requires
        encode_line(l1) == encode_line(l2),
    ensures
        l1 == l2,
{
    lemma_pair_injective(
        encode(l1.0), encode_justification(l1.1),
        encode(l2.0), encode_justification(l2.1),
    );
    lemma_encode_injective(l1.0, l2.0);
    lemma_encode_justification_injective(l1.1, l2.1);
}

/// Non-empty sequence has non-zero encoding.
pub proof fn lemma_encode_nat_seq_nonempty(s: Seq<nat>)
    requires
        s.len() > 0,
    ensures
        encode_nat_seq(s) > 0,
{
    lemma_pair_gt_components(s[0] + 1, encode_nat_seq(s.subrange(1, s.len() as int)));
}

/// Nat-sequence encoding is injective.
pub proof fn lemma_encode_nat_seq_injective(s1: Seq<nat>, s2: Seq<nat>)
    requires
        encode_nat_seq(s1) == encode_nat_seq(s2),
    ensures
        s1 =~= s2,
    decreases s1.len(),
{
    if s1.len() == 0 {
        if s2.len() > 0 {
            lemma_encode_nat_seq_nonempty(s2);
        }
    } else if s2.len() == 0 {
        lemma_encode_nat_seq_nonempty(s1);
    } else {
        let t1 = s1.subrange(1, s1.len() as int);
        let t2 = s2.subrange(1, s2.len() as int);
        lemma_pair_injective(
            s1[0] + 1, encode_nat_seq(t1),
            s2[0] + 1, encode_nat_seq(t2),
        );
        lemma_encode_nat_seq_injective(t1, t2);
        assert(s1.len() == s2.len()) by {
            assert(t1.len() == t2.len());
        };
        assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
            if i == 0 {
            } else {
                assert(s1[i] == t1[i - 1]);
                assert(s2[i] == t2[i - 1]);
            }
        };
    }
}

/// Proof encoding is injective.
pub proof fn lemma_encode_proof_injective(p1: Proof, p2: Proof)
    requires
        encode_proof(p1) == encode_proof(p2),
    ensures
        p1 == p2,
{
    let s1 = Seq::new(p1.lines.len(), |i: int| encode_line(p1.lines[i]));
    let s2 = Seq::new(p2.lines.len(), |i: int| encode_line(p2.lines[i]));
    lemma_encode_nat_seq_injective(s1, s2);
    assert(p1.lines.len() == p2.lines.len());
    assert forall|i: int| 0 <= i < p1.lines.len() implies p1.lines[i] == p2.lines[i] by {
        assert(s1[i] == encode_line(p1.lines[i]));
        assert(s2[i] == encode_line(p2.lines[i]));
        assert(s1[i] == s2[i]);
        lemma_encode_line_injective(p1.lines[i], p2.lines[i]);
    };
    assert(p1.lines =~= p2.lines);
}

} // verus!
