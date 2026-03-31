use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_all_lines_helpers::*;
use crate::compspec_dispatchers::*;
use crate::proof_system::*;
use crate::proof_encoding::*;
use crate::zfc::*;

verus! {

///  For each valid proof line, check_line returns nonzero.
///  This is the key lemma connecting per-line validity to the CompSpec checker.
///
///  For now: handles LogicAxiom, ModusPonens, Generalization.
///  Assumption is handled for fixed ZFC axioms (not replacement).
pub proof fn lemma_check_line_valid(p: Proof, i: nat)
    requires
        i < p.lines.len(),
        line_valid(p, i, |f: Formula| is_zfc_axiom(f)),
        //  Additional: for Assumption lines, require fixed ZFC axiom (not replacement)
        //  This restriction will be lifted once check_replacement_axiom is proved.
        (p.lines[i as int].1 == Justification::Assumption ==>
            (p.lines[i as int].0 == extensionality_axiom()
            || p.lines[i as int].0 == pairing_axiom()
            || p.lines[i as int].0 == union_axiom()
            || p.lines[i as int].0 == powerset_axiom()
            || p.lines[i as int].0 == infinity_axiom()
            || p.lines[i as int].0 == foundation_axiom()
            || p.lines[i as int].0 == choice_axiom())),
    ensures
        eval_comp(check_line(), pair(encode_proof(p), i)) != 0,
{
    let s = encode_proof(p);
    let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));
    let (formula, justification) = p.lines[i as int];
    let formula_enc = encode(formula);
    let just_enc = encode_justification(justification);
    let line_enc = encode_line(p.lines[i as int]);

    //  seq_elem_comp extracts the line encoding
    lemma_seq_elem_correct(lines, i);
    //  eval_comp(seq_elem_comp(), pair(s, i)) == lines[i] == line_enc

    //  line_enc = pair(formula_enc, just_enc)
    lemma_unpair1_pair(formula_enc, just_enc);
    lemma_unpair2_pair(formula_enc, just_enc);

    //  Extract tag from justification encoding
    //  tag = fst(snd(seq_elem)) = fst(just_enc)
    //  For LogicAxiom: just_enc = pair(0, 0), tag = 0
    //  For Assumption: just_enc = pair(1, 0), tag = 1
    //  For ModusPonens{pl, il}: just_enc = pair(2, pair(pl, il)), tag = 2
    //  For Generalization{pl, var}: just_enc = pair(3, pair(pl, var)), tag = 3

    match justification {
        Justification::LogicAxiom => {
            //  tag == 0: IfZero(tag) → then → check_logic_axiom(formula_enc)
            //  line_valid → is_logic_axiom(formula) → check_logic_axiom returns nonzero
            lemma_check_logic_axiom_correct(formula);
            //  Need: eval_comp(check_line(), pair(s, i)) == eval_comp(check_logic_axiom(), formula_enc)
            //  This requires the IfZero dispatch evaluation
            //  TODO: Full IfZero dispatch chain for tag 0
        },
        Justification::Assumption => {
            //  tag == 1: IfZero(tag) → else → IfZero(pred(tag)) → then → check_zfc_axiom
            lemma_check_zfc_fixed_axiom_correct(formula);
            //  TODO: Full IfZero dispatch chain for tag 1
        },
        Justification::ModusPonens { premise_line, implication_line } => {
            //  tag == 2: dispatch to check_modus_ponens
            lemma_check_mp_correct(p, i, premise_line, implication_line);
            //  TODO: Full IfZero dispatch chain for tag 2
        },
        Justification::Generalization { premise_line, var } => {
            //  tag == 3: dispatch to check_generalization
            lemma_check_gen_correct(p, i, premise_line, var);
            //  TODO: Full IfZero dispatch chain for tag 3
        },
    }

    //  TODO: Connect the sub-checker results to eval_comp(check_line(), pair(s, i))
    //  via the IfZero dispatch chain and seq_elem evaluation.
    //  This requires ~30 lines of eval_comp chain per justification type.
}

} //  verus!
