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

///  Extract the justification tag from an encoded proof line.
///  For line_enc = pair(formula_enc, just_enc), tag = fst(just_enc) = unpair1(unpair2(line_enc)).
proof fn lemma_line_tag(p: Proof, i: nat)
    requires i < p.lines.len(),
    ensures ({
        let s = encode_proof(p);
        let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));
        let input = pair(s, i);
        let tag_expr = cs_fst(cs_snd(seq_elem_comp()));
        let (formula, just) = p.lines[i as int];
        let just_enc = encode_justification(just);
        eval_comp(tag_expr, input) == unpair1(just_enc)
    }),
{
    let s = encode_proof(p);
    let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));
    let input = pair(s, i);
    let (formula, just) = p.lines[i as int];
    let formula_enc = encode(formula);
    let just_enc = encode_justification(just);
    let line_enc = pair(formula_enc, just_enc);

    lemma_seq_elem_correct(lines, i);
    //  eval_comp(seq_elem_comp(), input) == lines[i] == line_enc

    //  tag = fst(snd(seq_elem))
    lemma_eval_snd(seq_elem_comp(), input);
    lemma_unpair2_pair(formula_enc, just_enc);
    lemma_eval_fst(cs_snd(seq_elem_comp()), input);
}

///  For LogicAxiom (tag 0): check_line dispatches to check_logic_axiom.
proof fn check_line_logic_axiom(p: Proof, i: nat)
    requires
        i < p.lines.len(),
        p.lines[i as int].1 == Justification::LogicAxiom,
        is_logic_axiom(p.lines[i as int].0),
    ensures
        eval_comp(check_line(), pair(encode_proof(p), i)) != 0,
{
    let s = encode_proof(p);
    let input = pair(s, i);
    let (formula, _just) = p.lines[i as int];
    let formula_enc = encode(formula);

    //  Sub-checker result
    lemma_check_logic_axiom_correct(formula);

    //  Dispatch: tag = fst(encode_justification(LogicAxiom)) = fst(pair(0, 0)) = 0
    //  IfZero(tag=0) → then → cs_comp(check_logic_axiom(), cs_fst(seq_elem_comp()))
    //  = eval_comp(check_logic_axiom(), eval_comp(cs_fst(seq_elem_comp()), input))
    //  = eval_comp(check_logic_axiom(), formula_enc)

    let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));
    lemma_seq_elem_correct(lines, i);
    lemma_eval_fst(seq_elem_comp(), input);
    lemma_unpair1_pair(formula_enc, encode_justification(Justification::LogicAxiom));

    //  tag = 0
    lemma_line_tag(p, i);
    lemma_unpair1_pair(0nat, 0nat);

    //  IfZero(tag=0) → then branch → cs_comp(check_logic_axiom(), formula)
    let tag_expr = cs_fst(cs_snd(seq_elem_comp()));
    let formula_expr = cs_fst(seq_elem_comp());
    let then_br = cs_comp(check_logic_axiom(), formula_expr);

    lemma_eval_comp(check_logic_axiom(), formula_expr, input);
    //  eval_comp(then_br, input) = eval_comp(check_logic_axiom(), formula_enc) != 0

    //  The outer IfZero dispatches to then_br since tag == 0
    let else_br = CompSpec::IfZero {
        cond: Box::new(cs_comp(CompSpec::Pred, tag_expr)),
        then_br: Box::new(cs_comp(check_zfc_axiom(), formula_expr)),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr))),
            then_br: Box::new(cs_comp(check_modus_ponens(), CompSpec::CantorPair {
                left: Box::new(CompSpec::CantorPair {
                    left: Box::new(formula_expr),
                    right: Box::new(cs_snd(cs_snd(seq_elem_comp()))),
                }),
                right: Box::new(CompSpec::Id),
            })),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred,
                    cs_comp(CompSpec::Pred, tag_expr)))),
                then_br: Box::new(cs_comp(check_generalization(), CompSpec::CantorPair {
                    left: Box::new(CompSpec::CantorPair {
                        left: Box::new(formula_expr),
                        right: Box::new(cs_snd(cs_snd(seq_elem_comp()))),
                    }),
                    right: Box::new(CompSpec::Id),
                })),
                else_br: Box::new(cs_const(0)),
            }),
        }),
    };

    lemma_eval_ifzero_then(tag_expr, then_br, else_br, input);
}

///  For Assumption (tag 1): check_line dispatches to check_zfc_axiom.
proof fn check_line_assumption(p: Proof, i: nat)
    requires
        i < p.lines.len(),
        p.lines[i as int].1 == Justification::Assumption,
        is_zfc_axiom(p.lines[i as int].0),
    ensures eval_comp(check_line(), pair(encode_proof(p), i)) != 0,
{
    let s = encode_proof(p);
    let input = pair(s, i);
    let (formula, _just) = p.lines[i as int];
    let formula_enc = encode(formula);
    let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));

    lemma_check_zfc_axiom_correct(formula);
    lemma_seq_elem_correct(lines, i);
    lemma_eval_fst(seq_elem_comp(), input);
    lemma_unpair1_pair(formula_enc, encode_justification(Justification::Assumption));

    lemma_line_tag(p, i);
    lemma_unpair1_pair(1nat, 0nat);

    let tag_expr = cs_fst(cs_snd(seq_elem_comp()));
    let formula_expr = cs_fst(seq_elem_comp());

    //  tag = 1 → IfZero(tag=1) → else → IfZero(pred(1)=0) → then → check_zfc_axiom
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(1nat);
    let pred_tag = cs_comp(CompSpec::Pred, tag_expr);

    lemma_eval_comp(check_zfc_axiom(), formula_expr, input);

    let zfc_br = cs_comp(check_zfc_axiom(), formula_expr);
    let content_expr = cs_snd(cs_snd(seq_elem_comp()));
    let mp_gen_input = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(formula_expr), right: Box::new(content_expr) }),
        right: Box::new(CompSpec::Id) };
    let inner_else = CompSpec::IfZero {
        cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr))),
        then_br: Box::new(cs_comp(check_modus_ponens(), mp_gen_input)),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred,
                cs_comp(CompSpec::Pred, tag_expr)))),
            then_br: Box::new(cs_comp(check_generalization(), mp_gen_input)),
            else_br: Box::new(cs_const(0)),
        }),
    };

    lemma_eval_ifzero_then(pred_tag, zfc_br, inner_else, input);

    let logic_br = cs_comp(check_logic_axiom(), formula_expr);
    let outer_else = CompSpec::IfZero {
        cond: Box::new(pred_tag),
        then_br: Box::new(zfc_br),
        else_br: Box::new(inner_else),
    };
    lemma_eval_ifzero_else(tag_expr, logic_br, outer_else, input);
}

///  For ModusPonens (tag 2): check_line dispatches to check_modus_ponens.
proof fn check_line_mp(p: Proof, i: nat, premise_line: nat, implication_line: nat)
    requires
        i < p.lines.len(),
        p.lines[i as int].1 == (Justification::ModusPonens { premise_line, implication_line }),
        premise_line < i,
        implication_line < i,
        p.lines[implication_line as int].0 == mk_implies(
            p.lines[premise_line as int].0, p.lines[i as int].0),
    ensures eval_comp(check_line(), pair(encode_proof(p), i)) != 0,
{
    let s = encode_proof(p);
    let input = pair(s, i);
    let (formula, _just) = p.lines[i as int];
    let formula_enc = encode(formula);
    let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));

    lemma_check_mp_correct(p, i, premise_line, implication_line);
    lemma_seq_elem_correct(lines, i);
    lemma_eval_fst(seq_elem_comp(), input);
    let just_enc = encode_justification(Justification::ModusPonens { premise_line, implication_line });
    lemma_unpair1_pair(formula_enc, just_enc);

    lemma_line_tag(p, i);
    lemma_unpair1_pair(2nat, pair(premise_line, implication_line));

    let tag_expr = cs_fst(cs_snd(seq_elem_comp()));
    let formula_expr = cs_fst(seq_elem_comp());
    let content_expr = cs_snd(cs_snd(seq_elem_comp()));
    let mp_gen_input = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(formula_expr), right: Box::new(content_expr) }),
        right: Box::new(CompSpec::Id) };

    //  tag = 2 → else → else → IfZero(pred(pred(2))=0) → then → check_modus_ponens
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(2nat);
    let pred_tag = cs_comp(CompSpec::Pred, tag_expr);
    lemma_eval_comp(CompSpec::Pred, pred_tag, input);
    lemma_eval_pred(1nat);
    let pred_pred_tag = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr));

    //  Build the mp_gen input and evaluate
    lemma_eval_snd(seq_elem_comp(), input);
    lemma_unpair2_pair(formula_enc, just_enc);
    lemma_eval_snd(cs_snd(seq_elem_comp()), input);
    lemma_unpair2_pair(2nat, pair(premise_line, implication_line));
    lemma_eval_pair(formula_expr, content_expr, input);
    lemma_eval_pair(CompSpec::CantorPair {
        left: Box::new(formula_expr), right: Box::new(content_expr) },
        CompSpec::Id, input);
    lemma_eval_comp(check_modus_ponens(), mp_gen_input, input);

    let mp_br = cs_comp(check_modus_ponens(), mp_gen_input);
    let gen_else = CompSpec::IfZero {
        cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred,
            cs_comp(CompSpec::Pred, tag_expr)))),
        then_br: Box::new(cs_comp(check_generalization(), mp_gen_input)),
        else_br: Box::new(cs_const(0)),
    };
    lemma_eval_ifzero_then(pred_pred_tag, mp_br, gen_else, input);

    let zfc_br = cs_comp(check_zfc_axiom(), formula_expr);
    let mid_else = CompSpec::IfZero {
        cond: Box::new(pred_pred_tag),
        then_br: Box::new(mp_br),
        else_br: Box::new(gen_else),
    };
    lemma_eval_ifzero_else(pred_tag, zfc_br, mid_else, input);

    let logic_br = cs_comp(check_logic_axiom(), formula_expr);
    let outer_else = CompSpec::IfZero {
        cond: Box::new(pred_tag),
        then_br: Box::new(zfc_br),
        else_br: Box::new(mid_else),
    };
    lemma_eval_ifzero_else(tag_expr, logic_br, outer_else, input);
}

///  For Generalization (tag 3): check_line dispatches to check_generalization.
proof fn check_line_gen(p: Proof, i: nat, premise_line: nat, var: nat)
    requires
        i < p.lines.len(),
        p.lines[i as int].1 == (Justification::Generalization { premise_line, var }),
        premise_line < i,
        p.lines[i as int].0 == mk_forall(var, p.lines[premise_line as int].0),
    ensures eval_comp(check_line(), pair(encode_proof(p), i)) != 0,
{
    let s = encode_proof(p);
    let input = pair(s, i);
    let (formula, _just) = p.lines[i as int];
    let formula_enc = encode(formula);
    let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));

    lemma_check_gen_correct(p, i, premise_line, var);
    lemma_seq_elem_correct(lines, i);
    lemma_eval_fst(seq_elem_comp(), input);
    let just_enc = encode_justification(Justification::Generalization { premise_line, var });
    lemma_unpair1_pair(formula_enc, just_enc);

    lemma_line_tag(p, i);
    lemma_unpair1_pair(3nat, pair(premise_line, var));

    let tag_expr = cs_fst(cs_snd(seq_elem_comp()));
    let formula_expr = cs_fst(seq_elem_comp());
    let content_expr = cs_snd(cs_snd(seq_elem_comp()));
    let mp_gen_input = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(formula_expr), right: Box::new(content_expr) }),
        right: Box::new(CompSpec::Id) };

    //  tag = 3 → else → else → else → IfZero(pred(pred(pred(3)))=0) → then → check_gen
    lemma_eval_comp(CompSpec::Pred, tag_expr, input);
    lemma_eval_pred(3nat);
    let pred_tag = cs_comp(CompSpec::Pred, tag_expr);
    lemma_eval_comp(CompSpec::Pred, pred_tag, input);
    lemma_eval_pred(2nat);
    let pred_pred_tag = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr));
    lemma_eval_comp(CompSpec::Pred, pred_pred_tag, input);
    lemma_eval_pred(1nat);
    let pred3_tag = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag_expr)));

    //  Build mp_gen_input eval
    lemma_eval_snd(seq_elem_comp(), input);
    lemma_unpair2_pair(formula_enc, just_enc);
    lemma_eval_snd(cs_snd(seq_elem_comp()), input);
    lemma_unpair2_pair(3nat, pair(premise_line, var));
    lemma_eval_pair(formula_expr, content_expr, input);
    lemma_eval_pair(CompSpec::CantorPair {
        left: Box::new(formula_expr), right: Box::new(content_expr) },
        CompSpec::Id, input);
    lemma_eval_comp(check_generalization(), mp_gen_input, input);

    let gen_br = cs_comp(check_generalization(), mp_gen_input);
    lemma_eval_ifzero_then(pred3_tag, gen_br, cs_const(0), input);

    let mp_br = cs_comp(check_modus_ponens(), mp_gen_input);
    let inner_else = CompSpec::IfZero {
        cond: Box::new(pred3_tag),
        then_br: Box::new(gen_br),
        else_br: Box::new(cs_const(0)),
    };
    lemma_eval_ifzero_else(pred_pred_tag, mp_br, inner_else, input);

    let zfc_br = cs_comp(check_zfc_axiom(), formula_expr);
    let mid_else = CompSpec::IfZero {
        cond: Box::new(pred_pred_tag),
        then_br: Box::new(mp_br),
        else_br: Box::new(inner_else),
    };
    lemma_eval_ifzero_else(pred_tag, zfc_br, mid_else, input);

    let logic_br = cs_comp(check_logic_axiom(), formula_expr);
    let outer_else = CompSpec::IfZero {
        cond: Box::new(pred_tag),
        then_br: Box::new(zfc_br),
        else_br: Box::new(mid_else),
    };
    lemma_eval_ifzero_else(tag_expr, logic_br, outer_else, input);
}

///  For each valid proof line, check_line returns nonzero.
///  Currently handles: LogicAxiom, ModusPonens, Generalization.
///  Assumption: only fixed ZFC axioms (not replacement).
pub proof fn lemma_check_line_valid(p: Proof, i: nat)
    requires
        i < p.lines.len(),
        line_valid(p, i, |f: Formula| is_zfc_axiom(f)),
    ensures
        eval_comp(check_line(), pair(encode_proof(p), i)) != 0,
{
    let (formula, justification) = p.lines[i as int];
    match justification {
        Justification::LogicAxiom => {
            check_line_logic_axiom(p, i);
        },
        Justification::Assumption => {
            check_line_assumption(p, i);
        },
        Justification::ModusPonens { premise_line, implication_line } => {
            check_line_mp(p, i, premise_line, implication_line);
        },
        Justification::Generalization { premise_line, var } => {
            check_line_gen(p, i, premise_line, var);
        },
    }
}

} //  verus!
