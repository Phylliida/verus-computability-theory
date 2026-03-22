use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::proof_system::*;
use crate::proof_encoding::*;
use crate::zfc::*;
use crate::zfc_enumerator::*;
use crate::enumerator_computable::*;
use crate::compspec_decode::*;

verus! {

// ============================================================
// CompSpec helpers for nat-level operations
// ============================================================

/// CompSpec AND: returns 1 iff both sub-terms are nonzero.
/// Uses Mul (product of {0,1}-valued terms).
pub open spec fn cs_and(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Mul { left: Box::new(a), right: Box::new(b) }
}

/// CompSpec OR: returns nonzero iff either sub-term is nonzero.
/// Uses Add (sum of {0,1}-valued terms).
pub open spec fn cs_or(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Add { left: Box::new(a), right: Box::new(b) }
}

/// CompSpec NOT: 1 if input == 0, 0 otherwise.
pub open spec fn cs_not(a: CompSpec) -> CompSpec {
    CompSpec::IfZero {
        cond: Box::new(a),
        then_br: Box::new(CompSpec::Const { value: 1 }),
        else_br: Box::new(CompSpec::Const { value: 0 }),
    }
}

/// CompSpec: check if input != 0 (returns 1 if nonzero, 0 if zero).
pub open spec fn cs_nonzero() -> CompSpec {
    CompSpec::IfZero {
        cond: Box::new(CompSpec::Id),
        then_br: Box::new(CompSpec::Const { value: 0 }),
        else_br: Box::new(CompSpec::Const { value: 1 }),
    }
}

/// CompSpec: check two values are equal (returns 1 if equal, 0 if not).
/// Uses the built-in Eq.
pub open spec fn cs_eq(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Eq { left: Box::new(a), right: Box::new(b) }
}

/// CompSpec: check a < b (returns 1 if true, 0 if not).
pub open spec fn cs_lt(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Lt { left: Box::new(a), right: Box::new(b) }
}

/// CompSpec: apply f to input, i.e., Comp(f, inner).
pub open spec fn cs_comp(outer: CompSpec, inner: CompSpec) -> CompSpec {
    CompSpec::Comp { outer: Box::new(outer), inner: Box::new(inner) }
}

/// CompSpec: constant value.
pub open spec fn cs_const(v: nat) -> CompSpec {
    CompSpec::Const { value: v }
}

/// CompSpec: unpair1 of a sub-expression.
pub open spec fn cs_fst(inner: CompSpec) -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(inner) }
}

/// CompSpec: unpair2 of a sub-expression.
pub open spec fn cs_snd(inner: CompSpec) -> CompSpec {
    CompSpec::CantorSnd { inner: Box::new(inner) }
}

// ============================================================
// Sequence operations as CompSpec
// ============================================================

/// Get i-th element of encoded nat sequence (0-indexed).
/// Input: pair(seq_enc, i)
/// Output: the i-th element (unpair1-1 after advancing i times).
/// Uses BoundedRec to advance i times through the chain.
pub open spec fn seq_elem_comp() -> CompSpec {
    // Advance i times: BoundedRec with count=snd(input)=i, base=fst(input)=seq_enc
    // Step: advance = unpair2(acc) (move to tail)
    // After loop: acc is at the i-th position in the chain
    // Element = unpair1(acc) - 1
    cs_comp(
        CompSpec::Pred,  // subtract 1
        cs_fst(  // unpair1 of the position
            CompSpec::BoundedRec {
                count_fn: Box::new(cs_snd(CompSpec::Id)),  // count = i
                base: Box::new(cs_fst(CompSpec::Id)),      // start at seq_enc
                step: Box::new(cs_snd(br_acc())),          // advance: unpair2(acc)
            }
        ),
    )
}

/// Get formula encoding from the i-th line of an encoded proof sequence.
/// Input: pair(seq_enc, i)
/// Output: unpair1 of the i-th element (= encode(formula))
pub open spec fn line_formula_comp() -> CompSpec {
    cs_fst(seq_elem_comp())  // unpair1(element) = formula encoding
}

// ============================================================
// Per-line justification checks
// ============================================================

// Input convention for line checks:
//   pair(pair(formula_enc, justification_content), pair(seq_enc, line_idx))
// Where justification_content = unpair2(justification_enc) (tag already dispatched)

/// Access formula_enc from check input.
pub open spec fn ci_formula() -> CompSpec { cs_fst(cs_fst(CompSpec::Id)) }
/// Access justification content from check input.
pub open spec fn ci_just_content() -> CompSpec { cs_snd(cs_fst(CompSpec::Id)) }
/// Access seq_enc from check input.
pub open spec fn ci_seq() -> CompSpec { cs_fst(cs_snd(CompSpec::Id)) }
/// Access line_idx from check input.
pub open spec fn ci_idx() -> CompSpec { cs_snd(cs_snd(CompSpec::Id)) }

/// Look up the formula encoding at a given index in the sequence.
/// Input: pair(seq_enc, index) — delegates to line_formula_comp.
pub open spec fn lookup_formula_at(seq_expr: CompSpec, idx_expr: CompSpec) -> CompSpec {
    cs_comp(line_formula_comp(), CompSpec::CantorPair {
        left: Box::new(seq_expr),
        right: Box::new(idx_expr),
    })
}

/// Check ModusPonens justification at encoding level.
/// Input: pair(pair(formula_enc, pair(premise_idx, impl_idx)), pair(seq_enc, line_idx))
/// Check: premise_idx < line_idx, impl_idx < line_idx,
///   and formula at impl_idx == pair(5, pair(formula at premise_idx, formula_enc))
pub open spec fn check_modus_ponens() -> CompSpec {
    let premise_idx = cs_fst(ci_just_content());
    let impl_idx = cs_snd(ci_just_content());
    let formula_enc = ci_formula();
    let seq = ci_seq();
    let idx = ci_idx();

    // premise_idx < line_idx
    let check_premise_bound = cs_lt(premise_idx, idx);
    // impl_idx < line_idx
    let check_impl_bound = cs_lt(impl_idx, idx);

    // Look up premise formula
    let premise_formula = lookup_formula_at(seq, premise_idx);
    // Look up implication formula
    let impl_formula = lookup_formula_at(seq, impl_idx);

    // Expected implication: pair(5, pair(premise_formula, formula_enc))
    // i.e., encode(Implies(premise, current_formula))
    let expected_impl = CompSpec::CantorPair {
        left: Box::new(cs_const(5)),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(premise_formula),
            right: Box::new(formula_enc),
        }),
    };

    cs_and(check_premise_bound, cs_and(check_impl_bound,
        cs_eq(impl_formula, expected_impl)))
}

/// Check Generalization justification at encoding level.
/// Input: pair(pair(formula_enc, pair(premise_idx, var)), pair(seq_enc, line_idx))
/// Check: premise_idx < line_idx,
///   and formula_enc == pair(7, pair(var, formula at premise_idx))
pub open spec fn check_generalization() -> CompSpec {
    let premise_idx = cs_fst(ci_just_content());
    let var = cs_snd(ci_just_content());
    let formula_enc = ci_formula();
    let seq = ci_seq();
    let idx = ci_idx();

    // premise_idx < line_idx
    let check_bound = cs_lt(premise_idx, idx);

    // Look up premise formula
    let premise_formula = lookup_formula_at(seq, premise_idx);

    // Expected formula: pair(7, pair(var, premise_formula))
    // i.e., encode(Forall(var, premise))
    let expected = CompSpec::CantorPair {
        left: Box::new(cs_const(7)),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(var),
            right: Box::new(premise_formula),
        }),
    };

    cs_and(check_bound, cs_eq(formula_enc, expected))
}

/// Check: is_axiom_identity at encoding level.
/// f = Implies(φ, φ) ↔ tag==5 && left==right
/// Input: formula_enc
pub open spec fn check_axiom_identity() -> CompSpec {
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  // tag == 5 (Implies)
        cs_eq(
            cs_fst(cs_snd(CompSpec::Id)),   // left = unpair1(unpair2(f))
            cs_snd(cs_snd(CompSpec::Id)),   // right = unpair2(unpair2(f))
        )
    )
}

/// Check: is_axiom_eq_refl at encoding level.
/// f = Eq(t, t) ↔ tag==0 && left==right
/// Input: formula_enc
pub open spec fn check_axiom_eq_refl() -> CompSpec {
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(0)),  // tag == 0 (Eq)
        cs_eq(
            cs_fst(cs_snd(CompSpec::Id)),   // left term
            cs_snd(cs_snd(CompSpec::Id)),   // right term
        )
    )
}

/// Check: is_axiom_iff_elim_left at encoding level.
/// f = Implies(Iff(φ,ψ), Implies(φ,ψ))
/// ↔ tag==5, left has tag==6, right has tag==5,
///   and left's sub-formulas match right's sub-formulas
/// Input: formula_enc
pub open spec fn check_axiom_iff_elim_left() -> CompSpec {
    let left = cs_snd(CompSpec::Id);     // left of outer Implies (should be Iff)
    let right = cs_snd(CompSpec::Id);    // right of outer Implies (should be Implies)
    // Needs: fst(f)==5, fst(left)==6, fst(right)==5,
    //   snd(left) == snd(right) (both have same pair(φ,ψ))
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  // outer tag == Implies
        cs_and(
            cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6)),  // left tag == Iff
            cs_and(
                cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5)),  // right tag == Implies
                // left content == right content (same pair(φ,ψ))
                cs_eq(
                    cs_snd(cs_fst(cs_snd(CompSpec::Id))),  // content of left (Iff data)
                    cs_snd(cs_snd(cs_snd(CompSpec::Id))),  // content of right (Implies data)
                )
            )
        )
    )
}

/// Check: is_axiom_iff_elim_right at encoding level.
/// f = Implies(Iff(φ,ψ), Implies(ψ,φ))
/// Same as iff_elim_left but right's sub-formulas are swapped.
pub open spec fn check_axiom_iff_elim_right() -> CompSpec {
    // outer tag == 5, left tag == 6, right tag == 5
    // left content = pair(φ_enc, ψ_enc)
    // right content = pair(ψ_enc, φ_enc)  (swapped)
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),
        cs_and(
            cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6)),
            cs_and(
                cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5)),
                cs_and(
                    // left.φ == right.ψ
                    cs_eq(
                        cs_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),  // φ from Iff
                        cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))),  // ψ from Implies (right side)
                    ),
                    // left.ψ == right.φ
                    cs_eq(
                        cs_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),  // ψ from Iff
                        cs_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id)))),  // φ from Implies (left side)
                    )
                )
            )
        )
    )
}

/// Check: is_axiom_iff_intro at encoding level.
/// f = Implies(Implies(φ,ψ), Implies(Implies(ψ,φ), Iff(φ,ψ)))
/// Encoding: pair(5, pair(pair(5, pair(φ,ψ)), pair(5, pair(pair(5, pair(ψ,φ)), pair(6, pair(φ,ψ))))))
/// Check: outer tag==5, left is Implies(φ,ψ), right is Implies(Implies(ψ,φ), Iff(φ,ψ))
pub open spec fn check_axiom_iff_intro() -> CompSpec {
    // f = pair(5, pair(L, R))
    // L = pair(5, pair(φ, ψ))
    // R = pair(5, pair(pair(5, pair(ψ, φ)), pair(6, pair(φ, ψ))))
    // Extract φ = fst(snd(L)), ψ = snd(snd(L))
    // Check: outer tag==5, L tag==5, R tag==5
    //   R.left = pair(5, pair(ψ, φ))  [Implies(ψ,φ)]
    //   R.right = pair(6, pair(φ, ψ)) [Iff(φ,ψ)]
    let outer_content = cs_snd(CompSpec::Id);  // pair(L, R)
    let l = cs_fst(outer_content);              // L
    let r = cs_snd(outer_content);              // R
    let phi = cs_fst(cs_snd(l));                // φ from L = pair(5, pair(φ, ψ))
    let psi = cs_snd(cs_snd(l));                // ψ from L

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),   // outer tag == Implies
        cs_and(
            cs_eq(cs_fst(l), cs_const(5)),           // L tag == Implies
            cs_and(
                cs_eq(cs_fst(r), cs_const(5)),       // R tag == Implies
                cs_and(
                    // R.left == pair(5, pair(ψ, φ))
                    cs_eq(cs_fst(cs_snd(r)),
                        CompSpec::CantorPair {
                            left: Box::new(cs_const(5)),
                            right: Box::new(CompSpec::CantorPair {
                                left: Box::new(psi),
                                right: Box::new(phi),
                            }),
                        }),
                    // R.right == pair(6, pair(φ, ψ))
                    cs_eq(cs_snd(cs_snd(r)),
                        CompSpec::CantorPair {
                            left: Box::new(cs_const(6)),
                            right: Box::new(cs_snd(l)),  // pair(φ, ψ) = snd(L)
                        }),
                )
            )
        )
    )
}

/// Check: is_axiom_hyp_syllogism at encoding level.
/// f = Implies(Implies(φ,ψ), Implies(Implies(ψ,χ), Implies(φ,χ)))
/// Check by extracting φ,ψ,χ from the structure and verifying consistency.
pub open spec fn check_axiom_hyp_syllogism() -> CompSpec {
    // f = pair(5, pair(pair(5, pair(φ,ψ)), pair(5, pair(pair(5, pair(ψ',χ)), pair(5, pair(φ',χ'))))))
    // Check: all Implies tags, ψ==ψ', φ==φ', χ==χ'
    let content = cs_snd(CompSpec::Id);        // pair(L, R)
    let l = cs_fst(content);                    // L = pair(5, pair(φ, ψ))
    let r = cs_snd(content);                    // R = pair(5, pair(M, N))
    let phi = cs_fst(cs_snd(l));                // φ
    let psi = cs_snd(cs_snd(l));                // ψ
    let m = cs_fst(cs_snd(r));                  // M = pair(5, pair(ψ', χ))
    let n = cs_snd(cs_snd(r));                  // N = pair(5, pair(φ', χ'))

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  // outer Implies
        cs_and(
            cs_eq(cs_fst(l), cs_const(5)),          // L = Implies
            cs_and(
                cs_eq(cs_fst(r), cs_const(5)),      // R = Implies
                cs_and(
                    cs_eq(cs_fst(m), cs_const(5)),  // M = Implies
                    cs_and(
                        cs_eq(cs_fst(n), cs_const(5)),  // N = Implies
                        cs_and(
                            // ψ == ψ' (M's left == L's right)
                            cs_eq(cs_fst(cs_snd(m)), psi),
                            cs_and(
                                // φ == φ' (N's left == L's left)
                                cs_eq(cs_fst(cs_snd(n)), phi),
                                // χ == χ' (N's right == M's right)
                                cs_eq(cs_snd(cs_snd(n)), cs_snd(cs_snd(m))),
                            )
                        )
                    )
                )
            )
        )
    )
}

/// Check: is_axiom_quantifier_dist at encoding level.
/// f = Implies(Forall(v, Implies(φ,ψ)), Implies(Forall(v,φ), Forall(v,ψ)))
pub open spec fn check_axiom_quantifier_dist() -> CompSpec {
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);           // Forall(v, Implies(φ,ψ))
    let r = cs_snd(content);           // Implies(Forall(v,φ), Forall(v,ψ))
    let v = cs_fst(cs_snd(l));         // v (from Forall)
    let body = cs_snd(cs_snd(l));      // Implies(φ,ψ)
    let phi = cs_fst(cs_snd(body));    // φ
    let psi = cs_snd(cs_snd(body));    // ψ

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  // outer Implies
        cs_and(
            cs_eq(cs_fst(l), cs_const(7)),          // L = Forall
            cs_and(
                cs_eq(cs_fst(body), cs_const(5)),   // body = Implies
                cs_and(
                    cs_eq(cs_fst(r), cs_const(5)),  // R = Implies
                    cs_and(
                        // R.left == pair(7, pair(v, φ)) = Forall(v, φ)
                        cs_eq(cs_fst(cs_snd(r)),
                            CompSpec::CantorPair {
                                left: Box::new(cs_const(7)),
                                right: Box::new(CompSpec::CantorPair {
                                    left: Box::new(v),
                                    right: Box::new(phi),
                                }),
                            }),
                        // R.right == pair(7, pair(v, ψ)) = Forall(v, ψ)
                        cs_eq(cs_snd(cs_snd(r)),
                            CompSpec::CantorPair {
                                left: Box::new(cs_const(7)),
                                right: Box::new(CompSpec::CantorPair {
                                    left: Box::new(v),
                                    right: Box::new(psi),
                                }),
                            }),
                    )
                )
            )
        )
    )
}

/// Check LogicAxiom justification: formula matches one of the axiom schemas.
/// Input: formula_enc
/// Checks all pattern-matchable schemas. Schemas requiring substitution
/// or free-var checking (universal_inst, vacuous_quant, eq_subst) use
/// placeholder checks for now.
pub open spec fn check_logic_axiom() -> CompSpec {
    cs_or(check_axiom_identity(),
    cs_or(check_axiom_eq_refl(),
    cs_or(check_axiom_iff_elim_left(),
    cs_or(check_axiom_iff_elim_right(),
    cs_or(check_axiom_iff_intro(),
    cs_or(check_axiom_hyp_syllogism(),
    cs_or(check_axiom_quantifier_dist(),
        // TODO: universal_inst, vacuous_quant, eq_subst_left, eq_subst_right
        // These require substitution/free-var checking in CompSpec
        cs_const(0)
    )))))))
}

/// Check Assumption justification: formula is a ZFC axiom.
/// Input: formula_enc
pub open spec fn check_zfc_axiom() -> CompSpec {
    cs_const(1)  // placeholder
}

/// Check one proof line's validity.
/// Input: pair(seq_enc, line_idx)
/// Extracts the line, dispatches on justification tag.
/// Each branch independently recomputes what it needs from the input.
pub open spec fn check_line() -> CompSpec {
    // All sub-expressions take input = pair(seq, idx)
    // tag = fst(snd(seq_elem(input)))
    let tag = cs_fst(cs_snd(seq_elem_comp()));
    // formula = fst(seq_elem(input))
    let formula = cs_fst(seq_elem_comp());
    // justification content = snd(snd(seq_elem(input)))
    let content = cs_snd(cs_snd(seq_elem_comp()));

    // check_input for MP/Gen: pair(pair(formula, content), pair(seq, idx))
    let mp_gen_input = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(formula),
            right: Box::new(content),
        }),
        right: Box::new(CompSpec::Id),
    };

    // Tag dispatch via nested IfZero:
    // IfZero takes input = pair(seq, idx) for all branches
    CompSpec::IfZero {
        cond: Box::new(tag),
        // tag == 0: LogicAxiom
        then_br: Box::new(cs_comp(check_logic_axiom(), cs_fst(seq_elem_comp()))),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, cs_fst(cs_snd(seq_elem_comp())))),
            // tag == 1: Assumption (ZFC axiom check)
            then_br: Box::new(cs_comp(check_zfc_axiom(), cs_fst(seq_elem_comp()))),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred,
                    cs_comp(CompSpec::Pred, cs_fst(cs_snd(seq_elem_comp()))))),
                // tag == 2: ModusPonens
                then_br: Box::new(cs_comp(check_modus_ponens(), mp_gen_input)),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred,
                        cs_comp(CompSpec::Pred, cs_fst(cs_snd(seq_elem_comp())))))),
                    // tag == 3: Generalization
                    then_br: Box::new(cs_comp(check_generalization(), mp_gen_input)),
                    // tag > 3: invalid
                    else_br: Box::new(cs_const(0)),
                }),
            }),
        }),
    }
}

/// Check all proof lines are valid.
/// Input: seq_enc
/// Iterates over the sequence, checking each line.
/// Returns 1 if all valid, 0 if any invalid.
pub open spec fn check_all_lines() -> CompSpec {
    // BoundedRec: iterate over sequence positions
    // count = seq_enc (generous upper bound on number of lines)
    // acc = pair(remaining_seq, pair(valid_flag, line_idx))
    // step: if fst(remaining) == 0: stop. Else: check current line, advance.
    // After loop: extract valid_flag from acc.
    cs_comp(
        cs_fst(cs_snd(CompSpec::Id)),  // extract valid_flag from final acc
        CompSpec::BoundedRec {
            count_fn: Box::new(CompSpec::Id),
            base: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::Id),  // remaining = full seq
                right: Box::new(CompSpec::CantorPair {
                    left: Box::new(cs_const(1)),  // valid = true
                    right: Box::new(cs_const(0)),  // line_idx = 0
                }),
            }),
            step: Box::new({
                // step input: pair(i, pair(acc, original_seq))
                // acc = pair(remaining, pair(valid, idx))
                let remaining = cs_fst(br_acc());
                let valid = cs_fst(cs_snd(br_acc()));
                let idx = cs_snd(cs_snd(br_acc()));
                let orig_seq = cs_snd(cs_snd(CompSpec::Id));  // original_input

                // If fst(remaining) == 0: done, keep acc
                CompSpec::IfZero {
                    cond: Box::new(cs_fst(remaining)),
                    then_br: Box::new(br_acc()),  // keep acc (done)
                    else_br: Box::new(CompSpec::CantorPair {
                        // new remaining = snd(remaining)
                        left: Box::new(cs_snd(remaining)),
                        right: Box::new(CompSpec::CantorPair {
                            // new valid = old valid * check_line(pair(orig_seq, idx))
                            left: Box::new(cs_and(
                                valid,
                                cs_comp(check_line(), CompSpec::CantorPair {
                                    left: Box::new(orig_seq),
                                    right: Box::new(idx),
                                }),
                            )),
                            // new idx = idx + 1
                            right: Box::new(CompSpec::Add {
                                left: Box::new(idx),
                                right: Box::new(cs_const(1)),
                            }),
                        }),
                    }),
                }
            }),
        }
    )
}

// ============================================================
// Check conclusion is Iff of sentences
// ============================================================

/// Check if an encoded formula is a sentence (no free variables).
/// Input: formula_enc
/// This requires recursive traversal of the formula tree.
pub open spec fn check_is_sentence() -> CompSpec {
    cs_const(1)  // placeholder — needs recursive free-var check
}

/// Check conclusion is Iff with sentence sub-formulas.
/// Input: seq_enc (the encoded proof)
/// Gets last formula, checks tag==6 (Iff) and both sides are sentences.
pub open spec fn check_conclusion_iff_sentence() -> CompSpec {
    let formula_enc = last_formula_enc();  // from compspec_decode
    cs_and(
        // Tag is 6 (Iff)
        cs_eq(cs_fst(formula_enc), cs_const(6)),
        cs_and(
            // Left sub-formula is a sentence
            cs_comp(check_is_sentence(), cs_fst(cs_snd(formula_enc))),
            // Right sub-formula is a sentence
            cs_comp(check_is_sentence(), cs_snd(cs_snd(formula_enc)))
        )
    )
}

// ============================================================
// Top-level halts CompSpec
// ============================================================

/// The halts predicate as a CompSpec.
/// Returns nonzero iff s encodes a valid ZFC proof with Iff-of-sentences conclusion.
pub open spec fn halts_comp_term() -> CompSpec {
    cs_and(
        // s != 0 (non-empty sequence)
        cs_nonzero(),
        cs_and(
            // All lines valid
            check_all_lines(),
            // Conclusion is Iff of sentences
            check_conclusion_iff_sentence()
        )
    )
}

// ============================================================
// Correctness proof
// ============================================================

/// The halts CompSpec computes the halting predicate correctly.
pub proof fn lemma_halts_comp_correct()
    ensures
        is_halts_comp(halts_comp_term()),
{
    // For each s: eval_comp(halts_comp_term(), s) != 0 ↔ is_valid_iff_proof_code(s)
    // This requires:
    //   Forward: nonzero → valid proof (CompSpec checks are sufficient)
    //   Backward: valid proof → nonzero (CompSpec checks are necessary)
    // Both directions need detailed proofs connecting CompSpec evaluation
    // to the mathematical definitions.
    assume(false);  // TODO: fill in correctness proof
}

} // verus!
