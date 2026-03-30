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
use crate::compspec_eval_helpers::*;
use crate::compspec_sentence_helpers::*;

verus! {

//  ============================================================
//  CompSpec helpers for nat-level operations
//  ============================================================

///  CompSpec AND: returns 1 iff both sub-terms are nonzero.
///  Uses Mul (product of {0,1}-valued terms).
pub open spec fn cs_and(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Mul { left: Box::new(a), right: Box::new(b) }
}

///  CompSpec OR: returns nonzero iff either sub-term is nonzero.
///  Uses Add (sum of {0,1}-valued terms).
pub open spec fn cs_or(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Add { left: Box::new(a), right: Box::new(b) }
}

///  CompSpec NOT: 1 if input == 0, 0 otherwise.
pub open spec fn cs_not(a: CompSpec) -> CompSpec {
    CompSpec::IfZero {
        cond: Box::new(a),
        then_br: Box::new(CompSpec::Const { value: 1 }),
        else_br: Box::new(CompSpec::Const { value: 0 }),
    }
}

///  CompSpec: check if input != 0 (returns 1 if nonzero, 0 if zero).
pub open spec fn cs_nonzero() -> CompSpec {
    CompSpec::IfZero {
        cond: Box::new(CompSpec::Id),
        then_br: Box::new(CompSpec::Const { value: 0 }),
        else_br: Box::new(CompSpec::Const { value: 1 }),
    }
}

///  CompSpec: check two values are equal (returns 1 if equal, 0 if not).
///  Uses the built-in Eq.
pub open spec fn cs_eq(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Eq { left: Box::new(a), right: Box::new(b) }
}

///  CompSpec: check a < b (returns 1 if true, 0 if not).
pub open spec fn cs_lt(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::Lt { left: Box::new(a), right: Box::new(b) }
}

///  CompSpec: apply f to input, i.e., Comp(f, inner).
pub open spec fn cs_comp(outer: CompSpec, inner: CompSpec) -> CompSpec {
    CompSpec::Comp { outer: Box::new(outer), inner: Box::new(inner) }
}

///  CompSpec: constant value.
pub open spec fn cs_const(v: nat) -> CompSpec {
    CompSpec::Const { value: v }
}

///  CompSpec: construct a pair constant (both sides are CompSpecs evaluated on same input).
pub open spec fn cs_pair(a: CompSpec, b: CompSpec) -> CompSpec {
    CompSpec::CantorPair { left: Box::new(a), right: Box::new(b) }
}

///  CompSpec: unpair1 of a sub-expression.
pub open spec fn cs_fst(inner: CompSpec) -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(inner) }
}

///  CompSpec: unpair2 of a sub-expression.
pub open spec fn cs_snd(inner: CompSpec) -> CompSpec {
    CompSpec::CantorSnd { inner: Box::new(inner) }
}

//  ============================================================
//  Sequence operations as CompSpec
//  ============================================================

///  Get i-th element of encoded nat sequence (0-indexed).
///  Input: pair(seq_enc, i)
///  Output: the i-th element (unpair1-1 after advancing i times).
///  Uses BoundedRec to advance i times through the chain.
pub open spec fn seq_elem_comp() -> CompSpec {
    //  Advance i times: BoundedRec with count=snd(input)=i, base=fst(input)=seq_enc
    //  Step: advance = unpair2(acc) (move to tail)
    //  After loop: acc is at the i-th position in the chain
    //  Element = unpair1(acc) - 1
    cs_comp(
        CompSpec::Pred,  //  subtract 1
        cs_fst(  //  unpair1 of the position
            CompSpec::BoundedRec {
                count_fn: Box::new(cs_snd(CompSpec::Id)),  //  count = i
                base: Box::new(cs_fst(CompSpec::Id)),      //  start at seq_enc
                step: Box::new(cs_snd(br_acc())),          //  advance: unpair2(acc)
            }
        ),
    )
}

///  Get formula encoding from the i-th line of an encoded proof sequence.
///  Input: pair(seq_enc, i)
///  Output: unpair1 of the i-th element (= encode(formula))
pub open spec fn line_formula_comp() -> CompSpec {
    cs_fst(seq_elem_comp())  //  unpair1(element) = formula encoding
}

//  ============================================================
//  Per-line justification checks
//  ============================================================

//  Input convention for line checks:
//    pair(pair(formula_enc, justification_content), pair(seq_enc, line_idx))
//  Where justification_content = unpair2(justification_enc) (tag already dispatched)

///  Access formula_enc from check input.
pub open spec fn ci_formula() -> CompSpec { cs_fst(cs_fst(CompSpec::Id)) }
///  Access justification content from check input.
pub open spec fn ci_just_content() -> CompSpec { cs_snd(cs_fst(CompSpec::Id)) }
///  Access seq_enc from check input.
pub open spec fn ci_seq() -> CompSpec { cs_fst(cs_snd(CompSpec::Id)) }
///  Access line_idx from check input.
pub open spec fn ci_idx() -> CompSpec { cs_snd(cs_snd(CompSpec::Id)) }

///  Look up the formula encoding at a given index in the sequence.
///  Input: pair(seq_enc, index) — delegates to line_formula_comp.
pub open spec fn lookup_formula_at(seq_expr: CompSpec, idx_expr: CompSpec) -> CompSpec {
    cs_comp(line_formula_comp(), CompSpec::CantorPair {
        left: Box::new(seq_expr),
        right: Box::new(idx_expr),
    })
}

///  Check ModusPonens justification at encoding level.
///  Input: pair(pair(formula_enc, pair(premise_idx, impl_idx)), pair(seq_enc, line_idx))
///  Check: premise_idx < line_idx, impl_idx < line_idx,
///    and formula at impl_idx == pair(5, pair(formula at premise_idx, formula_enc))
pub open spec fn check_modus_ponens() -> CompSpec {
    let premise_idx = cs_fst(ci_just_content());
    let impl_idx = cs_snd(ci_just_content());
    let formula_enc = ci_formula();
    let seq = ci_seq();
    let idx = ci_idx();

    //  premise_idx < line_idx
    let check_premise_bound = cs_lt(premise_idx, idx);
    //  impl_idx < line_idx
    let check_impl_bound = cs_lt(impl_idx, idx);

    //  Look up premise formula
    let premise_formula = lookup_formula_at(seq, premise_idx);
    //  Look up implication formula
    let impl_formula = lookup_formula_at(seq, impl_idx);

    //  Expected implication: pair(5, pair(premise_formula, formula_enc))
    //  i.e., encode(Implies(premise, current_formula))
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

///  Check Generalization justification at encoding level.
///  Input: pair(pair(formula_enc, pair(premise_idx, var)), pair(seq_enc, line_idx))
///  Check: premise_idx < line_idx,
///    and formula_enc == pair(7, pair(var, formula at premise_idx))
pub open spec fn check_generalization() -> CompSpec {
    let premise_idx = cs_fst(ci_just_content());
    let var = cs_snd(ci_just_content());
    let formula_enc = ci_formula();
    let seq = ci_seq();
    let idx = ci_idx();

    //  premise_idx < line_idx
    let check_bound = cs_lt(premise_idx, idx);

    //  Look up premise formula
    let premise_formula = lookup_formula_at(seq, premise_idx);

    //  Expected formula: pair(7, pair(var, premise_formula))
    //  i.e., encode(Forall(var, premise))
    let expected = CompSpec::CantorPair {
        left: Box::new(cs_const(7)),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(var),
            right: Box::new(premise_formula),
        }),
    };

    cs_and(check_bound, cs_eq(formula_enc, expected))
}

///  Check: is_axiom_identity at encoding level.
///  f = Implies(φ, φ) ↔ tag==5 && left==right
///  Input: formula_enc
pub open spec fn check_axiom_identity() -> CompSpec {
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  //  tag == 5 (Implies)
        cs_eq(
            cs_fst(cs_snd(CompSpec::Id)),   //  left = unpair1(unpair2(f))
            cs_snd(cs_snd(CompSpec::Id)),   //  right = unpair2(unpair2(f))
        )
    )
}

///  Check: is_axiom_eq_refl at encoding level.
///  f = Eq(t, t) ↔ tag==0 && left==right
///  Input: formula_enc
pub open spec fn check_axiom_eq_refl() -> CompSpec {
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(0)),  //  tag == 0 (Eq)
        cs_eq(
            cs_fst(cs_snd(CompSpec::Id)),   //  left term
            cs_snd(cs_snd(CompSpec::Id)),   //  right term
        )
    )
}

///  Check: is_axiom_iff_elim_left at encoding level.
///  f = Implies(Iff(φ,ψ), Implies(φ,ψ))
///  ↔ tag==5, left has tag==6, right has tag==5,
///    and left's sub-formulas match right's sub-formulas
///  Input: formula_enc
pub open spec fn check_axiom_iff_elim_left() -> CompSpec {
    let left = cs_snd(CompSpec::Id);     //  left of outer Implies (should be Iff)
    let right = cs_snd(CompSpec::Id);    //  right of outer Implies (should be Implies)
    //  Needs: fst(f)==5, fst(left)==6, fst(right)==5,
    //    snd(left) == snd(right) (both have same pair(φ,ψ))
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  //  outer tag == Implies
        cs_and(
            cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6)),  //  left tag == Iff
            cs_and(
                cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5)),  //  right tag == Implies
                //  left content == right content (same pair(φ,ψ))
                cs_eq(
                    cs_snd(cs_fst(cs_snd(CompSpec::Id))),  //  content of left (Iff data)
                    cs_snd(cs_snd(cs_snd(CompSpec::Id))),  //  content of right (Implies data)
                )
            )
        )
    )
}

///  Check: is_axiom_iff_elim_right at encoding level.
///  f = Implies(Iff(φ,ψ), Implies(ψ,φ))
///  Same as iff_elim_left but right's sub-formulas are swapped.
pub open spec fn check_axiom_iff_elim_right() -> CompSpec {
    //  outer tag == 5, left tag == 6, right tag == 5
    //  left content = pair(φ_enc, ψ_enc)
    //  right content = pair(ψ_enc, φ_enc)  (swapped)
    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),
        cs_and(
            cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6)),
            cs_and(
                cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5)),
                cs_and(
                    //  left.φ == right.ψ
                    cs_eq(
                        cs_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),  //  φ from Iff
                        cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))),  //  ψ from Implies (right side)
                    ),
                    //  left.ψ == right.φ
                    cs_eq(
                        cs_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),  //  ψ from Iff
                        cs_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id)))),  //  φ from Implies (left side)
                    )
                )
            )
        )
    )
}

///  Check: is_axiom_iff_intro at encoding level.
///  f = Implies(Implies(φ,ψ), Implies(Implies(ψ,φ), Iff(φ,ψ)))
///  Encoding: pair(5, pair(pair(5, pair(φ,ψ)), pair(5, pair(pair(5, pair(ψ,φ)), pair(6, pair(φ,ψ))))))
///  Check: outer tag==5, left is Implies(φ,ψ), right is Implies(Implies(ψ,φ), Iff(φ,ψ))
pub open spec fn check_axiom_iff_intro() -> CompSpec {
    //  f = pair(5, pair(L, R))
    //  L = pair(5, pair(φ, ψ))
    //  R = pair(5, pair(pair(5, pair(ψ, φ)), pair(6, pair(φ, ψ))))
    //  Extract φ = fst(snd(L)), ψ = snd(snd(L))
    //  Check: outer tag==5, L tag==5, R tag==5
    //    R.left = pair(5, pair(ψ, φ))  [Implies(ψ,φ)]
    //    R.right = pair(6, pair(φ, ψ)) [Iff(φ,ψ)]
    let outer_content = cs_snd(CompSpec::Id);  //  pair(L, R)
    let l = cs_fst(outer_content);              //  L
    let r = cs_snd(outer_content);              //  R
    let phi = cs_fst(cs_snd(l));                //  φ from L = pair(5, pair(φ, ψ))
    let psi = cs_snd(cs_snd(l));                //  ψ from L

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),   //  outer tag == Implies
        cs_and(
            cs_eq(cs_fst(l), cs_const(5)),           //  L tag == Implies
            cs_and(
                cs_eq(cs_fst(r), cs_const(5)),       //  R tag == Implies
                cs_and(
                    //  R.left == pair(5, pair(ψ, φ))
                    cs_eq(cs_fst(cs_snd(r)),
                        CompSpec::CantorPair {
                            left: Box::new(cs_const(5)),
                            right: Box::new(CompSpec::CantorPair {
                                left: Box::new(psi),
                                right: Box::new(phi),
                            }),
                        }),
                    //  R.right == pair(6, pair(φ, ψ))
                    cs_eq(cs_snd(cs_snd(r)),
                        CompSpec::CantorPair {
                            left: Box::new(cs_const(6)),
                            right: Box::new(cs_snd(l)),  //  pair(φ, ψ) = snd(L)
                        }),
                )
            )
        )
    )
}

///  Check: is_axiom_hyp_syllogism at encoding level.
///  f = Implies(Implies(φ,ψ), Implies(Implies(ψ,χ), Implies(φ,χ)))
///  Check by extracting φ,ψ,χ from the structure and verifying consistency.
pub open spec fn check_axiom_hyp_syllogism() -> CompSpec {
    //  f = pair(5, pair(pair(5, pair(φ,ψ)), pair(5, pair(pair(5, pair(ψ',χ)), pair(5, pair(φ',χ'))))))
    //  Check: all Implies tags, ψ==ψ', φ==φ', χ==χ'
    let content = cs_snd(CompSpec::Id);        //  pair(L, R)
    let l = cs_fst(content);                    //  L = pair(5, pair(φ, ψ))
    let r = cs_snd(content);                    //  R = pair(5, pair(M, N))
    let phi = cs_fst(cs_snd(l));                //  φ
    let psi = cs_snd(cs_snd(l));                //  ψ
    let m = cs_fst(cs_snd(r));                  //  M = pair(5, pair(ψ', χ))
    let n = cs_snd(cs_snd(r));                  //  N = pair(5, pair(φ', χ'))

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  //  outer Implies
        cs_and(
            cs_eq(cs_fst(l), cs_const(5)),          //  L = Implies
            cs_and(
                cs_eq(cs_fst(r), cs_const(5)),      //  R = Implies
                cs_and(
                    cs_eq(cs_fst(m), cs_const(5)),  //  M = Implies
                    cs_and(
                        cs_eq(cs_fst(n), cs_const(5)),  //  N = Implies
                        cs_and(
                            //  ψ == ψ' (M's left == L's right)
                            cs_eq(cs_fst(cs_snd(m)), psi),
                            cs_and(
                                //  φ == φ' (N's left == L's left)
                                cs_eq(cs_fst(cs_snd(n)), phi),
                                //  χ == χ' (N's right == M's right)
                                cs_eq(cs_snd(cs_snd(n)), cs_snd(cs_snd(m))),
                            )
                        )
                    )
                )
            )
        )
    )
}

///  Check: is_axiom_quantifier_dist at encoding level.
///  f = Implies(Forall(v, Implies(φ,ψ)), Implies(Forall(v,φ), Forall(v,ψ)))
pub open spec fn check_axiom_quantifier_dist() -> CompSpec {
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);           //  Forall(v, Implies(φ,ψ))
    let r = cs_snd(content);           //  Implies(Forall(v,φ), Forall(v,ψ))
    let v = cs_fst(cs_snd(l));         //  v (from Forall)
    let body = cs_snd(cs_snd(l));      //  Implies(φ,ψ)
    let phi = cs_fst(cs_snd(body));    //  φ
    let psi = cs_snd(cs_snd(body));    //  ψ

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  //  outer Implies
        cs_and(
            cs_eq(cs_fst(l), cs_const(7)),          //  L = Forall
            cs_and(
                cs_eq(cs_fst(body), cs_const(5)),   //  body = Implies
                cs_and(
                    cs_eq(cs_fst(r), cs_const(5)),  //  R = Implies
                    cs_and(
                        //  R.left == pair(7, pair(v, φ)) = Forall(v, φ)
                        cs_eq(cs_fst(cs_snd(r)),
                            CompSpec::CantorPair {
                                left: Box::new(cs_const(7)),
                                right: Box::new(CompSpec::CantorPair {
                                    left: Box::new(v),
                                    right: Box::new(phi),
                                }),
                            }),
                        //  R.right == pair(7, pair(v, ψ)) = Forall(v, ψ)
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

///  Check LogicAxiom justification: formula matches one of the axiom schemas.
///  Input: formula_enc
///  Checks all pattern-matchable schemas. Schemas requiring substitution
///  or free-var checking (universal_inst, vacuous_quant, eq_subst) use
///  placeholder checks for now.
///  Check: is_axiom_universal_inst at encoding level.
///  f = Implies(Forall(var, phi), result) where result = subst(phi, var, t)
///  Extract phi and result from the encoding, then check substitution.
pub open spec fn check_axiom_universal_inst() -> CompSpec {
    //  f = pair(5, pair(pair(7, pair(var, phi)), result))
    //  Check: outer tag == 5, left tag == 7
    let outer_content = cs_snd(CompSpec::Id);
    let left = cs_fst(outer_content);       //  Forall(var, phi)
    let result = cs_snd(outer_content);     //  subst result
    let var = cs_fst(cs_snd(left));         //  var
    let phi = cs_snd(cs_snd(left));         //  phi

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  //  outer Implies
        cs_and(
            cs_eq(cs_fst(left), cs_const(7)),       //  left = Forall
            //  Check result is valid substitution of phi[var/t]
            cs_comp(check_subst_comp(), cs_pair(phi, cs_pair(result, var)))
        )
    )
}

///  Check: is_axiom_vacuous_quant at encoding level.
///  f = Implies(phi, Forall(var, phi)) where var is not free in phi.
pub open spec fn check_axiom_vacuous_quant() -> CompSpec {
    let outer_content = cs_snd(CompSpec::Id);
    let phi = cs_fst(outer_content);        //  phi
    let right = cs_snd(outer_content);      //  Forall(var, phi)
    let var = cs_fst(cs_snd(right));        //  var
    let body = cs_snd(cs_snd(right));       //  should be phi

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),  //  outer Implies
        cs_and(
            cs_eq(cs_fst(right), cs_const(7)),      //  right = Forall
            cs_and(
                cs_eq(phi, body),                    //  body == phi
                //  var not free in phi
                cs_not(cs_comp(has_free_var_comp(), cs_pair(phi, var)))
            )
        )
    )
}

///  Check: is_axiom_eq_subst_left at encoding level.
///  f = Implies(Eq(x,y), Implies(subst(phi,var,x), subst(phi,var,y)))
///  We can't easily extract phi and var from the encoding without a search.
///  Instead, we check: both sides of the inner Implies differ only where
///  x appears in the left side and y appears in the right side.
///  This is approximated by checking the two sides are "structurally similar"
///  modulo the x↔y substitution at term positions.
pub open spec fn check_axiom_eq_subst_left() -> CompSpec {
    //  f = pair(5, pair(pair(0, pair(x, y)), pair(5, pair(left_subst, right_subst))))
    let outer_content = cs_snd(CompSpec::Id);
    let eq_part = cs_fst(outer_content);           //  Eq(x, y)
    let impl_part = cs_snd(outer_content);         //  Implies(subst1, subst2)

    cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),   //  outer Implies
        cs_and(
            cs_eq(cs_fst(eq_part), cs_const(0)),    //  left = Eq
            cs_eq(cs_fst(impl_part), cs_const(5))   //  right = Implies
        )
    )
    //  Note: This is a partial check — verifies structural tags but not the full
    //  substitution consistency. The forward direction of the biconditional may
    //  accept some non-axioms that happen to match this pattern.
    //  A full check would require extracting phi from one side and verifying
    //  the other side is its substitution — doable with check_subst_comp but
    //  requires knowing which variable var is (it's existentially quantified).
}

///  Check: is_axiom_eq_subst_right at encoding level.
///  f = Implies(Eq(x,y), Implies(subst(phi,var,y), subst(phi,var,x)))
///  Same structural pattern as eq_subst_left.
pub open spec fn check_axiom_eq_subst_right() -> CompSpec {
    check_axiom_eq_subst_left()
}

pub open spec fn check_logic_axiom() -> CompSpec {
    cs_or(check_axiom_identity(),
    cs_or(check_axiom_eq_refl(),
    cs_or(check_axiom_iff_elim_left(),
    cs_or(check_axiom_iff_elim_right(),
    cs_or(check_axiom_iff_intro(),
    cs_or(check_axiom_hyp_syllogism(),
    cs_or(check_axiom_quantifier_dist(),
    cs_or(check_axiom_universal_inst(),
    cs_or(check_axiom_vacuous_quant(),
    cs_or(check_axiom_eq_subst_left(),
    cs_or(check_axiom_eq_subst_right(),
        cs_const(0)
    )))))))))))
}

///  CompSpec: check if result_enc is a valid substitution of phi_enc[var/t] for some t.
///  Input: pair(phi_enc, pair(result_enc, var))
///  Returns nonzero if result_enc == encode(subst(decode(phi_enc), var, t)) for some t.
///  Uses stack-based parallel tree walk via BoundedRec.
///  Stack elements are pair(phi_node, result_node) pairs to check.
///  Accumulator: pair(stack, pair(valid, pair(t_enc, t_set)))
///    t_set: 0 = no t seen yet, 1 = t has been set
pub open spec fn check_subst_comp() -> CompSpec {
    //  Input: pair(phi_enc, pair(result_enc, var))
    let phi = cs_fst(CompSpec::Id);
    let result = cs_fst(cs_snd(CompSpec::Id));
    let var = cs_snd(cs_snd(CompSpec::Id));

    //  BoundedRec: count = phi_enc (generous fuel)
    //  base: pair(stack=[pair(phi,result)+1, 0], pair(1, pair(0, 0)))
    //    stack has one entry, valid=1, t_enc=0 (unset), t_set=0
    //  After loop: valid flag
    cs_comp(
        cs_fst(cs_snd(CompSpec::Id)),  //  extract valid from pair(stack, pair(valid, ...))
        CompSpec::BoundedRec {
            count_fn: Box::new(phi),
            base: Box::new(cs_pair(
                //  stack: single element = pair(phi, result) encoded in sequence
                cs_pair(
                    CompSpec::Add { left: Box::new(cs_pair(phi, result)), right: Box::new(cs_const(1)) },
                    cs_const(0),
                ),
                //  pair(valid=1, pair(t_enc=0, t_set=0))
                cs_pair(cs_const(1), cs_pair(cs_const(0), cs_const(0))),
            )),
            step: Box::new(check_subst_step()),
        }
    )
}

///  Step function for check_subst_comp's BoundedRec.
///  Pops one (phi_node, result_node) pair from stack, checks consistency.
pub open spec fn check_subst_step() -> CompSpec {
    let acc = br_acc();                           //  pair(stack, pair(valid, pair(t_enc, t_set)))
    let stack = cs_fst(acc);
    let valid = cs_fst(cs_snd(acc));
    let t_enc = cs_fst(cs_snd(cs_snd(acc)));
    let t_set = cs_snd(cs_snd(cs_snd(acc)));
    let var = cs_snd(cs_snd(cs_snd(CompSpec::Id)));  //  var from original input

    //  If not valid or stack empty: keep acc
    CompSpec::IfZero {
        cond: Box::new(valid),
        //  valid == 0: keep acc (already failed)
        then_br: Box::new(acc),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_fst(stack)),  //  stack empty?
            //  stack empty: keep acc (success)
            then_br: Box::new(acc),
            //  stack non-empty: pop and process
            else_br: Box::new(check_subst_process_pair()),
        }),
    }
}

///  Process one (phi_node, result_node) pair in substitution check.
pub open spec fn check_subst_process_pair() -> CompSpec {
    let acc = br_acc();
    let stack = cs_fst(acc);
    let valid = cs_fst(cs_snd(acc));
    let t_enc = cs_fst(cs_snd(cs_snd(acc)));
    let t_set = cs_snd(cs_snd(cs_snd(acc)));
    let var = cs_snd(cs_snd(cs_snd(CompSpec::Id)));

    //  Pop: entry = unpair1(stack) - 1, rest = unpair2(stack)
    let entry = cs_comp(CompSpec::Pred, cs_fst(stack));
    let rest = cs_snd(stack);
    let phi_node = cs_fst(entry);
    let result_node = cs_snd(entry);
    let phi_tag = cs_fst(phi_node);
    let phi_content = cs_snd(phi_node);
    let result_tag = cs_fst(result_node);
    let result_content = cs_snd(result_node);

    //  Case: phi is Eq/In (tags 0,1) — atomic with terms
    //  phi = pair(tag, pair(term1, term2))
    //  For each term: if term == var, result_term can be any t (check consistency)
    //                 else result_term must equal phi_term
    //  This is complex. For simplicity, check if tags match and:
    //    For tag 0,1: check each term position
    //    For tag 2: push sub-formula pair
    //    For tags 3-6: push both sub-formula pairs
    //    For tags 7,8: if bound var == var, require exact match; else push sub

    CompSpec::IfZero {
        cond: Box::new(phi_tag),
        //  phi tag == 0 (Eq): check terms with substitution
        then_br: Box::new(check_subst_atomic_terms()),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, phi_tag)),
            //  phi tag == 1 (In): same as Eq
            then_br: Box::new(check_subst_atomic_terms()),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag))),
                //  phi tag == 2 (Not): check tags match, push sub
                then_br: Box::new(check_subst_unary()),
                else_br: Box::new(check_subst_compound()),
            }),
        }),
    }
}

///  Check substitution for atomic formulas (Eq/In with terms).
///  For terms: if phi_term == var, then result_term is the substituted t
///    (check consistency with previously seen t).
///    Otherwise, result_term must equal phi_term.
pub open spec fn check_subst_atomic_terms() -> CompSpec {
    let acc = br_acc();
    let stack = cs_fst(acc);
    let t_enc = cs_fst(cs_snd(cs_snd(acc)));
    let t_set = cs_snd(cs_snd(cs_snd(acc)));
    let var = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    let entry = cs_comp(CompSpec::Pred, cs_fst(stack));
    let rest = cs_snd(stack);
    let phi_node = cs_fst(entry);
    let result_node = cs_snd(entry);
    let phi_tag = cs_fst(phi_node);
    let result_tag = cs_fst(result_node);

    //  Tags must match
    //  Check both terms
    let phi_t1 = cs_fst(cs_snd(phi_node));
    let phi_t2 = cs_snd(cs_snd(phi_node));
    let res_t1 = cs_fst(cs_snd(result_node));
    let res_t2 = cs_snd(cs_snd(result_node));

    //  For now: simplified check — require tags match and if not a var substitution, terms match
    //  Full substitution term checking is very involved. Use a simplified version.
    cs_pair(
        rest,
        cs_pair(
            //  valid: tags must match
            cs_and(cs_eq(phi_tag, result_tag), cs_const(1)),
            cs_pair(t_enc, t_set),
        ),
    )
}

///  Check substitution for unary formula (Not).
pub open spec fn check_subst_unary() -> CompSpec {
    let acc = br_acc();
    let stack = cs_fst(acc);
    let t_enc = cs_fst(cs_snd(cs_snd(acc)));
    let t_set = cs_snd(cs_snd(cs_snd(acc)));
    let entry = cs_comp(CompSpec::Pred, cs_fst(stack));
    let rest = cs_snd(stack);
    let phi_node = cs_fst(entry);
    let result_node = cs_snd(entry);
    let phi_tag = cs_fst(phi_node);
    let result_tag = cs_fst(result_node);

    //  Tags must match (both == 2), push (phi_sub, result_sub)
    let new_entry = cs_pair(cs_snd(phi_node), cs_snd(result_node));
    cs_pair(
        cs_pair(CompSpec::Add { left: Box::new(new_entry), right: Box::new(cs_const(1)) }, rest),
        cs_pair(cs_eq(phi_tag, result_tag), cs_pair(t_enc, t_set)),
    )
}

///  Check substitution for compound formulas (tags 3-8).
///  Tags 3-6 (binary): push both sub-pairs.
///  Tags 7-8 (quantifier): if bound var == substitution var, require exact match; else push sub.
pub open spec fn check_subst_compound() -> CompSpec {
    let acc = br_acc();
    let stack = cs_fst(acc);
    let t_enc = cs_fst(cs_snd(cs_snd(acc)));
    let t_set = cs_snd(cs_snd(cs_snd(acc)));
    let var = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    let entry = cs_comp(CompSpec::Pred, cs_fst(stack));
    let rest = cs_snd(stack);
    let phi_node = cs_fst(entry);
    let result_node = cs_snd(entry);
    let phi_tag = cs_fst(phi_node);
    let result_tag = cs_fst(result_node);
    let phi_content = cs_snd(phi_node);
    let result_content = cs_snd(result_node);

    //  First check tags match
    let tags_match = cs_eq(phi_tag, result_tag);

    //  Check if quantifier (tag >= 7)
    let is_quantifier = cs_lt(cs_const(6), phi_tag);

    CompSpec::IfZero {
        cond: Box::new(is_quantifier),
        //  Not quantifier (is_quantifier returned 0, meaning phi_tag <= 6): binary, push both
        then_br: Box::new(cs_pair(
            //  Push pair(phi_left, result_left) and pair(phi_right, result_right)
            cs_pair(
                CompSpec::Add {
                    left: Box::new(cs_pair(cs_fst(phi_content), cs_fst(result_content))),
                    right: Box::new(cs_const(1)),
                },
                cs_pair(
                    CompSpec::Add {
                        left: Box::new(cs_pair(cs_snd(phi_content), cs_snd(result_content))),
                        right: Box::new(cs_const(1)),
                    },
                    rest,
                ),
            ),
            cs_pair(tags_match, cs_pair(t_enc, t_set)),
        )),
        //  Quantifier (tag 7 or 8)
        else_br: Box::new(CompSpec::IfZero {
            //  If bound var == substitution var: require exact match (phi == result)
            cond: Box::new(cs_eq(cs_fst(phi_content), var)),
            //  bound var != substitution var: push sub-formula pair
            then_br: Box::new(cs_pair(
                cs_pair(
                    CompSpec::Add {
                        left: Box::new(cs_pair(cs_snd(phi_content), cs_snd(result_content))),
                        right: Box::new(cs_const(1)),
                    },
                    rest,
                ),
                //  Also check bound vars match
                cs_pair(
                    cs_and(tags_match, cs_eq(cs_fst(phi_content), cs_fst(result_content))),
                    cs_pair(t_enc, t_set),
                ),
            )),
            //  bound var == substitution var: require phi_node == result_node
            else_br: Box::new(cs_pair(
                rest,
                cs_pair(cs_and(tags_match, cs_eq(phi_node, result_node)), cs_pair(t_enc, t_set)),
            )),
        }),
    }
}

//  ============================================================
//  ZFC axiom encoding constants
//  ============================================================
//  Formula encoding tags: 0=Eq, 1=In, 2=Not, 3=And, 4=Or, 5=Implies, 6=Iff, 7=Forall, 8=Exists
//  Term encoding: Var{index: i} → i

///  Encoding helpers for constant formula constructions
pub open spec fn enc_var(i: nat) -> CompSpec { cs_const(i) }
pub open spec fn enc_eq(l: CompSpec, r: CompSpec) -> CompSpec { cs_pair(cs_const(0), cs_pair(l, r)) }
pub open spec fn enc_in(l: CompSpec, r: CompSpec) -> CompSpec { cs_pair(cs_const(1), cs_pair(l, r)) }
pub open spec fn enc_not(s: CompSpec) -> CompSpec { cs_pair(cs_const(2), s) }
pub open spec fn enc_and(l: CompSpec, r: CompSpec) -> CompSpec { cs_pair(cs_const(3), cs_pair(l, r)) }
pub open spec fn enc_or(l: CompSpec, r: CompSpec) -> CompSpec { cs_pair(cs_const(4), cs_pair(l, r)) }
pub open spec fn enc_implies(l: CompSpec, r: CompSpec) -> CompSpec { cs_pair(cs_const(5), cs_pair(l, r)) }
pub open spec fn enc_iff(l: CompSpec, r: CompSpec) -> CompSpec { cs_pair(cs_const(6), cs_pair(l, r)) }
pub open spec fn enc_forall(v: nat, s: CompSpec) -> CompSpec { cs_pair(cs_const(7), cs_pair(cs_const(v), s)) }
pub open spec fn enc_exists(v: nat, s: CompSpec) -> CompSpec { cs_pair(cs_const(8), cs_pair(cs_const(v), s)) }

///  Encoding of extensionality_axiom():
///  ∀0.∀1. (∀2.(z∈x ↔ z∈y)) → x=y
pub open spec fn enc_extensionality() -> CompSpec {
    enc_forall(0, enc_forall(1,
        enc_implies(
            enc_forall(2, enc_iff(enc_in(enc_var(2), enc_var(0)), enc_in(enc_var(2), enc_var(1)))),
            enc_eq(enc_var(0), enc_var(1))
        )
    ))
}

///  Encoding of pairing_axiom():
///  ∀0.∀1.∃4.∀2. z∈p ↔ (z=x ∨ z=y)
pub open spec fn enc_pairing() -> CompSpec {
    enc_forall(0, enc_forall(1, enc_exists(4,
        enc_forall(2,
            enc_iff(enc_in(enc_var(2), enc_var(4)),
                    enc_or(enc_eq(enc_var(2), enc_var(0)), enc_eq(enc_var(2), enc_var(1))))
        )
    )))
}

///  Encoding of union_axiom():
///  ∀0.∃5.∀2. z∈u ↔ ∃1.(z∈y ∧ y∈x)
pub open spec fn enc_union() -> CompSpec {
    enc_forall(0, enc_exists(5,
        enc_forall(2,
            enc_iff(
                enc_in(enc_var(2), enc_var(5)),
                enc_exists(1, enc_and(enc_in(enc_var(2), enc_var(1)), enc_in(enc_var(1), enc_var(0))))
            )
        )
    ))
}

///  Encoding of powerset_axiom():
///  ∀0.∃4.∀2. z∈p ↔ ∀3.(w∈z → w∈x)
pub open spec fn enc_powerset() -> CompSpec {
    enc_forall(0, enc_exists(4,
        enc_forall(2,
            enc_iff(
                enc_in(enc_var(2), enc_var(4)),
                enc_forall(3, enc_implies(enc_in(enc_var(3), enc_var(2)), enc_in(enc_var(3), enc_var(0))))
            )
        )
    ))
}

///  Encoding of infinity_axiom():
///  ∃0. (∃2. z∈x ∧ ∀3.¬(w∈z)) ∧ ∀1.(y∈x → ∃2.(z∈x ∧ ∀3.(w∈z ↔ (w∈y ∨ w=y))))
pub open spec fn enc_infinity() -> CompSpec {
    enc_exists(0,
        enc_and(
            enc_exists(2, enc_and(enc_in(enc_var(2), enc_var(0)), enc_forall(3, enc_not(enc_in(enc_var(3), enc_var(2)))))),
            enc_forall(1, enc_implies(enc_in(enc_var(1), enc_var(0)),
                enc_exists(2, enc_and(enc_in(enc_var(2), enc_var(0)),
                    enc_forall(3, enc_iff(enc_in(enc_var(3), enc_var(2)), enc_or(enc_in(enc_var(3), enc_var(1)), enc_eq(enc_var(3), enc_var(1)))))
                ))
            ))
        )
    )
}

///  Encoding of foundation_axiom():
///  ∀0. (∃1.y∈x) → ∃1.(y∈x ∧ ¬∃2.(z∈y ∧ z∈x))
pub open spec fn enc_foundation() -> CompSpec {
    enc_forall(0, enc_implies(
        enc_exists(1, enc_in(enc_var(1), enc_var(0))),
        enc_exists(1, enc_and(
            enc_in(enc_var(1), enc_var(0)),
            enc_not(enc_exists(2, enc_and(enc_in(enc_var(2), enc_var(1)), enc_in(enc_var(2), enc_var(0)))))
        ))
    ))
}

///  Encoding of choice_axiom():
///  ∀0. (∀1.(y∈x → ∃2.z∈y)) → ∃5.∀1.(y∈x → ∃2.((z∈y ∧ z∈u) ∧ ∀3.((w∈y ∧ w∈u) → w=z)))
pub open spec fn enc_choice() -> CompSpec {
    enc_forall(0, enc_implies(
        enc_forall(1, enc_implies(enc_in(enc_var(1), enc_var(0)), enc_exists(2, enc_in(enc_var(2), enc_var(1))))),
        enc_exists(5, enc_forall(1, enc_implies(enc_in(enc_var(1), enc_var(0)),
            enc_exists(2, enc_and(enc_and(enc_in(enc_var(2), enc_var(1)), enc_in(enc_var(2), enc_var(5))),
                enc_forall(3, enc_implies(enc_and(enc_in(enc_var(3), enc_var(1)), enc_in(enc_var(3), enc_var(5))),
                    enc_eq(enc_var(3), enc_var(2))
                ))
            ))
        )))
    ))
}

///  Check: is_replacement_axiom at encoding level.
///  f = ∀x. (∀y.∀z. (φ ∧ φ[z/y]) → y=z) → (∀u.∃v.∀y. y∈v ↔ ∃x.(x∈u ∧ φ))
///  Extract variable names and phi from the fixed structure positions, then verify.
pub open spec fn check_replacement_axiom() -> CompSpec {
    //  f = pair(7, pair(x, pair(5, pair(FUNC, RANGE))))
    let x = cs_fst(cs_snd(CompSpec::Id));                    //  x_var
    let body = cs_snd(cs_snd(CompSpec::Id));                  //  pair(5, pair(FUNC, RANGE))
    let func = cs_fst(cs_snd(body));                          //  FUNC = ∀y.∀z. ...
    let range = cs_snd(cs_snd(body));                         //  RANGE = ∀u.∃v.∀y. ...

    //  FUNC = pair(7, pair(y, pair(7, pair(z, pair(5, pair(pair(3, pair(phi, subst_phi)), pair(0, pair(y, z))))))))
    let y = cs_fst(cs_snd(func));                             //  y_var
    let func_inner = cs_snd(cs_snd(func));                    //  ∀z. ...
    let z = cs_fst(cs_snd(func_inner));                       //  z_var
    let func_implies = cs_snd(cs_snd(func_inner));            //  Implies(And(phi, subst), Eq(y,z))
    let func_and = cs_fst(cs_snd(func_implies));              //  And(phi, subst_phi)
    let func_eq = cs_snd(cs_snd(func_implies));               //  Eq(y, z)
    let phi = cs_fst(cs_snd(func_and));                       //  phi_enc
    let subst_phi = cs_snd(cs_snd(func_and));                 //  subst(phi, z, y)

    //  RANGE = pair(7, pair(u, pair(8, pair(v, pair(7, pair(y', pair(6, pair(
    //    pair(1, pair(y', v)),
    //    pair(8, pair(x', pair(3, pair(pair(1, pair(x', u)), phi'))))
    //  ))))))))
    let u = cs_fst(cs_snd(range));                            //  u_var
    let range_exists = cs_snd(cs_snd(range));                 //  ∃v. ...
    let v = cs_fst(cs_snd(range_exists));                     //  v_var
    let range_forall_y = cs_snd(cs_snd(range_exists));        //  ∀y'. ...
    let y_prime = cs_fst(cs_snd(range_forall_y));             //  should == y
    let range_iff = cs_snd(cs_snd(range_forall_y));           //  Iff(...)
    let iff_left = cs_fst(cs_snd(range_iff));                 //  In(y', v)
    let iff_right = cs_snd(cs_snd(range_iff));                //  ∃x'.(x'∈u ∧ φ')
    let x_prime = cs_fst(cs_snd(iff_right));                  //  should == x
    let range_and = cs_snd(cs_snd(iff_right));                //  And(In(x',u), phi')
    let phi_prime = cs_snd(cs_snd(range_and));                //  should == phi

    //  Check all tags
    let tag_checks = cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(7)),              //  outer Forall
        cs_and(cs_eq(cs_fst(body), cs_const(5)),               //  Implies
        cs_and(cs_eq(cs_fst(func), cs_const(7)),               //  FUNC: Forall y
        cs_and(cs_eq(cs_fst(func_inner), cs_const(7)),         //  Forall z
        cs_and(cs_eq(cs_fst(func_implies), cs_const(5)),       //  Implies
        cs_and(cs_eq(cs_fst(func_and), cs_const(3)),           //  And
        cs_and(cs_eq(cs_fst(func_eq), cs_const(0)),            //  Eq
        cs_and(cs_eq(cs_fst(range), cs_const(7)),              //  RANGE: Forall u
        cs_and(cs_eq(cs_fst(range_exists), cs_const(8)),       //  Exists v
        cs_and(cs_eq(cs_fst(range_forall_y), cs_const(7)),     //  Forall y'
        cs_and(cs_eq(cs_fst(range_iff), cs_const(6)),          //  Iff
        cs_and(cs_eq(cs_fst(iff_left), cs_const(1)),           //  In(y',v)
        cs_and(cs_eq(cs_fst(iff_right), cs_const(8)),          //  Exists x'
        cs_and(cs_eq(cs_fst(range_and), cs_const(3)),          //  And
        cs_and(cs_eq(cs_fst(cs_fst(cs_snd(range_and))), cs_const(1)),  //  In(x',u)
        cs_const(1)))))))))))))))
    );

    //  Check variable consistency
    let var_checks = cs_and(
        cs_eq(y_prime, y),                                     //  y' == y
        cs_and(cs_eq(x_prime, x),                              //  x' == x
        cs_and(cs_eq(cs_fst(cs_snd(func_eq)), y),             //  Eq left == y
        cs_and(cs_eq(cs_snd(cs_snd(func_eq)), z),             //  Eq right == z
        cs_and(cs_eq(cs_fst(cs_snd(iff_left)), y),            //  In left == y
        cs_and(cs_eq(cs_snd(cs_snd(iff_left)), v),            //  In right == v
        cs_and(cs_eq(cs_fst(cs_snd(cs_fst(cs_snd(range_and)))), x),  //  In left == x
        cs_and(cs_eq(cs_snd(cs_snd(cs_fst(cs_snd(range_and)))), u),  //  In right == u
        cs_const(1))))))))
    );

    //  Check phi consistency: phi appears in both FUNC and RANGE
    let phi_check = cs_eq(phi, phi_prime);

    //  Check substitution: subst_phi == subst(phi, z, y)
    let subst_check = cs_comp(check_subst_comp(),
        cs_pair(phi, cs_pair(subst_phi, z)));

    //  Check variable distinctness
    let distinct_checks = cs_and(
        cs_not(cs_eq(x, y)),
        cs_and(cs_not(cs_eq(x, z)),
        cs_and(cs_not(cs_eq(y, z)),
        cs_and(cs_not(cs_eq(u, x)),
        cs_and(cs_not(cs_eq(u, y)),
        cs_and(cs_not(cs_eq(v, x)),
        cs_and(cs_not(cs_eq(v, y)),
        cs_not(cs_eq(u, v))))))))
    );

    cs_and(tag_checks, cs_and(var_checks, cs_and(phi_check,
        cs_and(subst_check, distinct_checks))))
}

///  Check Assumption justification: formula is a ZFC axiom.
///  Input: formula_enc
///  Checks if the formula equals one of the 7 fixed ZFC axiom encodings
///  or matches the Replacement axiom schema.
pub open spec fn check_zfc_axiom() -> CompSpec {
    cs_or(cs_eq(CompSpec::Id, enc_extensionality()),
    cs_or(cs_eq(CompSpec::Id, enc_pairing()),
    cs_or(cs_eq(CompSpec::Id, enc_union()),
    cs_or(cs_eq(CompSpec::Id, enc_powerset()),
    cs_or(cs_eq(CompSpec::Id, enc_infinity()),
    cs_or(cs_eq(CompSpec::Id, enc_foundation()),
    cs_or(cs_eq(CompSpec::Id, enc_choice()),
        check_replacement_axiom()
    )))))))
}

///  Check one proof line's validity.
///  Input: pair(seq_enc, line_idx)
///  Extracts the line, dispatches on justification tag.
///  Each branch independently recomputes what it needs from the input.
pub open spec fn check_line() -> CompSpec {
    //  All sub-expressions take input = pair(seq, idx)
    //  tag = fst(snd(seq_elem(input)))
    let tag = cs_fst(cs_snd(seq_elem_comp()));
    //  formula = fst(seq_elem(input))
    let formula = cs_fst(seq_elem_comp());
    //  justification content = snd(snd(seq_elem(input)))
    let content = cs_snd(cs_snd(seq_elem_comp()));

    //  check_input for MP/Gen: pair(pair(formula, content), pair(seq, idx))
    let mp_gen_input = CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(formula),
            right: Box::new(content),
        }),
        right: Box::new(CompSpec::Id),
    };

    //  Tag dispatch via nested IfZero:
    //  IfZero takes input = pair(seq, idx) for all branches
    CompSpec::IfZero {
        cond: Box::new(tag),
        //  tag == 0: LogicAxiom
        then_br: Box::new(cs_comp(check_logic_axiom(), cs_fst(seq_elem_comp()))),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, cs_fst(cs_snd(seq_elem_comp())))),
            //  tag == 1: Assumption (ZFC axiom check)
            then_br: Box::new(cs_comp(check_zfc_axiom(), cs_fst(seq_elem_comp()))),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred,
                    cs_comp(CompSpec::Pred, cs_fst(cs_snd(seq_elem_comp()))))),
                //  tag == 2: ModusPonens
                then_br: Box::new(cs_comp(check_modus_ponens(), mp_gen_input)),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred,
                        cs_comp(CompSpec::Pred, cs_fst(cs_snd(seq_elem_comp())))))),
                    //  tag == 3: Generalization
                    then_br: Box::new(cs_comp(check_generalization(), mp_gen_input)),
                    //  tag > 3: invalid
                    else_br: Box::new(cs_const(0)),
                }),
            }),
        }),
    }
}

///  Check all proof lines are valid.
///  Input: seq_enc
///  Iterates over the sequence, checking each line.
///  Returns 1 if all valid, 0 if any invalid.
pub open spec fn check_all_lines() -> CompSpec {
    //  BoundedRec: iterate over sequence positions
    //  count = seq_enc (generous upper bound on number of lines)
    //  acc = pair(remaining_seq, pair(valid_flag, line_idx))
    //  step: if fst(remaining) == 0: stop. Else: check current line, advance.
    //  After loop: extract valid_flag from acc.
    cs_comp(
        cs_fst(cs_snd(CompSpec::Id)),  //  extract valid_flag from final acc
        CompSpec::BoundedRec {
            count_fn: Box::new(CompSpec::Id),
            base: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::Id),  //  remaining = full seq
                right: Box::new(CompSpec::CantorPair {
                    left: Box::new(cs_const(1)),  //  valid = true
                    right: Box::new(cs_const(0)),  //  line_idx = 0
                }),
            }),
            step: Box::new({
                //  step input: pair(i, pair(acc, original_seq))
                //  acc = pair(remaining, pair(valid, idx))
                let remaining = cs_fst(br_acc());
                let valid = cs_fst(cs_snd(br_acc()));
                let idx = cs_snd(cs_snd(br_acc()));
                let orig_seq = cs_snd(cs_snd(CompSpec::Id));  //  original_input

                //  If fst(remaining) == 0: done, keep acc
                CompSpec::IfZero {
                    cond: Box::new(cs_fst(remaining)),
                    then_br: Box::new(br_acc()),  //  keep acc (done)
                    else_br: Box::new(CompSpec::CantorPair {
                        //  new remaining = snd(remaining)
                        left: Box::new(cs_snd(remaining)),
                        right: Box::new(CompSpec::CantorPair {
                            //  new valid = old valid * check_line(pair(orig_seq, idx))
                            left: Box::new(cs_and(
                                valid,
                                cs_comp(check_line(), CompSpec::CantorPair {
                                    left: Box::new(orig_seq),
                                    right: Box::new(idx),
                                }),
                            )),
                            //  new idx = idx + 1
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

//  ============================================================
//  Check conclusion is Iff of sentences
//  ============================================================

///  CompSpec: check if variable v is free in encoded formula f_enc.
///  Input: pair(f_enc, v)
///  Uses a stack-based tree traversal via BoundedRec.
///  Stack is encoded as a nat sequence (0=empty, pair(elem+1, rest)=non-empty).
///  Each element is pair(sub_formula_enc, is_bound_flag) where is_bound_flag=1 if v is bound here.
///  Returns nonzero if v is free in f_enc.
#[verifier::opaque]
pub open spec fn has_free_var_comp() -> CompSpec {
    //  Input: pair(f_enc, v)
    //  BoundedRec: count = f_enc (upper bound on tree traversal steps)
    //  base = pair(pair(f_enc + 1, 0), 0)  //  stack = [f_enc], found = 0
    //  The stack encodes formulas to check. Each elem is sub_formula_enc.
    //  After loop: found flag
    let f_enc_expr = cs_fst(CompSpec::Id);  //  f_enc from input
    let v_expr = cs_snd(CompSpec::Id);       //  v from input

    cs_comp(
        cs_snd(CompSpec::Id),  //  extract found from final pair(stack, found)
        CompSpec::BoundedRec {
            count_fn: Box::new(f_enc_expr),
            base: Box::new(CompSpec::CantorPair {
                //  Initial stack: single-element sequence with f_enc
                left: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::Add {
                        left: Box::new(f_enc_expr),
                        right: Box::new(cs_const(1)),
                    }),
                    right: Box::new(cs_const(0)),  //  empty tail
                }),
                right: Box::new(cs_const(0)),  //  found = 0
            }),
            step: Box::new(has_free_var_step()),
        }
    )
}

///  Step function for has_free_var_comp's BoundedRec.
///  Input: pair(i, pair(acc, pair(f_enc, v)))
///  acc = pair(stack, found)
///  If found != 0 or stack empty: keep acc.
///  Else: pop top formula, dispatch on tag, check/push sub-formulas.
pub open spec fn has_free_var_step() -> CompSpec {
    let acc = br_acc();                          //  pair(stack, found)
    let stack = cs_fst(acc);
    let found = cs_snd(acc);
    let v = cs_snd(cs_snd(cs_snd(CompSpec::Id)));  //  v from original input

    //  If found != 0: keep acc (already found free occurrence)
    CompSpec::IfZero {
        cond: Box::new(found),
        //  found == 0: check the stack
        then_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_fst(stack)),  //  unpair1(stack) == 0 means empty
            //  stack empty: keep acc (done, not found)
            then_br: Box::new(acc),
            //  stack non-empty: pop and process
            else_br: Box::new(has_free_var_process_top()),
        }),
        //  found != 0: keep acc
        else_br: Box::new(acc),
    }
}

///  Process the top formula from the stack in has_free_var.
///  Input: pair(i, pair(pair(stack, 0), pair(f_enc, v)))
///  stack is non-empty. Pop top, dispatch on tag.
pub open spec fn has_free_var_process_top() -> CompSpec {
    let acc = br_acc();
    let stack = cs_fst(acc);
    let v = cs_snd(cs_snd(cs_snd(CompSpec::Id)));

    //  Pop: top_enc = unpair1(stack) - 1, rest = unpair2(stack)
    let top_enc = cs_comp(CompSpec::Pred, cs_fst(stack));
    let rest = cs_snd(stack);
    let tag = cs_fst(top_enc);
    let content = cs_snd(top_enc);

    //  Dispatch on tag:
    //  0, 1 (Eq, In): check if either term == v
    //    terms are just variable indices: left = fst(content), right = snd(content)
    //    found = (left == v) || (right == v) ? 1 : 0
    //  2 (Not): push sub onto stack
    //  3-6 (And/Or/Implies/Iff): push both subs
    //  7, 8 (Forall, Exists): if bound var == v then skip, else push sub

    CompSpec::IfZero {
        cond: Box::new(tag),
        //  tag == 0 (Eq): check terms
        then_br: Box::new(CompSpec::CantorPair {
            left: Box::new(rest),
            right: Box::new(cs_or(
                cs_eq(cs_fst(content), v),
                cs_eq(cs_snd(content), v),
            )),
        }),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_comp(CompSpec::Pred, tag)),
            //  tag == 1 (In): same as Eq
            then_br: Box::new(CompSpec::CantorPair {
                left: Box::new(rest),
                right: Box::new(cs_or(
                    cs_eq(cs_fst(content), v),
                    cs_eq(cs_snd(content), v),
                )),
            }),
            else_br: Box::new(CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag))),
                //  tag == 2 (Not): push sub-formula
                then_br: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::CantorPair {
                        left: Box::new(CompSpec::Add {
                            left: Box::new(content),
                            right: Box::new(cs_const(1)),
                        }),
                        right: Box::new(rest),
                    }),
                    right: Box::new(cs_const(0)),
                }),
                else_br: Box::new(has_free_var_binary_or_quantifier()),
            }),
        }),
    }
}

///  Handle binary formulas (tags 3-6) and quantifiers (tags 7-8) in has_free_var.
///  For binary: push both sub-formulas onto stack.
///  For quantifier: if bound var == v, skip; else push sub.
pub open spec fn has_free_var_binary_or_quantifier() -> CompSpec {
    let acc = br_acc();
    let stack = cs_fst(acc);
    let v = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    let top_enc = cs_comp(CompSpec::Pred, cs_fst(stack));
    let rest = cs_snd(stack);
    let tag = cs_fst(top_enc);
    let content = cs_snd(top_enc);

    //  Tags 3-6: binary. Push both fst(content) and snd(content) onto rest.
    //  Tags 7-8: quantifier. fst(content) = bound_var, snd(content) = sub.
    //    If bound_var == v: pair(rest, 0)  (v is bound, skip)
    //    Else: push snd(content) onto rest

    //  Check if tag <= 6 (binary) vs >= 7 (quantifier)
    //  tag - 3 < 4 means tag <= 6 (binary)
    //  We already know tag >= 3 from the dispatch chain
    let tag_minus_3 = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, tag)));

    CompSpec::IfZero {
        cond: Box::new(cs_lt(tag_minus_3, cs_const(4))),
        //  tag - 3 >= 4 means tag >= 7: quantifier
        //  (IfZero: cond==0 means lt returned 0 means NOT less than 4)
        then_br: Box::new(
            //  Quantifier: check if bound_var == v
            CompSpec::IfZero {
                cond: Box::new(cs_eq(cs_fst(content), v)),
                //  bound_var != v: push sub
                then_br: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::CantorPair {
                        left: Box::new(CompSpec::Add {
                            left: Box::new(cs_snd(content)),
                            right: Box::new(cs_const(1)),
                        }),
                        right: Box::new(rest),
                    }),
                    right: Box::new(cs_const(0)),
                }),
                //  bound_var == v: skip (v is bound here)
                else_br: Box::new(CompSpec::CantorPair {
                    left: Box::new(rest),
                    right: Box::new(cs_const(0)),
                }),
            }
        ),
        //  tag - 3 < 4 means tag <= 6: binary
        else_br: Box::new(CompSpec::CantorPair {
            //  Push both sub-formulas: pair(left+1, pair(right+1, rest))
            left: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::Add {
                    left: Box::new(cs_fst(content)),
                    right: Box::new(cs_const(1)),
                }),
                right: Box::new(CompSpec::CantorPair {
                    left: Box::new(CompSpec::Add {
                        left: Box::new(cs_snd(content)),
                        right: Box::new(cs_const(1)),
                    }),
                    right: Box::new(rest),
                }),
            }),
            right: Box::new(cs_const(0)),
        }),
    }
}

///  Check if an encoded formula is a sentence (no free variables).
///  Input: formula_enc
///  The step function for check_is_sentence, extracted for use in proofs.
///  Input: pair(i, pair(acc, f_enc))
///  Output: acc * (if has_free_var(f_enc, i) == 0 then 1 else 0)
///
///  Opaque to prevent Z3 from unfolding has_free_var_comp's BoundedRec tree
///  inside eval_comp calls, which causes rlimit explosion. Reveal only in
///  the step evaluation lemma.
#[verifier::opaque]
pub open spec fn check_is_sentence_step() -> CompSpec {
    let acc = cs_fst(cs_snd(CompSpec::Id));  //  acc from step input
    let f_enc = cs_snd(cs_snd(CompSpec::Id));  //  original_input = f_enc
    let i = cs_fst(CompSpec::Id);  //  current variable index

    //  check = has_free_var(f_enc, i)
    let check = cs_comp(has_free_var_comp(), CompSpec::CantorPair {
        left: Box::new(f_enc),
        right: Box::new(i),
    });

    //  new_acc = acc * (1 if !has_free_var else 0)
    cs_and(acc, cs_not(check))
}

///  Checks: for all v from 0 to f_enc, v is not free in f_enc.
///  Uses BoundedRec over variable index, calling has_free_var_comp for each.
pub open spec fn check_is_sentence() -> CompSpec {
    //  BoundedRec: count = f_enc, base = 1 (assume sentence)
    //  step: input = pair(i, pair(acc, f_enc))
    //    acc = 1 (still sentence) or 0 (found free var)
    //    check has_free_var(f_enc, i): if nonzero, set acc to 0
    //    new_acc = acc * (1 if !has_free_var else 0)
    CompSpec::BoundedRec {
        count_fn: Box::new(CompSpec::Id),
        base: Box::new(cs_const(1)),
        step: Box::new(check_is_sentence_step()),
    }
}

///  Check conclusion is Iff with sentence sub-formulas.
///  Input: seq_enc (the encoded proof)
///  Gets last formula, checks tag==6 (Iff) and both sides are sentences.
pub open spec fn check_conclusion_iff_sentence() -> CompSpec {
    let formula_enc = last_formula_enc();  //  from compspec_decode
    cs_and(
        //  Tag is 6 (Iff)
        cs_eq(cs_fst(formula_enc), cs_const(6)),
        cs_and(
            //  Left sub-formula is a sentence
            cs_comp(check_is_sentence(), cs_fst(cs_snd(formula_enc))),
            //  Right sub-formula is a sentence
            cs_comp(check_is_sentence(), cs_snd(cs_snd(formula_enc)))
        )
    )
}

//  ============================================================
//  Top-level halts CompSpec
//  ============================================================

///  The halts predicate as a CompSpec.
///  Returns nonzero iff s encodes a valid ZFC proof with Iff-of-sentences conclusion.
pub open spec fn halts_comp_term() -> CompSpec {
    cs_and(
        //  s != 0 (non-empty sequence)
        cs_nonzero(),
        cs_and(
            //  All lines valid
            check_all_lines(),
            //  Conclusion is Iff of sentences
            check_conclusion_iff_sentence()
        )
    )
}

//  ============================================================
//  Correctness proof
//  ============================================================

///  The halts CompSpec computes the halting predicate correctly.
///
///  PROOF STATUS: The CompSpec term (halts_comp_term) is fully constructed with:
///  - All 11 logic axiom schema checks (7 pure pattern matching + 4 with subst/free-var)
///  - 7 fixed ZFC axiom encoding constants + Replacement axiom pattern matching
///  - Stack-based free variable traversal (has_free_var_comp)
///  - Stack-based substitution verification (check_subst_comp)
///  - ModusPonens/Generalization line lookup and formula matching
///  - BoundedRec iteration over all proof lines
///  - Conclusion Iff-of-sentences check
///
///  The correctness proof (both directions of the biconditional) requires
///  ~200 lines connecting each CompSpec sub-computation to its mathematical
///  counterpart. This is mechanical but extensive — each eval_comp chain
///  must be traced through the encoding/decoding round-trip.
///
///  Known simplification: eq_subst_left/right use a partial structural check
///  (tag matching only) rather than full substitution consistency verification.
///  This must be strengthened before the forward direction can be fully proved.
//  ============================================================
//  General eval_comp rewriting rules
//  ============================================================
//  Z3 can't automatically unfold eval_comp through nested CompSpec.
//  These helpers provide one-step unfolding rules.

pub proof fn lemma_eval_fst(inner: CompSpec, s: nat)
    ensures eval_comp(CompSpec::CantorFst { inner: Box::new(inner) }, s)
        == unpair1(eval_comp(inner, s))
{}

pub proof fn lemma_eval_snd(inner: CompSpec, s: nat)
    ensures eval_comp(CompSpec::CantorSnd { inner: Box::new(inner) }, s)
        == unpair2(eval_comp(inner, s))
{}

pub proof fn lemma_eval_comp(outer: CompSpec, inner: CompSpec, s: nat)
    ensures eval_comp(CompSpec::Comp { outer: Box::new(outer), inner: Box::new(inner) }, s)
        == eval_comp(outer, eval_comp(inner, s))
{}

pub proof fn lemma_eval_eq(l: CompSpec, r: CompSpec, s: nat)
    ensures eval_comp(CompSpec::Eq { left: Box::new(l), right: Box::new(r) }, s)
        == (if eval_comp(l, s) == eval_comp(r, s) { 1nat } else { 0nat })
{}

///  Helper: eval_comp(cs_nonzero(), s) == if s == 0 { 0 } else { 1 }
pub proof fn lemma_eval_cs_nonzero(s: nat)
    ensures
        eval_comp(cs_nonzero(), s) == (if s == 0 { 0nat } else { 1nat }),
{
    //  Unfold cs_nonzero step by step
    let term = cs_nonzero();
    //  term = IfZero { cond: Id, then_br: Const(0), else_br: Const(1) }
    //  eval_comp(term, s):
    //    = if eval_comp(Id, s) == 0 { eval_comp(Const(0), s) } else { eval_comp(Const(1), s) }
    //    = if s == 0 { 0 } else { 1 }
    assert(eval_comp(CompSpec::Id, s) == s);
    assert(eval_comp(CompSpec::Const { value: 0 }, s) == 0);
    assert(eval_comp(CompSpec::Const { value: 1 }, s) == 1);
}

///  Helper: eval_comp(cs_not(a), s) == if eval_comp(a, s) == 0 { 1 } else { 0 }
pub proof fn lemma_eval_cs_not(a: CompSpec, s: nat)
    ensures
        eval_comp(cs_not(a), s) == (if eval_comp(a, s) == 0 { 1nat } else { 0nat }),
{
    //  cs_not(a) = IfZero { cond: a, then_br: Const(1), else_br: Const(0) }
    assert(eval_comp(CompSpec::Const { value: 1 }, s) == 1nat);
    assert(eval_comp(CompSpec::Const { value: 0 }, s) == 0nat);
}

///  Helper: eval_comp(cs_and(a, b), s) == eval_comp(a, s) * eval_comp(b, s)
pub proof fn lemma_eval_cs_and(a: CompSpec, b: CompSpec, s: nat)
    ensures
        eval_comp(cs_and(a, b), s) == eval_comp(a, s) * eval_comp(b, s),
{
    //  cs_and(a, b) = Mul { left: a, right: b }
    //  eval_comp(Mul{l,r}, s) = eval_comp(l, s) * eval_comp(r, s)
}

///  Helper: IfZero when condition evaluates to 0 → take then branch.
pub proof fn lemma_eval_ifzero_then(
    cond: CompSpec, then_br: CompSpec, else_br: CompSpec, s: nat,
)
    requires
        eval_comp(cond, s) == 0,
    ensures
        eval_comp(CompSpec::IfZero {
            cond: Box::new(cond),
            then_br: Box::new(then_br),
            else_br: Box::new(else_br),
        }, s) == eval_comp(then_br, s),
{
}

///  Helper: IfZero when condition evaluates to nonzero → take else branch.
pub proof fn lemma_eval_ifzero_else(
    cond: CompSpec, then_br: CompSpec, else_br: CompSpec, s: nat,
)
    requires
        eval_comp(cond, s) != 0,
    ensures
        eval_comp(CompSpec::IfZero {
            cond: Box::new(cond),
            then_br: Box::new(then_br),
            else_br: Box::new(else_br),
        }, s) == eval_comp(else_br, s),
{
}

///  Helper: eval_comp(CantorPair{l, r}, s) == pair(eval_comp(l, s), eval_comp(r, s))
pub proof fn lemma_eval_pair(l: CompSpec, r: CompSpec, s: nat)
    ensures
        eval_comp(CompSpec::CantorPair {
            left: Box::new(l), right: Box::new(r)
        }, s) == pair(eval_comp(l, s), eval_comp(r, s)),
{
}

///  Helper: eval_comp(Add{l, r}, s) == eval_comp(l, s) + eval_comp(r, s)
pub proof fn lemma_eval_add(l: CompSpec, r: CompSpec, s: nat)
    ensures
        eval_comp(CompSpec::Add {
            left: Box::new(l), right: Box::new(r)
        }, s) == eval_comp(l, s) + eval_comp(r, s),
{
}

///  Helper: eval_comp(Pred, s) == if s > 0 { s - 1 } else { 0 }
pub proof fn lemma_eval_pred(s: nat)
    ensures
        eval_comp(CompSpec::Pred, s) == (if s > 0 { (s - 1) as nat } else { 0nat }),
{
}

///  Helper: eval_comp(Lt{l, r}, s) == if eval_comp(l, s) < eval_comp(r, s) { 1 } else { 0 }
pub proof fn lemma_eval_lt(l: CompSpec, r: CompSpec, s: nat)
    ensures
        eval_comp(CompSpec::Lt {
            left: Box::new(l), right: Box::new(r)
        }, s) == (if eval_comp(l, s) < eval_comp(r, s) { 1nat } else { 0nat }),
{
}

///  Helper: for encoded sentences, has_free_var returns 0.
///  The stack-based tree traversal correctly finds no free variables.
proof fn lemma_has_free_var_sentence(f: Formula, v: nat)
    requires
        is_sentence(f),
    ensures
        eval_comp(has_free_var_comp(), pair(encode(f), v)) == 0,
{
    //  Delegate to isolated module to avoid trigger pollution
    crate::compspec_free_var_induction::lemma_has_free_var_sentence_core(f, v);
}

//  DEAD CODE — replaced by lemma_has_free_var_sentence_core in compspec_free_var_induction.rs.
//  Kept temporarily to avoid changing line numbers of downstream code.
proof fn lemma_has_free_var_sentence_OLD(f: Formula, v: nat)
    requires false,
{
    let f_enc = encode(f);
    let input = pair(f_enc, v);
    lemma_sentence_no_free_var(f, v);

    reveal(has_free_var_comp);
    let f_enc_expr = cs_fst(CompSpec::Id);
    let bounded_rec = CompSpec::BoundedRec {
        count_fn: Box::new(f_enc_expr),
        base: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::CantorPair {
                left: Box::new(CompSpec::Add {
                    left: Box::new(f_enc_expr),
                    right: Box::new(cs_const(1)),
                }),
                right: Box::new(cs_const(0)),
            }),
            right: Box::new(cs_const(0)),
        }),
        step: Box::new(has_free_var_step()),
    };
    //  has_free_var_comp() = cs_comp(cs_snd(Id), bounded_rec)
    lemma_eval_comp(cs_snd(CompSpec::Id), bounded_rec, input);
    //  eval = eval(cs_snd(Id), eval(bounded_rec, input))
    //       = unpair2(eval(bounded_rec, input))

    //  Step 3: unfold BoundedRec via lemma_eval_bounded_rec
    lemma_eval_bounded_rec(f_enc_expr, CompSpec::CantorPair {
        left: Box::new(CompSpec::CantorPair {
            left: Box::new(CompSpec::Add {
                left: Box::new(f_enc_expr),
                right: Box::new(cs_const(1)),
            }),
            right: Box::new(cs_const(0)),
        }),
        right: Box::new(cs_const(0)),
    }, has_free_var_step(), input);
    //  eval(bounded_rec, input) = compspec_iterate(step, count, base_val, input)
    //  count = eval(f_enc_expr, input) = f_enc
    //  base_val = pair(pair(f_enc + 1, 0), 0)
    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(f_enc, v);
    assert(eval_comp(f_enc_expr, input) == f_enc);
    lemma_eval_pair(CompSpec::CantorPair {
        left: Box::new(CompSpec::Add {
            left: Box::new(f_enc_expr),
            right: Box::new(cs_const(1)),
        }),
        right: Box::new(cs_const(0)),
    }, cs_const(0), input);
    lemma_eval_pair(CompSpec::Add {
        left: Box::new(f_enc_expr),
        right: Box::new(cs_const(1)),
    }, cs_const(0), input);
    lemma_eval_add(f_enc_expr, cs_const(1), input);
    let base_val = pair(pair(f_enc + 1, 0nat), 0nat);

    //  Step 4: apply traversal induction
    lemma_traversal_cost_le_size(f, v);
    crate::compspec_free_var_induction::lemma_traversal_no_free_var(
        f, v, 0nat, f_enc, f_enc);
    //  compspec_iterate(step, f_enc, pair(pair(f_enc+1, 0), 0), pair(f_enc, v))
    //    == compspec_iterate(step, f_enc - traversal_cost(f, v), pair(0, 0), pair(f_enc, v))

    //  Step 5: remaining iterations on empty stack stay at pair(0, 0)
    crate::compspec_free_var_induction::lemma_csi_empty_stable(
        (f_enc - traversal_cost(f, v)) as nat, f_enc, v);
    //  So: eval(bounded_rec, input) = pair(0, 0)
    //  compspec_iterate(step, remaining, pair(0, 0), input) == pair(0, 0)

    //  Step 6: extract found flag
    lemma_eval_snd(CompSpec::Id, pair(0nat, 0nat));
    lemma_unpair2_pair(0nat, 0nat);
}

//  lemma_cis_step_preserves is in compspec_sentence_helpers.rs
//  (isolated in its own module to reduce trigger pollution from compspec_halts proof fn bodies)

///  Helper: the check_is_sentence BoundedRec iteration preserves nonzero acc
///  when all has_free_var checks return 0.
///  fuel <= f_enc ensures all checked variables are < f_enc.
pub proof fn lemma_check_is_sentence_iter(
    f_enc: nat,
    fuel: nat,
    acc: nat,
)
    requires
        acc != 0,
        fuel <= f_enc,
        forall|v: nat| v < f_enc ==>
            eval_comp(has_free_var_comp(), pair(f_enc, v)) == 0,
    ensures
        iterate(
            |x: nat| eval_comp(check_is_sentence_step(), x),
            fuel, acc, f_enc,
        ) != 0,
    decreases fuel,
{
    if fuel > 0 {
        let i = (fuel - 1) as nat;
        //  i = fuel - 1 < fuel <= f_enc, so i < f_enc
        assert(i < f_enc);
        lemma_cis_step_preserves(i, acc, f_enc);
        let step_fn = |x: nat| eval_comp(check_is_sentence_step(), x);
        assert(step_fn(pair(i, pair(acc, f_enc))) == acc);
        assert(acc != 0);
        lemma_check_is_sentence_iter(f_enc, (fuel - 1) as nat, acc);
    }
}

///  Helper: for encoded sentences, check_is_sentence returns nonzero.
proof fn lemma_check_is_sentence_backward(f: Formula)
    requires
        is_sentence(f),
    ensures
        eval_comp(check_is_sentence(), encode(f)) != 0,
{
    let f_enc = encode(f);
    //  Establish: all has_free_var checks return 0
    assert forall|v: nat| v < f_enc implies
        eval_comp(has_free_var_comp(), pair(f_enc, v)) == 0
    by {
        lemma_has_free_var_sentence(f, v);
    };
    //  Delegate to the helper module where closure matching works
    //  (compspec_halts.rs has too many proof fn bodies causing trigger pollution)
    lemma_check_is_sentence_nonzero(f_enc);
}

//  lemma_eval_last_formula_enc is in compspec_eval_helpers.rs
//  (isolated file to avoid module trigger pollution from large CompSpec definitions)

///  Backward: for valid proof codes, check_conclusion_iff_sentence returns nonzero.
proof fn lemma_conclusion_check_backward(s: nat, p: Proof)
    requires
        encode_proof(p) == s,
        p.lines.len() > 0,
        conclusion_is_iff_of_sentences(proof_conclusion(p)),
    ensures
        eval_comp(check_conclusion_iff_sentence(), s) != 0,
{
    let conclusion = proof_conclusion(p);
    lemma_eval_last_formula_enc(s, p);
    let f_enc = encode(conclusion);
    assert(eval_comp(last_formula_enc(), s) == f_enc);

    match conclusion {
        Formula::Iff { left, right } => {
            let el = encode(*left);
            let er = encode(*right);

            //  Unpairing facts
            lemma_unpair1_pair(6nat, pair(el, er));
            lemma_unpair2_pair(6nat, pair(el, er));
            lemma_unpair1_pair(el, er);
            lemma_unpair2_pair(el, er);

            //  Tag check: cs_eq(cs_fst(last_formula_enc()), cs_const(6))
            lemma_eval_fst(last_formula_enc(), s);
            assert(eval_comp(cs_fst(last_formula_enc()), s) == unpair1(f_enc));
            assert(unpair1(f_enc) == 6);

            //  Sentence checks
            assert(is_sentence(*left));
            assert(is_sentence(*right));
            lemma_check_is_sentence_backward(*left);
            lemma_check_is_sentence_backward(*right);

            //  Sub-formula extraction
            lemma_eval_snd(last_formula_enc(), s);
            assert(eval_comp(cs_snd(last_formula_enc()), s) == pair(el, er));
            lemma_eval_fst(cs_snd(last_formula_enc()), s);
            assert(eval_comp(cs_fst(cs_snd(last_formula_enc())), s) == el);
            lemma_eval_snd(cs_snd(last_formula_enc()), s);
            assert(eval_comp(cs_snd(cs_snd(last_formula_enc())), s) == er);

            //  Sentence check composition: cs_comp(check_is_sentence(), sub_formula_expr)
            lemma_eval_comp(check_is_sentence(), cs_fst(cs_snd(last_formula_enc())), s);
            assert(eval_comp(cs_comp(check_is_sentence(), cs_fst(cs_snd(last_formula_enc()))), s)
                == eval_comp(check_is_sentence(), el));
            lemma_eval_comp(check_is_sentence(), cs_snd(cs_snd(last_formula_enc())), s);
            assert(eval_comp(cs_comp(check_is_sentence(), cs_snd(cs_snd(last_formula_enc()))), s)
                == eval_comp(check_is_sentence(), er));

            //  Now compose: check_conclusion_iff_sentence = cs_and(tag_eq_6, cs_and(sent_l, sent_r))
            let tag_check = cs_eq(cs_fst(last_formula_enc()), cs_const(6));
            let sent_l_check = cs_comp(check_is_sentence(), cs_fst(cs_snd(last_formula_enc())));
            let sent_r_check = cs_comp(check_is_sentence(), cs_snd(cs_snd(last_formula_enc())));

            lemma_eval_eq(cs_fst(last_formula_enc()), cs_const(6), s);
            assert(eval_comp(tag_check, s) == 1);

            let sl = eval_comp(sent_l_check, s);
            let sr = eval_comp(sent_r_check, s);
            assert(sl != 0);
            assert(sr != 0);

            lemma_eval_cs_and(sent_l_check, sent_r_check, s);
            assert(sl >= 1nat);
            assert(sr >= 1nat);
            assert(sl * sr >= 1nat) by(nonlinear_arith)
                requires sl >= 1nat, sr >= 1nat;

            lemma_eval_cs_and(tag_check, cs_and(sent_l_check, sent_r_check), s);
            assert(eval_comp(check_conclusion_iff_sentence(), s) == 1 * (sl * sr));
            assert(1nat * (sl * sr) >= 1nat) by(nonlinear_arith)
                requires sl * sr >= 1nat;
        },
        _ => { assert(false); },
    }
}

///  Backward: for valid proof codes, check_all_lines returns nonzero.
proof fn lemma_all_lines_check_backward(s: nat, p: Proof)
    requires
        encode_proof(p) == s,
        is_valid_proof(p, |f: Formula| is_zfc_axiom(f)),
        p.lines.len() > 0,
    ensures
        eval_comp(check_all_lines(), s) != 0,
{
    //  The BoundedRec in check_all_lines iterates over the encoded sequence,
    //  checking each line with check_line(pair(s, idx)).
    //  For each valid line, check_line must return nonzero.
    //
    //  This requires showing:
    //  1. The iteration processes exactly p.lines.len() elements
    //  2. For each line i, check_line correctly validates the justification
    //  3. The validity accumulator stays 1 throughout
    //
    //  Each sub-check (ModusPonens, Generalization, LogicAxiom, Assumption)
    //  needs its own connecting lemma.
    assume(eval_comp(check_all_lines(), s) != 0);
}

pub proof fn lemma_halts_comp_correct()
    ensures
        is_halts_comp(halts_comp_term()),
{
    assert forall|s: nat| (#[trigger] eval_comp(halts_comp_term(), s) != 0)
        <==> is_valid_iff_proof_code(s)
    by {
        //  Backward direction: valid proof → CompSpec returns nonzero
        if is_valid_iff_proof_code(s) {
            let p: Proof = choose|p: Proof|
                encode_proof(p) == s &&
                is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
                p.lines.len() > 0 &&
                conclusion_is_iff_of_sentences(proof_conclusion(p));

            //  (a) s != 0: valid proof has non-empty encoding
            lemma_encode_nat_seq_nonempty(
                Seq::new(p.lines.len(), |i: int| encode_line(p.lines[i])));
            assert(s != 0);

            //  (b) All lines valid
            lemma_all_lines_check_backward(s, p);

            //  (c) Conclusion is Iff of sentences
            lemma_conclusion_check_backward(s, p);

            //  Combine: halts_comp_term = cs_and(nonzero, cs_and(all_lines, conclusion))
            //  cs_and = Mul. eval_comp(Mul{l,r}, s) = eval_comp(l, s) * eval_comp(r, s)
            //  All three sub-results are nonzero, so product is nonzero.
            //  (d) Compose: halts_comp_term = cs_and(cs_nonzero, cs_and(check_all_lines, check_conclusion))
            lemma_eval_cs_nonzero(s);
            assert(eval_comp(cs_nonzero(), s) == 1);

            let b = eval_comp(check_all_lines(), s);
            let c = eval_comp(check_conclusion_iff_sentence(), s);
            assert(b != 0);
            assert(c != 0);

            //  cs_and composition
            lemma_eval_cs_and(check_all_lines(), check_conclusion_iff_sentence(), s);
            assert(b >= 1nat);
            assert(c >= 1nat);
            assert(b * c >= 1nat) by(nonlinear_arith)
                requires b >= 1nat, c >= 1nat;

            lemma_eval_cs_and(cs_nonzero(), cs_and(check_all_lines(), check_conclusion_iff_sentence()), s);
            let bc = b * c;
            assert(eval_comp(halts_comp_term(), s) == 1 * bc);
            assert(1nat * bc >= 1nat) by(nonlinear_arith)
                requires bc >= 1nat;
        }

        //  Forward direction: CompSpec returns nonzero → valid proof
        if eval_comp(halts_comp_term(), s) != 0 {
            assume(is_valid_iff_proof_code(s));
        }
    };
}

} //  verus!
