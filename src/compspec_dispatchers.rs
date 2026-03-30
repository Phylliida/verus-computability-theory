use vstd::prelude::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_axiom_correct::*;
use crate::compspec_axiom_eval::*;
use crate::compspec_logic_axiom_helpers::*;
use crate::proof_system::*;
use crate::zfc::*;
use crate::pairing::*;

verus! {

///  Helper: if any sub-check returns nonzero, check_logic_axiom returns nonzero.
///  This scopes ALL the cs_or unfolding inside one assert-by.
proof fn logic_axiom_chain(x: nat, check_idx: nat)
    requires
        check_idx <= 10,
        //  The specific sub-check at position check_idx returns nonzero
        (check_idx == 0 ==> eval_comp(check_axiom_identity(), x) != 0) &&
        (check_idx == 1 ==> eval_comp(check_axiom_eq_refl(), x) != 0) &&
        (check_idx == 2 ==> eval_comp(check_axiom_iff_elim_left(), x) != 0) &&
        (check_idx == 3 ==> eval_comp(check_axiom_iff_elim_right(), x) != 0) &&
        (check_idx == 4 ==> eval_comp(check_axiom_iff_intro(), x) != 0) &&
        (check_idx == 5 ==> eval_comp(check_axiom_hyp_syllogism(), x) != 0) &&
        (check_idx == 6 ==> eval_comp(check_axiom_quantifier_dist(), x) != 0) &&
        (check_idx == 7 ==> eval_comp(check_axiom_universal_inst(), x) != 0) &&
        (check_idx == 8 ==> eval_comp(check_axiom_vacuous_quant(), x) != 0) &&
        (check_idx == 9 ==> eval_comp(check_axiom_eq_subst_left(), x) != 0) &&
        (check_idx == 10 ==> eval_comp(check_axiom_eq_subst_right(), x) != 0),
    ensures eval_comp(check_logic_axiom(), x) != 0,
{
    let a0 = check_axiom_identity();
    let a1 = check_axiom_eq_refl();
    let a2 = check_axiom_iff_elim_left();
    let a3 = check_axiom_iff_elim_right();
    let a4 = check_axiom_iff_intro();
    let a5 = check_axiom_hyp_syllogism();
    let a6 = check_axiom_quantifier_dist();
    let a7 = check_axiom_universal_inst();
    let a8 = check_axiom_vacuous_quant();
    let a9 = check_axiom_eq_subst_left();
    let a10 = check_axiom_eq_subst_right();

    lemma_eval_cs_or(a10, cs_const(0), x);
    lemma_eval_cs_or(a9, cs_or(a10, cs_const(0)), x);
    lemma_eval_cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0))), x);
    lemma_eval_cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0)))), x);
    lemma_eval_cs_or(a6, cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0))))), x);
    lemma_eval_cs_or(a5, cs_or(a6, cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0)))))), x);
    lemma_eval_cs_or(a4, cs_or(a5, cs_or(a6, cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0))))))), x);
    lemma_eval_cs_or(a3, cs_or(a4, cs_or(a5, cs_or(a6, cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0)))))))), x);
    lemma_eval_cs_or(a2, cs_or(a3, cs_or(a4, cs_or(a5, cs_or(a6, cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0))))))))), x);
    lemma_eval_cs_or(a1, cs_or(a2, cs_or(a3, cs_or(a4, cs_or(a5, cs_or(a6, cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0)))))))))), x);
    lemma_eval_cs_or(a0, cs_or(a1, cs_or(a2, cs_or(a3, cs_or(a4, cs_or(a5, cs_or(a6, cs_or(a7, cs_or(a8, cs_or(a9, cs_or(a10, cs_const(0))))))))))), x);
}

///  check_logic_axiom returns nonzero for any valid logic axiom.
#[verifier::rlimit(100)]
pub proof fn lemma_check_logic_axiom_correct(f: Formula)
    requires is_logic_axiom(f),
    ensures eval_comp(check_logic_axiom(), encode(f)) != 0,
{
    let x = encode(f);

    //  Handle eq_subst via structural match first (always exhaustive)
    match f {
        Formula::Implies { left, right } => {
            match (*left, *right) {
                (Formula::Eq { left: xt, right: yt }, Formula::Implies { left: s1, right: s2 }) => {
                    eq_subst_left_inner(f, xt, yt, *s1, *s2);
                    logic_axiom_chain(x, 9);
                    return;
                },
                (_, _) => {},
            }
        },
        _ => {},
    }

    //  Dispatch via Formula match — always exhaustive
    //  Within each arm, use choose to extract witnesses from is_logic_axiom
    match f {
        Formula::Eq { left, right } => {
            //  Test: can Z3 derive !is_axiom_identity(f) from f == Eq{...}?
            assert(!is_axiom_identity(f));
            let t: Term = choose|t: Term| f == mk_eq(t, t);
            eq_refl_compose(f, t);
            logic_axiom_chain(x, 1);
        },
        Formula::Implies { left, right } => {
            match *left {
                Formula::Iff { left: pl, right: pr } => {
                    if is_axiom_iff_elim_left(f) {
                        lemma_check_axiom_iff_elim_left_correct(f);
                        logic_axiom_chain(x, 2);
                    } else if is_axiom_iff_elim_right(f) {
                        lemma_check_axiom_iff_elim_right_correct(f);
                        logic_axiom_chain(x, 3);
                    } else {
                        //  Implies(Iff(pl,pr), right) where right is not Implies(pl,pr) or Implies(pr,pl)
                        //  Must be identity: Implies(phi, phi) where phi = Iff(pl, pr)
                        let phi: Formula = choose|phi: Formula| f == mk_implies(phi, phi);
                        identity_compose(f, phi);
                        logic_axiom_chain(x, 0);
                    }
                },
                Formula::Implies { left: pl, right: pr } => {
                    if is_axiom_identity(f) {
                        lemma_check_axiom_identity_correct(f);
                        logic_axiom_chain(x, 0);
                    } else if is_axiom_iff_intro(f) {
                        lemma_check_axiom_iff_intro_correct(f);
                        logic_axiom_chain(x, 4);
                    } else if is_axiom_hyp_syllogism(f) {
                        lemma_check_axiom_hyp_syllogism_correct(f);
                        logic_axiom_chain(x, 5);
                    } else {
                        //  Must be identity with Implies sub
                        let phi: Formula = choose|phi: Formula| f == mk_implies(phi, phi);
                        identity_compose(f, phi);
                        logic_axiom_chain(x, 0);
                    }
                },
                Formula::Forall { var: v, sub } => {
                    if is_axiom_quantifier_dist(f) {
                        lemma_check_axiom_quantifier_dist_correct(f);
                        logic_axiom_chain(x, 6);
                    } else if is_axiom_universal_inst(f) {
                        lemma_check_axiom_universal_inst_correct(f);
                        logic_axiom_chain(x, 7);
                    } else {
                        //  Must be identity with Forall sub
                        let phi: Formula = choose|phi: Formula| f == mk_implies(phi, phi);
                        identity_compose(f, phi);
                        logic_axiom_chain(x, 0);
                    }
                },
                Formula::Eq { left: el, right: er } => {
                    //  Already handled by structural match above (eq_subst)
                    //  Shouldn't reach here due to return. But just in case:
                    match *right {
                        Formula::Implies { left: s1, right: s2 } => {
                            eq_subst_left_inner(f, el, er, *s1, *s2);
                            logic_axiom_chain(x, 9);
                        },
                        _ => {
                            let phi: Formula = choose|phi: Formula| f == mk_implies(phi, phi);
                            identity_compose(f, phi);
                            logic_axiom_chain(x, 0);
                        },
                    }
                },
                _ => {
                    //  Implies(X, right) where X is In/Not/And/Or/Exists
                    //  Could be identity or vacuous_quant
                    if is_axiom_vacuous_quant(f) {
                        lemma_check_axiom_vacuous_quant_correct(f);
                        logic_axiom_chain(x, 8);
                    } else {
                        let phi: Formula = choose|phi: Formula| f == mk_implies(phi, phi);
                        identity_compose(f, phi);
                        logic_axiom_chain(x, 0);
                    }
                },
            }
        },
        _ => {
            //  Non-Eq, non-Implies top-level: no logic axiom has this structure
            //  is_logic_axiom(f) → false (all axioms are Eq or Implies)
            //  Contradiction with requires
        },
    }
}

///  check_zfc_axiom returns nonzero for fixed ZFC axioms.
pub proof fn lemma_check_zfc_fixed_axiom_correct(f: Formula)
    requires
        f == extensionality_axiom() || f == pairing_axiom() || f == union_axiom()
        || f == powerset_axiom() || f == infinity_axiom() || f == foundation_axiom()
        || f == choice_axiom(),
    ensures eval_comp(check_zfc_axiom(), encode(f)) != 0,
{
    let x = encode(f);
    let e0 = cs_eq(CompSpec::Id, enc_extensionality());
    let e1 = cs_eq(CompSpec::Id, enc_pairing());
    let e2 = cs_eq(CompSpec::Id, enc_union());
    let e3 = cs_eq(CompSpec::Id, enc_powerset());
    let e4 = cs_eq(CompSpec::Id, enc_infinity());
    let e5 = cs_eq(CompSpec::Id, enc_foundation());
    let e6 = cs_eq(CompSpec::Id, enc_choice());
    let e7 = check_replacement_axiom();

    lemma_eval_cs_or(e6, e7, x);
    lemma_eval_cs_or(e5, cs_or(e6, e7), x);
    lemma_eval_cs_or(e4, cs_or(e5, cs_or(e6, e7)), x);
    lemma_eval_cs_or(e3, cs_or(e4, cs_or(e5, cs_or(e6, e7))), x);
    lemma_eval_cs_or(e2, cs_or(e3, cs_or(e4, cs_or(e5, cs_or(e6, e7)))), x);
    lemma_eval_cs_or(e1, cs_or(e2, cs_or(e3, cs_or(e4, cs_or(e5, cs_or(e6, e7))))), x);
    lemma_eval_cs_or(e0, cs_or(e1, cs_or(e2, cs_or(e3, cs_or(e4, cs_or(e5, cs_or(e6, e7)))))), x);

    if f == extensionality_axiom() {
        lemma_enc_extensionality_eval(x);
        lemma_eval_eq(CompSpec::Id, enc_extensionality(), x);
    } else if f == pairing_axiom() {
        lemma_enc_pairing_eval(x);
        lemma_eval_eq(CompSpec::Id, enc_pairing(), x);
    } else if f == union_axiom() {
        lemma_enc_union_eval(x);
        lemma_eval_eq(CompSpec::Id, enc_union(), x);
    } else if f == powerset_axiom() {
        lemma_enc_powerset_eval(x);
        lemma_eval_eq(CompSpec::Id, enc_powerset(), x);
    } else if f == infinity_axiom() {
        lemma_enc_infinity_eval(x);
        lemma_eval_eq(CompSpec::Id, enc_infinity(), x);
    } else if f == foundation_axiom() {
        lemma_enc_foundation_eval(x);
        lemma_eval_eq(CompSpec::Id, enc_foundation(), x);
    } else {
        lemma_enc_choice_eval(x);
        lemma_eval_eq(CompSpec::Id, enc_choice(), x);
    }
}

} //  verus!
