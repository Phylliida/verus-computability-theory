use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_free_var_induction::*;
use crate::proof_system::*;

verus! {

///  Helper: cs_or evaluates to sum.
pub proof fn lemma_eval_cs_or(a: CompSpec, b: CompSpec, s: nat)
    ensures
        eval_comp(cs_or(a, b), s) == eval_comp(a, s) + eval_comp(b, s),
{
    lemma_eval_add(a, b, s);
}

//  ============================================================
//  Per-axiom correctness lemmas
//  ============================================================

///  check_axiom_identity returns nonzero for φ → φ.
#[verifier::rlimit(100)]
pub proof fn lemma_check_axiom_identity_correct(f: Formula)
    requires is_axiom_identity(f),
    ensures eval_comp(check_axiom_identity(), encode(f)) != 0,
{
    let phi: Formula = choose|phi: Formula| f == mk_implies(phi, phi);
    let x = encode(f);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(encode(phi), encode(phi)));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(encode(phi), encode(phi)));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(encode(phi), encode(phi));
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(encode(phi), encode(phi));
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_eval_cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),
        cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))), x);
}

///  check_axiom_eq_refl returns nonzero for t = t.
#[verifier::rlimit(100)]
pub proof fn lemma_check_axiom_eq_refl_correct(f: Formula)
    requires is_axiom_eq_refl(f),
    ensures eval_comp(check_axiom_eq_refl(), encode(f)) != 0,
{
    let t: Term = choose|t: Term| f == mk_eq(t, t);
    let x = encode(f);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(0nat, pair(encode_term(t), encode_term(t)));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(0nat, pair(encode_term(t), encode_term(t)));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(encode_term(t), encode_term(t));
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(encode_term(t), encode_term(t));
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(0), x);
    lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_eval_cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(0)),
        cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))), x);
}

///  check_axiom_iff_elim_left returns nonzero for (φ ↔ ψ) → (φ → ψ).
#[verifier::rlimit(100)]
pub proof fn lemma_check_axiom_iff_elim_left_correct(f: Formula)
    requires is_axiom_iff_elim_left(f),
    ensures eval_comp(check_axiom_iff_elim_left(), encode(f)) != 0,
{
    let w = choose|w: (Formula, Formula)|
        f == mk_implies(mk_iff(w.0, w.1), mk_implies(w.0, w.1));
    let (phi, psi) = (w.0, w.1);
    let ep = encode(phi);
    let es = encode(psi);
    let x = encode(f);
    let iff_enc = pair(6nat, pair(ep, es));
    let impl_enc = pair(5nat, pair(ep, es));

    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(iff_enc, impl_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(iff_enc, impl_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(iff_enc, impl_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(iff_enc, impl_enc);
    lemma_eval_fst(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(6nat, pair(ep, es));
    lemma_eval_fst(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(ep, es));
    lemma_eval_snd(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(6nat, pair(ep, es));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(5nat, pair(ep, es));

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5), x);
    lemma_eval_eq(cs_snd(cs_fst(cs_snd(CompSpec::Id))),
        cs_snd(cs_snd(cs_snd(CompSpec::Id))), x);

    let c4 = cs_eq(cs_snd(cs_fst(cs_snd(CompSpec::Id))),
        cs_snd(cs_snd(cs_snd(CompSpec::Id))));
    let c3 = cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5));
    let c2 = cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    lemma_eval_cs_and(c3, c4, x);
    lemma_eval_cs_and(c2, cs_and(c3, c4), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c4)), x);
}

///  check_axiom_iff_elim_right returns nonzero for (φ ↔ ψ) → (ψ → φ).
#[verifier::rlimit(100)]
pub proof fn lemma_check_axiom_iff_elim_right_correct(f: Formula)
    requires is_axiom_iff_elim_right(f),
    ensures eval_comp(check_axiom_iff_elim_right(), encode(f)) != 0,
{
    let w = choose|w: (Formula, Formula)|
        f == mk_implies(mk_iff(w.0, w.1), mk_implies(w.1, w.0));
    let (phi, psi) = (w.0, w.1);
    let ep = encode(phi);
    let es = encode(psi);
    let x = encode(f);
    let iff_enc = pair(6nat, pair(ep, es));
    let impl_enc = pair(5nat, pair(es, ep));

    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(iff_enc, impl_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(iff_enc, impl_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(iff_enc, impl_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(iff_enc, impl_enc);
    lemma_eval_fst(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(6nat, pair(ep, es));
    lemma_eval_fst(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(es, ep));
    lemma_eval_snd(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(6nat, pair(ep, es));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(5nat, pair(es, ep));
    lemma_eval_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id))), x);
    lemma_unpair1_pair(ep, es);
    lemma_eval_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id))), x);
    lemma_unpair2_pair(ep, es);
    lemma_eval_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id))), x);
    lemma_unpair1_pair(es, ep);
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), x);
    lemma_unpair2_pair(es, ep);

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))), x);
    lemma_eval_eq(cs_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id)))), x);

    let c5 = cs_eq(cs_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id)))));
    let c4 = cs_eq(cs_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))));
    let c3 = cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5));
    let c2 = cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    lemma_eval_cs_and(c4, c5, x);
    lemma_eval_cs_and(c3, cs_and(c4, c5), x);
    lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, c5)), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), x);
}

///  check_axiom_eq_subst_left returns nonzero for x=y → (φ[z/x] → φ[z/y]).
#[verifier::rlimit(100)]
pub proof fn lemma_check_axiom_eq_subst_left_correct(f: Formula)
    requires is_axiom_eq_subst_left(f),
    ensures eval_comp(check_axiom_eq_subst_left(), encode(f)) != 0,
{
    let w = choose|w: (Term, Term, Formula, nat)|
        f == mk_implies(mk_eq(w.0, w.1),
            mk_implies(subst(w.2, w.3, w.0), subst(w.2, w.3, w.1)));
    let (xt, yt, phi, var) = (w.0, w.1, w.2, w.3);
    let x = encode(f);
    let eq_enc = encode(mk_eq(xt, yt));
    let impl_enc = encode(mk_implies(subst(phi, var, xt), subst(phi, var, yt)));

    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(eq_enc, impl_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(eq_enc, impl_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(eq_enc, impl_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(eq_enc, impl_enc);
    lemma_eval_fst(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(0nat, pair(encode_term(xt), encode_term(yt)));
    lemma_eval_fst(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(encode(subst(phi, var, xt)), encode(subst(phi, var, yt))));

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(0), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5), x);

    let c3 = cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5));
    let c2 = cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(0));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    lemma_eval_cs_and(c2, c3, x);
    lemma_eval_cs_and(c1, cs_and(c2, c3), x);
}

///  check_axiom_eq_subst_right returns nonzero for x=y → (φ[z/y] → φ[z/x]).
#[verifier::rlimit(100)]
pub proof fn lemma_check_axiom_eq_subst_right_correct(f: Formula)
    requires is_axiom_eq_subst_right(f),
    ensures eval_comp(check_axiom_eq_subst_right(), encode(f)) != 0,
{
    let w = choose|w: (Term, Term, Formula, nat)|
        f == mk_implies(mk_eq(w.0, w.1),
            mk_implies(subst(w.2, w.3, w.1), subst(w.2, w.3, w.0)));
    let (xt, yt, phi, var) = (w.0, w.1, w.2, w.3);
    let x = encode(f);
    let eq_enc = encode(mk_eq(xt, yt));
    let impl_enc = encode(mk_implies(subst(phi, var, yt), subst(phi, var, xt)));

    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(eq_enc, impl_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(eq_enc, impl_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(eq_enc, impl_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(eq_enc, impl_enc);
    lemma_eval_fst(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(0nat, pair(encode_term(xt), encode_term(yt)));
    lemma_eval_fst(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(encode(subst(phi, var, yt)), encode(subst(phi, var, xt))));

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(0), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5), x);

    let c3 = cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5));
    let c2 = cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(0));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    lemma_eval_cs_and(c2, c3, x);
    lemma_eval_cs_and(c1, cs_and(c2, c3), x);
}

///  check_axiom_vacuous_quant returns nonzero for φ → ∀x.φ (x not free in φ).
#[verifier::rlimit(100)]
pub proof fn lemma_check_axiom_vacuous_quant_correct(f: Formula)
    requires is_axiom_vacuous_quant(f),
    ensures eval_comp(check_axiom_vacuous_quant(), encode(f)) != 0,
{
    let w = choose|w: (Formula, nat)|
        !free_vars(w.0).contains(w.1) &&
        f == mk_implies(w.0, mk_forall(w.1, w.0));
    let (phi, var) = (w.0, w.1);
    let ep = encode(phi);
    let x = encode(f);
    let right_enc = pair(7nat, pair(var, ep));

    let outer_content = cs_snd(CompSpec::Id);
    let phi_cs = cs_fst(outer_content);
    let right = cs_snd(outer_content);

    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(ep, right_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(ep, right_enc));
    lemma_eval_fst(outer_content, x);
    lemma_unpair1_pair(ep, right_enc);
    lemma_eval_snd(outer_content, x);
    lemma_unpair2_pair(ep, right_enc);
    lemma_eval_fst(right, x);
    lemma_unpair1_pair(7nat, pair(var, ep));
    lemma_eval_snd(right, x);
    lemma_unpair2_pair(7nat, pair(var, ep));
    let var_expr = cs_fst(cs_snd(right));
    let body_expr = cs_snd(cs_snd(right));
    lemma_eval_fst(cs_snd(right), x);
    lemma_unpair1_pair(var, ep);
    lemma_eval_snd(cs_snd(right), x);
    lemma_unpair2_pair(var, ep);

    lemma_eval_eq(phi_cs, body_expr, x);

    lemma_eval_pair(phi_cs, var_expr, x);
    lemma_eval_comp(has_free_var_comp(),
        CompSpec::CantorPair { left: Box::new(phi_cs), right: Box::new(var_expr) }, x);
    lemma_has_free_var_general(phi, var);
    lemma_eval_cs_not(
        cs_comp(has_free_var_comp(),
            CompSpec::CantorPair { left: Box::new(phi_cs), right: Box::new(var_expr) }), x);

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(right), cs_const(7), x);

    let c_not = cs_not(cs_comp(has_free_var_comp(), cs_pair(phi_cs, var_expr)));
    let c3 = cs_eq(phi_cs, body_expr);
    let c2 = cs_eq(cs_fst(right), cs_const(7));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    lemma_eval_cs_and(c3, c_not, x);
    lemma_eval_cs_and(c2, cs_and(c3, c_not), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c_not)), x);
}

} //  verus!
