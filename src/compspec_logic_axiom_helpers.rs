use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_free_var_induction::*;
use crate::compspec_subst_helpers::*;
use crate::proof_system::*;

verus! {

pub proof fn lemma_eval_cs_or(a: CompSpec, b: CompSpec, s: nat)
    ensures eval_comp(cs_or(a, b), s) == eval_comp(a, s) + eval_comp(b, s),
{ lemma_eval_add(a, b, s); }

//  ============================================================
//  Encoding structure lemmas
//  ============================================================
proof fn lemma_encode_implies(a: Formula, b: Formula)
    ensures encode(mk_implies(a, b)) == pair(5nat, pair(encode(a), encode(b))),
{}

proof fn lemma_encode_iff(a: Formula, b: Formula)
    ensures encode(mk_iff(a, b)) == pair(6nat, pair(encode(a), encode(b))),
{}

proof fn lemma_encode_eq(a: Term, b: Term)
    ensures encode(mk_eq(a, b)) == pair(0nat, pair(encode_term(a), encode_term(b))),
{}

proof fn lemma_encode_forall(v: nat, sub: Formula)
    ensures encode(mk_forall(v, sub)) == pair(7nat, pair(v, encode(sub))),
{}

//  ============================================================
//  Identity: φ → φ
//  ============================================================
pub proof fn identity_evals(phi: Formula)
    ensures ({
        let x = encode(mk_implies(phi, phi));
        eval_comp(cs_fst(CompSpec::Id), x) == 5 &&
        eval_comp(cs_fst(cs_snd(CompSpec::Id)), x) == encode(phi) &&
        eval_comp(cs_snd(cs_snd(CompSpec::Id)), x) == encode(phi)
    }),
{
    let ep = encode(phi);
    let x = encode(mk_implies(phi, phi));
    lemma_encode_implies(phi, phi);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(ep, ep));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(ep, ep));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(ep, ep);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(ep, ep);
}

pub proof fn identity_compose(f: Formula, phi: Formula)
    requires f == mk_implies(phi, phi),
    ensures eval_comp(check_axiom_identity(), encode(f)) != 0,
{
    let x = encode(f);
    identity_evals(phi);
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_eval_cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(5)),
        cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))), x);
}

//  ============================================================
//  Eq refl: t = t
//  ============================================================
pub proof fn eq_refl_evals(t: Term)
    ensures ({
        let x = encode(mk_eq(t, t));
        eval_comp(cs_fst(CompSpec::Id), x) == 0 &&
        eval_comp(cs_fst(cs_snd(CompSpec::Id)), x) == encode_term(t) &&
        eval_comp(cs_snd(cs_snd(CompSpec::Id)), x) == encode_term(t)
    }),
{
    let et = encode_term(t);
    let x = encode(mk_eq(t, t));
    lemma_encode_eq(t, t);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(0nat, pair(et, et));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(0nat, pair(et, et));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(et, et);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(et, et);
}

proof fn eq_refl_checks(t: Term)
    ensures ({
        let x = encode(mk_eq(t, t));
        eval_comp(cs_eq(cs_fst(CompSpec::Id), cs_const(0)), x) == 1 &&
        eval_comp(cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))), x) == 1
    }),
{
    let x = encode(mk_eq(t, t));
    eq_refl_evals(t);
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(0), x);
    lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), x);
}

pub proof fn eq_refl_compose(f: Formula, t: Term)
    requires f == mk_eq(t, t),
    ensures eval_comp(check_axiom_eq_refl(), encode(f)) != 0,
{
    let x = encode(f);
    eq_refl_checks(t);
    lemma_eval_cs_and(
        cs_eq(cs_fst(CompSpec::Id), cs_const(0)),
        cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))), x);
}

//  ============================================================
//  Iff elim left: (φ ↔ ψ) → (φ → ψ)
//  ============================================================
pub proof fn iff_elim_left_tags(phi: Formula, psi: Formula)
    ensures ({
        let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(phi, psi)));
        eval_comp(cs_fst(CompSpec::Id), x) == 5 &&
        eval_comp(cs_fst(cs_fst(cs_snd(CompSpec::Id))), x) == 6 &&
        eval_comp(cs_fst(cs_snd(cs_snd(CompSpec::Id))), x) == 5
    }),
{
    let ep = encode(phi);
    let es = encode(psi);
    let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(phi, psi)));
    lemma_encode_implies(mk_iff(phi, psi), mk_implies(phi, psi));
    lemma_encode_iff(phi, psi);
    lemma_encode_implies(phi, psi);
    let le = encode(mk_iff(phi, psi));
    let re = encode(mk_implies(phi, psi));
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(le, re));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(le, re));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(le, re);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(le, re);
    lemma_eval_fst(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(6nat, pair(ep, es));
    lemma_eval_fst(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(ep, es));
}

pub proof fn iff_elim_left_content(phi: Formula, psi: Formula)
    ensures ({
        let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(phi, psi)));
        eval_comp(cs_snd(cs_fst(cs_snd(CompSpec::Id))), x)
            == eval_comp(cs_snd(cs_snd(cs_snd(CompSpec::Id))), x)
    }),
{
    let ep = encode(phi);
    let es = encode(psi);
    let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(phi, psi)));
    lemma_encode_implies(mk_iff(phi, psi), mk_implies(phi, psi));
    lemma_encode_iff(phi, psi);
    lemma_encode_implies(phi, psi);
    let le = encode(mk_iff(phi, psi));
    let re = encode(mk_implies(phi, psi));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(le, re));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(le, re);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(le, re);
    lemma_eval_snd(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(6nat, pair(ep, es));
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(5nat, pair(ep, es));
}

pub proof fn iff_elim_left_compose(f: Formula, phi: Formula, psi: Formula)
    requires f == mk_implies(mk_iff(phi, psi), mk_implies(phi, psi)),
    ensures eval_comp(check_axiom_iff_elim_left(), encode(f)) != 0,
{
    let x = encode(f);
    iff_elim_left_tags(phi, psi);
    iff_elim_left_content(phi, psi);
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6));
    let c3 = cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5));
    let c4 = cs_eq(cs_snd(cs_fst(cs_snd(CompSpec::Id))),
        cs_snd(cs_snd(cs_snd(CompSpec::Id))));
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5), x);
    lemma_eval_eq(cs_snd(cs_fst(cs_snd(CompSpec::Id))),
        cs_snd(cs_snd(cs_snd(CompSpec::Id))), x);
    lemma_eval_cs_and(c3, c4, x);
    lemma_eval_cs_and(c2, cs_and(c3, c4), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c4)), x);
}

//  ============================================================
//  Iff elim right: (φ ↔ ψ) → (ψ → φ)
//  ============================================================
pub proof fn iff_elim_right_tags(phi: Formula, psi: Formula)
    ensures ({
        let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(psi, phi)));
        eval_comp(cs_fst(CompSpec::Id), x) == 5 &&
        eval_comp(cs_fst(cs_fst(cs_snd(CompSpec::Id))), x) == 6 &&
        eval_comp(cs_fst(cs_snd(cs_snd(CompSpec::Id))), x) == 5
    }),
{
    let ep = encode(phi);
    let es = encode(psi);
    let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(psi, phi)));
    lemma_encode_implies(mk_iff(phi, psi), mk_implies(psi, phi));
    lemma_encode_iff(phi, psi);
    lemma_encode_implies(psi, phi);
    let le = encode(mk_iff(phi, psi));
    let re = encode(mk_implies(psi, phi));
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(le, re));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(le, re));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(le, re);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(le, re);
    lemma_eval_fst(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(6nat, pair(ep, es));
    lemma_eval_fst(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(es, ep));
}

pub proof fn iff_elim_right_content(phi: Formula, psi: Formula)
    ensures ({
        let ep = encode(phi);
        let es = encode(psi);
        let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(psi, phi)));
        //  φ from Iff == right-snd from Implies (both ep)
        eval_comp(cs_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id)))), x) == ep &&
        eval_comp(cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))), x) == ep &&
        //  ψ from Iff == left from Implies (both es)
        eval_comp(cs_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id)))), x) == es &&
        eval_comp(cs_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id)))), x) == es
    }),
{
    let ep = encode(phi);
    let es = encode(psi);
    let x = encode(mk_implies(mk_iff(phi, psi), mk_implies(psi, phi)));
    lemma_encode_implies(mk_iff(phi, psi), mk_implies(psi, phi));
    lemma_encode_iff(phi, psi);
    lemma_encode_implies(psi, phi);
    let le = encode(mk_iff(phi, psi));
    let re = encode(mk_implies(psi, phi));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(le, re));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(le, re);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(le, re);
    lemma_eval_snd(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(6nat, pair(ep, es));
    lemma_eval_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id))), x);
    lemma_unpair1_pair(ep, es);
    lemma_eval_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id))), x);
    lemma_unpair2_pair(ep, es);
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair2_pair(5nat, pair(es, ep));
    lemma_eval_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id))), x);
    lemma_unpair1_pair(es, ep);
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), x);
    lemma_unpair2_pair(es, ep);
}

pub proof fn iff_elim_right_compose(f: Formula, phi: Formula, psi: Formula)
    requires f == mk_implies(mk_iff(phi, psi), mk_implies(psi, phi)),
    ensures eval_comp(check_axiom_iff_elim_right(), encode(f)) != 0,
{
    let x = encode(f);
    iff_elim_right_tags(phi, psi);
    iff_elim_right_content(phi, psi);
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6));
    let c3 = cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5));
    let c4 = cs_eq(cs_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))));
    let c5 = cs_eq(cs_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id)))));
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(6), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id)))), x);
    lemma_eval_eq(cs_snd(cs_snd(cs_fst(cs_snd(CompSpec::Id)))),
        cs_fst(cs_snd(cs_snd(cs_snd(CompSpec::Id)))), x);
    lemma_eval_cs_and(c4, c5, x);
    lemma_eval_cs_and(c3, cs_and(c4, c5), x);
    lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, c5)), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), x);
}

//  ============================================================
//  Eq subst left: x=y → (φ[z/x] → φ[z/y]) — partial tag check
//  ============================================================
proof fn eq_subst_tags(f: Formula, xt: Term, yt: Term, sl: Formula, sr: Formula)
    requires f == mk_implies(mk_eq(xt, yt), mk_implies(sl, sr)),
    ensures
        eval_comp(cs_fst(CompSpec::Id), encode(f)) == 5,
        eval_comp(cs_fst(cs_fst(cs_snd(CompSpec::Id))), encode(f)) == 0,
        eval_comp(cs_fst(cs_snd(cs_snd(CompSpec::Id))), encode(f)) == 5,
{
    let x = encode(f);
    let eq_enc = encode(mk_eq(xt, yt));
    let impl_enc = encode(mk_implies(sl, sr));
    lemma_encode_implies(mk_eq(xt, yt), mk_implies(sl, sr));
    lemma_encode_eq(xt, yt);
    lemma_encode_implies(sl, sr);
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
    lemma_unpair1_pair(5nat, pair(encode(sl), encode(sr)));
}

pub proof fn eq_subst_left_inner(f: Formula, xt: Term, yt: Term, sl: Formula, sr: Formula)
    requires f == mk_implies(mk_eq(xt, yt), mk_implies(sl, sr)),
    ensures eval_comp(check_axiom_eq_subst_left(), encode(f)) != 0,
{
    let x = encode(f);
    eq_subst_tags(f, xt, yt, sl, sr);
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(0), x);
    lemma_eval_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5), x);
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(cs_fst(cs_snd(CompSpec::Id))), cs_const(0));
    let c3 = cs_eq(cs_fst(cs_snd(cs_snd(CompSpec::Id))), cs_const(5));
    lemma_eval_cs_and(c2, c3, x);
    lemma_eval_cs_and(c1, cs_and(c2, c3), x);
}

//  ============================================================
//  Eq subst right: x=y → (φ[z/y] → φ[z/x])
//  ============================================================
pub proof fn eq_subst_right_inner(f: Formula, xt: Term, yt: Term, sl: Formula, sr: Formula)
    requires f == mk_implies(mk_eq(xt, yt), mk_implies(sl, sr)),
    ensures eval_comp(check_axiom_eq_subst_right(), encode(f)) != 0,
{
    //  check_axiom_eq_subst_right() == check_axiom_eq_subst_left() (same CompSpec)
    eq_subst_left_inner(f, xt, yt, sl, sr);
}

//  ============================================================
//  Vacuous quantification: φ → ∀x.φ (x not free in φ)
//  ============================================================
pub proof fn vacuous_quant_tags(phi: Formula, var: nat)
    ensures ({
        let x = encode(mk_implies(phi, mk_forall(var, phi)));
        let right = cs_snd(cs_snd(CompSpec::Id));
        eval_comp(cs_fst(CompSpec::Id), x) == 5 &&
        eval_comp(cs_fst(right), x) == 7 &&
        eval_comp(cs_fst(cs_snd(CompSpec::Id)), x) == encode(phi) &&
        eval_comp(cs_snd(cs_snd(right)), x) == encode(phi) &&
        eval_comp(cs_fst(cs_snd(right)), x) == var
    }),
{
    let ep = encode(phi);
    let x = encode(mk_implies(phi, mk_forall(var, phi)));
    let right_enc = encode(mk_forall(var, phi));
    lemma_encode_implies(phi, mk_forall(var, phi));
    lemma_encode_forall(var, phi);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(ep, right_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(ep, right_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(ep, right_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(ep, right_enc);
    let right = cs_snd(cs_snd(CompSpec::Id));
    lemma_eval_fst(right, x);
    lemma_unpair1_pair(7nat, pair(var, ep));
    lemma_eval_snd(right, x);
    lemma_unpair2_pair(7nat, pair(var, ep));
    lemma_eval_fst(cs_snd(right), x);
    lemma_unpair1_pair(var, ep);
    lemma_eval_snd(cs_snd(right), x);
    lemma_unpair2_pair(var, ep);
}

pub proof fn vacuous_quant_freevar(phi: Formula, var: nat)
    requires !has_free_var(phi, var),
    ensures ({
        let x = encode(mk_implies(phi, mk_forall(var, phi)));
        let phi_cs = cs_fst(cs_snd(CompSpec::Id));
        let right = cs_snd(cs_snd(CompSpec::Id));
        eval_comp(cs_not(cs_comp(has_free_var_comp(),
            cs_pair(phi_cs, cs_fst(cs_snd(right))))), x) == 1
    }),
{
    let ep = encode(phi);
    let x = encode(mk_implies(phi, mk_forall(var, phi)));
    let right_enc = encode(mk_forall(var, phi));
    let phi_cs = cs_fst(cs_snd(CompSpec::Id));
    let right = cs_snd(cs_snd(CompSpec::Id));
    lemma_encode_implies(phi, mk_forall(var, phi));
    lemma_encode_forall(var, phi);
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(ep, right_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(ep, right_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(ep, right_enc);
    lemma_eval_snd(right, x);
    lemma_unpair2_pair(7nat, pair(var, ep));
    lemma_eval_fst(cs_snd(right), x);
    lemma_unpair1_pair(var, ep);
    lemma_eval_pair(phi_cs, cs_fst(cs_snd(right)), x);
    lemma_eval_comp(has_free_var_comp(), cs_pair(phi_cs, cs_fst(cs_snd(right))), x);
    lemma_has_free_var_general(phi, var);
    lemma_eval_cs_not(cs_comp(has_free_var_comp(), cs_pair(phi_cs, cs_fst(cs_snd(right)))), x);
}

pub proof fn vacuous_quant_compose(f: Formula, phi: Formula, var: nat)
    requires f == mk_implies(phi, mk_forall(var, phi)),
        !has_free_var(phi, var),
    ensures eval_comp(check_axiom_vacuous_quant(), encode(f)) != 0,
{
    let x = encode(f);
    let phi_cs = cs_fst(cs_snd(CompSpec::Id));
    let right = cs_snd(cs_snd(CompSpec::Id));
    vacuous_quant_tags(phi, var);
    vacuous_quant_freevar(phi, var);
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(right), cs_const(7));
    let c3 = cs_eq(phi_cs, cs_snd(cs_snd(right)));
    let c_not = cs_not(cs_comp(has_free_var_comp(), cs_pair(phi_cs, cs_fst(cs_snd(right)))));
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(right), cs_const(7), x);
    lemma_eval_eq(phi_cs, cs_snd(cs_snd(right)), x);
    lemma_eval_cs_and(c3, c_not, x);
    lemma_eval_cs_and(c2, cs_and(c3, c_not), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c_not)), x);
}

//  ============================================================
//  Iff intro: (φ→ψ) → ((ψ→φ) → (φ↔ψ))
//  ============================================================
proof fn iff_intro_tags(f: Formula, phi: Formula, psi: Formula)
    requires f == mk_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, phi), mk_iff(phi, psi))),
    ensures
        eval_comp(cs_fst(CompSpec::Id), encode(f)) == 5,
        eval_comp(cs_fst(cs_fst(cs_snd(CompSpec::Id))), encode(f)) == 5,
        eval_comp(cs_fst(cs_snd(cs_snd(CompSpec::Id))), encode(f)) == 5,
{
    let x = encode(f);
    let l_enc = encode(mk_implies(phi, psi));
    let r_enc = encode(mk_implies(mk_implies(psi, phi), mk_iff(phi, psi)));
    lemma_encode_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, phi), mk_iff(phi, psi)));
    lemma_encode_implies(phi, psi);
    lemma_encode_implies(mk_implies(psi, phi), mk_iff(phi, psi));
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(l_enc, r_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(l_enc, r_enc);
    lemma_eval_fst(cs_fst(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(encode(phi), encode(psi)));
    lemma_eval_fst(cs_snd(cs_snd(CompSpec::Id)), x);
    lemma_unpair1_pair(5nat, pair(encode(mk_implies(psi, phi)), encode(mk_iff(phi, psi))));
}

proof fn iff_intro_content(f: Formula, phi: Formula, psi: Formula)
    requires f == mk_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, phi), mk_iff(phi, psi))),
    ensures ({
        let x = encode(f);
        let l = cs_fst(cs_snd(CompSpec::Id));
        let r = cs_snd(cs_snd(CompSpec::Id));
        let phi_e = cs_fst(cs_snd(l));
        let psi_e = cs_snd(cs_snd(l));
        //  R.left == pair(5, pair(ψ, φ))
        eval_comp(cs_fst(cs_snd(r)), x) == pair(5nat, pair(eval_comp(psi_e, x), eval_comp(phi_e, x)))
        &&
        //  R.right == pair(6, snd(L))
        eval_comp(cs_snd(cs_snd(r)), x) == pair(6nat, eval_comp(cs_snd(l), x))
    }),
{
    let x = encode(f);
    let ep = encode(phi);
    let es = encode(psi);
    let l_enc = encode(mk_implies(phi, psi));
    let r_enc = encode(mk_implies(mk_implies(psi, phi), mk_iff(phi, psi)));
    lemma_encode_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, phi), mk_iff(phi, psi)));
    lemma_encode_implies(phi, psi);
    lemma_encode_implies(mk_implies(psi, phi), mk_iff(phi, psi));
    lemma_encode_implies(psi, phi);
    lemma_encode_iff(phi, psi);

    let l = cs_fst(cs_snd(CompSpec::Id));
    let r = cs_snd(cs_snd(CompSpec::Id));

    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(l_enc, r_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(l_enc, r_enc);

    //  L content
    lemma_eval_snd(l, x);
    lemma_unpair2_pair(5nat, pair(ep, es));
    lemma_eval_fst(cs_snd(l), x);
    lemma_unpair1_pair(ep, es);
    lemma_eval_snd(cs_snd(l), x);
    lemma_unpair2_pair(ep, es);

    //  R content
    let r_left_enc = encode(mk_implies(psi, phi));
    let r_right_enc = encode(mk_iff(phi, psi));
    lemma_eval_snd(r, x);
    lemma_unpair2_pair(5nat, pair(r_left_enc, r_right_enc));
    lemma_eval_fst(cs_snd(r), x);
    lemma_unpair1_pair(r_left_enc, r_right_enc);
    lemma_eval_snd(cs_snd(r), x);
    lemma_unpair2_pair(r_left_enc, r_right_enc);
}

pub proof fn iff_intro_compose(f: Formula, phi: Formula, psi: Formula)
    requires f == mk_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, phi), mk_iff(phi, psi))),
    ensures eval_comp(check_axiom_iff_intro(), encode(f)) != 0,
{
    let x = encode(f);
    let l = cs_fst(cs_snd(CompSpec::Id));
    let r = cs_snd(cs_snd(CompSpec::Id));
    let phi_e = cs_fst(cs_snd(l));
    let psi_e = cs_snd(cs_snd(l));

    iff_intro_tags(f, phi, psi);
    iff_intro_content(f, phi, psi);

    //  Construct expected values for R.left and R.right
    let r_left_expected = CompSpec::CantorPair {
        left: Box::new(cs_const(5)),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(psi_e), right: Box::new(phi_e) }),
    };
    let r_right_expected = CompSpec::CantorPair {
        left: Box::new(cs_const(6)),
        right: Box::new(cs_snd(l)),
    };
    lemma_eval_pair(psi_e, phi_e, x);
    lemma_eval_pair(cs_const(5), CompSpec::CantorPair {
        left: Box::new(psi_e), right: Box::new(phi_e) }, x);
    lemma_eval_pair(cs_const(6), cs_snd(l), x);

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(l), cs_const(5), x);
    lemma_eval_eq(cs_fst(r), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_snd(r)), r_left_expected, x);
    lemma_eval_eq(cs_snd(cs_snd(r)), r_right_expected, x);

    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(l), cs_const(5));
    let c3 = cs_eq(cs_fst(r), cs_const(5));
    let c4 = cs_eq(cs_fst(cs_snd(r)), r_left_expected);
    let c5 = cs_eq(cs_snd(cs_snd(r)), r_right_expected);
    lemma_eval_cs_and(c4, c5, x);
    lemma_eval_cs_and(c3, cs_and(c4, c5), x);
    lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, c5)), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), x);
}

//  ============================================================
//  Hyp syllogism: (φ→ψ) → ((ψ→χ) → (φ→χ))
//  ============================================================
proof fn hyp_syl_tags(f: Formula, phi: Formula, psi: Formula, chi: Formula)
    requires f == mk_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, chi), mk_implies(phi, chi))),
    ensures ({
        let x = encode(f);
        let content = cs_snd(CompSpec::Id);
        let l = cs_fst(content);
        let r = cs_snd(content);
        let m = cs_fst(cs_snd(r));
        let n = cs_snd(cs_snd(r));
        eval_comp(cs_fst(CompSpec::Id), x) == 5 &&
        eval_comp(cs_fst(l), x) == 5 &&
        eval_comp(cs_fst(r), x) == 5 &&
        eval_comp(cs_fst(m), x) == 5 &&
        eval_comp(cs_fst(n), x) == 5
    }),
{
    let x = encode(f);
    let ep = encode(phi); let es = encode(psi); let ec = encode(chi);
    let l_enc = encode(mk_implies(phi, psi));
    let m_enc = encode(mk_implies(psi, chi));
    let n_enc = encode(mk_implies(phi, chi));
    let r_enc = encode(mk_implies(mk_implies(psi, chi), mk_implies(phi, chi)));
    lemma_encode_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, chi), mk_implies(phi, chi)));
    lemma_encode_implies(mk_implies(psi, chi), mk_implies(phi, chi));
    lemma_encode_implies(phi, psi);
    lemma_encode_implies(psi, chi);
    lemma_encode_implies(phi, chi);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_fst(content, x);
    lemma_unpair1_pair(l_enc, r_enc);
    lemma_eval_snd(content, x);
    lemma_unpair2_pair(l_enc, r_enc);
    lemma_eval_fst(l, x);
    lemma_unpair1_pair(5nat, pair(ep, es));
    lemma_eval_fst(r, x);
    lemma_unpair1_pair(5nat, pair(m_enc, n_enc));
    lemma_eval_snd(r, x);
    lemma_unpair2_pair(5nat, pair(m_enc, n_enc));
    lemma_eval_fst(cs_snd(r), x);
    lemma_unpair1_pair(m_enc, n_enc);
    lemma_eval_snd(cs_snd(r), x);
    lemma_unpair2_pair(m_enc, n_enc);
    let m = cs_fst(cs_snd(r));
    let n = cs_snd(cs_snd(r));
    lemma_eval_fst(m, x);
    lemma_unpair1_pair(5nat, pair(es, ec));
    lemma_eval_fst(n, x);
    lemma_unpair1_pair(5nat, pair(ep, ec));
}

proof fn hyp_syl_content(f: Formula, phi: Formula, psi: Formula, chi: Formula)
    requires f == mk_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, chi), mk_implies(phi, chi))),
    ensures ({
        let x = encode(f);
        let content = cs_snd(CompSpec::Id);
        let l = cs_fst(content);
        let r = cs_snd(content);
        let m = cs_fst(cs_snd(r));
        let n = cs_snd(cs_snd(r));
        let phi_e = cs_fst(cs_snd(l));
        let psi_e = cs_snd(cs_snd(l));
        //  ψ' == ψ, φ' == φ, χ' == χ
        eval_comp(cs_fst(cs_snd(m)), x) == eval_comp(psi_e, x) &&
        eval_comp(cs_fst(cs_snd(n)), x) == eval_comp(phi_e, x) &&
        eval_comp(cs_snd(cs_snd(n)), x) == eval_comp(cs_snd(cs_snd(m)), x)
    }),
{
    let x = encode(f);
    let ep = encode(phi); let es = encode(psi); let ec = encode(chi);
    let l_enc = encode(mk_implies(phi, psi));
    let m_enc = encode(mk_implies(psi, chi));
    let n_enc = encode(mk_implies(phi, chi));
    let r_enc = encode(mk_implies(mk_implies(psi, chi), mk_implies(phi, chi)));
    lemma_encode_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, chi), mk_implies(phi, chi)));
    lemma_encode_implies(mk_implies(psi, chi), mk_implies(phi, chi));
    lemma_encode_implies(phi, psi);
    lemma_encode_implies(psi, chi);
    lemma_encode_implies(phi, chi);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    //  Navigate to L content
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_fst(content, x);
    lemma_unpair1_pair(l_enc, r_enc);
    lemma_eval_snd(l, x);
    lemma_unpair2_pair(5nat, pair(ep, es));
    lemma_eval_fst(cs_snd(l), x);
    lemma_unpair1_pair(ep, es);
    lemma_eval_snd(cs_snd(l), x);
    lemma_unpair2_pair(ep, es);
    //  Navigate to M, N content
    lemma_eval_snd(content, x);
    lemma_unpair2_pair(l_enc, r_enc);
    lemma_eval_snd(r, x);
    lemma_unpair2_pair(5nat, pair(m_enc, n_enc));
    lemma_eval_fst(cs_snd(r), x);
    lemma_unpair1_pair(m_enc, n_enc);
    lemma_eval_snd(cs_snd(r), x);
    lemma_unpair2_pair(m_enc, n_enc);
    let m = cs_fst(cs_snd(r));
    let n = cs_snd(cs_snd(r));
    lemma_eval_snd(m, x);
    lemma_unpair2_pair(5nat, pair(es, ec));
    lemma_eval_fst(cs_snd(m), x);
    lemma_unpair1_pair(es, ec);
    lemma_eval_snd(cs_snd(m), x);
    lemma_unpair2_pair(es, ec);
    lemma_eval_snd(n, x);
    lemma_unpair2_pair(5nat, pair(ep, ec));
    lemma_eval_fst(cs_snd(n), x);
    lemma_unpair1_pair(ep, ec);
    lemma_eval_snd(cs_snd(n), x);
    lemma_unpair2_pair(ep, ec);
}

pub proof fn hyp_syl_compose(f: Formula, phi: Formula, psi: Formula, chi: Formula)
    requires f == mk_implies(mk_implies(phi, psi),
        mk_implies(mk_implies(psi, chi), mk_implies(phi, chi))),
    ensures eval_comp(check_axiom_hyp_syllogism(), encode(f)) != 0,
{
    let x = encode(f);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    let m = cs_fst(cs_snd(r));
    let n = cs_snd(cs_snd(r));
    let phi_e = cs_fst(cs_snd(l));
    let psi_e = cs_snd(cs_snd(l));

    hyp_syl_tags(f, phi, psi, chi);
    hyp_syl_content(f, phi, psi, chi);

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(l), cs_const(5), x);
    lemma_eval_eq(cs_fst(r), cs_const(5), x);
    lemma_eval_eq(cs_fst(m), cs_const(5), x);
    lemma_eval_eq(cs_fst(n), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_snd(m)), psi_e, x);
    lemma_eval_eq(cs_fst(cs_snd(n)), phi_e, x);
    lemma_eval_eq(cs_snd(cs_snd(n)), cs_snd(cs_snd(m)), x);

    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(l), cs_const(5));
    let c3 = cs_eq(cs_fst(r), cs_const(5));
    let c4 = cs_eq(cs_fst(m), cs_const(5));
    let c5 = cs_eq(cs_fst(n), cs_const(5));
    let c6 = cs_eq(cs_fst(cs_snd(m)), psi_e);
    let c7 = cs_eq(cs_fst(cs_snd(n)), phi_e);
    let c8 = cs_eq(cs_snd(cs_snd(n)), cs_snd(cs_snd(m)));
    lemma_eval_cs_and(c7, c8, x);
    lemma_eval_cs_and(c6, cs_and(c7, c8), x);
    lemma_eval_cs_and(c5, cs_and(c6, cs_and(c7, c8)), x);
    lemma_eval_cs_and(c4, cs_and(c5, cs_and(c6, cs_and(c7, c8))), x);
    lemma_eval_cs_and(c3, cs_and(c4, cs_and(c5, cs_and(c6, cs_and(c7, c8)))), x);
    lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, cs_and(c5, cs_and(c6, cs_and(c7, c8))))), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, cs_and(c5, cs_and(c6, cs_and(c7, c8)))))), x);
}

//  ============================================================
//  Quantifier dist: (∀x.(φ→ψ)) → ((∀x.φ) → (∀x.ψ))
//  ============================================================
proof fn quant_dist_tags(f: Formula, phi: Formula, psi: Formula, var: nat)
    requires f == mk_implies(mk_forall(var, mk_implies(phi, psi)),
        mk_implies(mk_forall(var, phi), mk_forall(var, psi))),
    ensures ({
        let x = encode(f);
        let content = cs_snd(CompSpec::Id);
        let l = cs_fst(content);
        let r = cs_snd(content);
        let body = cs_snd(cs_snd(l));
        eval_comp(cs_fst(CompSpec::Id), x) == 5 &&
        eval_comp(cs_fst(l), x) == 7 &&
        eval_comp(cs_fst(body), x) == 5 &&
        eval_comp(cs_fst(r), x) == 5
    }),
{
    let x = encode(f);
    let ep = encode(phi); let es = encode(psi);
    let body_enc = encode(mk_implies(phi, psi));
    let l_enc = encode(mk_forall(var, mk_implies(phi, psi)));
    let r_enc = encode(mk_implies(mk_forall(var, phi), mk_forall(var, psi)));
    lemma_encode_implies(mk_forall(var, mk_implies(phi, psi)),
        mk_implies(mk_forall(var, phi), mk_forall(var, psi)));
    lemma_encode_forall(var, mk_implies(phi, psi));
    lemma_encode_implies(phi, psi);
    lemma_encode_implies(mk_forall(var, phi), mk_forall(var, psi));
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_fst(content, x);
    lemma_unpair1_pair(l_enc, r_enc);
    lemma_eval_snd(content, x);
    lemma_unpair2_pair(l_enc, r_enc);
    lemma_eval_fst(l, x);
    lemma_unpair1_pair(7nat, pair(var, body_enc));
    lemma_eval_snd(l, x);
    lemma_unpair2_pair(7nat, pair(var, body_enc));
    lemma_eval_snd(cs_snd(l), x);
    lemma_unpair2_pair(var, body_enc);
    let body = cs_snd(cs_snd(l));
    lemma_eval_fst(body, x);
    lemma_unpair1_pair(5nat, pair(ep, es));
    lemma_eval_fst(r, x);
    lemma_unpair1_pair(5nat, pair(encode(mk_forall(var, phi)), encode(mk_forall(var, psi))));
}

proof fn quant_dist_content(f: Formula, phi: Formula, psi: Formula, var: nat)
    requires f == mk_implies(mk_forall(var, mk_implies(phi, psi)),
        mk_implies(mk_forall(var, phi), mk_forall(var, psi))),
    ensures ({
        let x = encode(f);
        let content = cs_snd(CompSpec::Id);
        let l = cs_fst(content);
        let r = cs_snd(content);
        let v = cs_fst(cs_snd(l));
        let body = cs_snd(cs_snd(l));
        let phi_e = cs_fst(cs_snd(body));
        let psi_e = cs_snd(cs_snd(body));
        //  R.left == pair(7, pair(v, φ))
        eval_comp(cs_fst(cs_snd(r)), x)
            == pair(7nat, pair(eval_comp(v, x), eval_comp(phi_e, x)))
        &&
        //  R.right == pair(7, pair(v, ψ))
        eval_comp(cs_snd(cs_snd(r)), x)
            == pair(7nat, pair(eval_comp(v, x), eval_comp(psi_e, x)))
    }),
{
    let x = encode(f);
    let ep = encode(phi); let es = encode(psi);
    let body_enc = encode(mk_implies(phi, psi));
    let l_enc = encode(mk_forall(var, mk_implies(phi, psi)));
    let r_left_enc = encode(mk_forall(var, phi));
    let r_right_enc = encode(mk_forall(var, psi));
    let r_enc = encode(mk_implies(mk_forall(var, phi), mk_forall(var, psi)));
    lemma_encode_implies(mk_forall(var, mk_implies(phi, psi)),
        mk_implies(mk_forall(var, phi), mk_forall(var, psi)));
    lemma_encode_forall(var, mk_implies(phi, psi));
    lemma_encode_implies(phi, psi);
    lemma_encode_implies(mk_forall(var, phi), mk_forall(var, psi));
    lemma_encode_forall(var, phi);
    lemma_encode_forall(var, psi);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    //  Navigate
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(l_enc, r_enc));
    lemma_eval_fst(content, x);
    lemma_unpair1_pair(l_enc, r_enc);
    lemma_eval_snd(content, x);
    lemma_unpair2_pair(l_enc, r_enc);
    //  L: Forall(v, body)
    lemma_eval_snd(l, x);
    lemma_unpair2_pair(7nat, pair(var, body_enc));
    lemma_eval_fst(cs_snd(l), x);
    lemma_unpair1_pair(var, body_enc);
    lemma_eval_snd(cs_snd(l), x);
    lemma_unpair2_pair(var, body_enc);
    //  Body content: phi, psi
    let body = cs_snd(cs_snd(l));
    lemma_eval_snd(body, x);
    lemma_unpair2_pair(5nat, pair(ep, es));
    lemma_eval_fst(cs_snd(body), x);
    lemma_unpair1_pair(ep, es);
    lemma_eval_snd(cs_snd(body), x);
    lemma_unpair2_pair(ep, es);
    //  R content
    lemma_eval_snd(r, x);
    lemma_unpair2_pair(5nat, pair(r_left_enc, r_right_enc));
    lemma_eval_fst(cs_snd(r), x);
    lemma_unpair1_pair(r_left_enc, r_right_enc);
    lemma_eval_snd(cs_snd(r), x);
    lemma_unpair2_pair(r_left_enc, r_right_enc);
}

pub proof fn quant_dist_compose(f: Formula, phi: Formula, psi: Formula, var: nat)
    requires f == mk_implies(mk_forall(var, mk_implies(phi, psi)),
        mk_implies(mk_forall(var, phi), mk_forall(var, psi))),
    ensures eval_comp(check_axiom_quantifier_dist(), encode(f)) != 0,
{
    let x = encode(f);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    let v = cs_fst(cs_snd(l));
    let body = cs_snd(cs_snd(l));
    let phi_e = cs_fst(cs_snd(body));
    let psi_e = cs_snd(cs_snd(body));

    quant_dist_tags(f, phi, psi, var);
    quant_dist_content(f, phi, psi, var);

    let r_left_expected = CompSpec::CantorPair {
        left: Box::new(cs_const(7)),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(v), right: Box::new(phi_e) }),
    };
    let r_right_expected = CompSpec::CantorPair {
        left: Box::new(cs_const(7)),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(v), right: Box::new(psi_e) }),
    };
    lemma_eval_pair(v, phi_e, x);
    lemma_eval_pair(cs_const(7), CompSpec::CantorPair {
        left: Box::new(v), right: Box::new(phi_e) }, x);
    lemma_eval_pair(v, psi_e, x);
    lemma_eval_pair(cs_const(7), CompSpec::CantorPair {
        left: Box::new(v), right: Box::new(psi_e) }, x);

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(l), cs_const(7), x);
    lemma_eval_eq(cs_fst(body), cs_const(5), x);
    lemma_eval_eq(cs_fst(r), cs_const(5), x);
    lemma_eval_eq(cs_fst(cs_snd(r)), r_left_expected, x);
    lemma_eval_eq(cs_snd(cs_snd(r)), r_right_expected, x);

    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(l), cs_const(7));
    let c3 = cs_eq(cs_fst(body), cs_const(5));
    let c4 = cs_eq(cs_fst(r), cs_const(5));
    let c5 = cs_eq(cs_fst(cs_snd(r)), r_left_expected);
    let c6 = cs_eq(cs_snd(cs_snd(r)), r_right_expected);
    lemma_eval_cs_and(c5, c6, x);
    lemma_eval_cs_and(c4, cs_and(c5, c6), x);
    lemma_eval_cs_and(c3, cs_and(c4, cs_and(c5, c6)), x);
    lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, cs_and(c5, c6))), x);
    lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, cs_and(c5, c6)))), x);
}

//  ============================================================
//  Universal instantiation: (∀x.φ) → φ[x/t]
//  ============================================================
proof fn universal_inst_tags(f: Formula, phi: Formula, var: nat, t: Term)
    requires f == mk_implies(mk_forall(var, phi), subst(phi, var, t)),
    ensures ({
        let x = encode(f);
        let left = cs_fst(cs_snd(CompSpec::Id));
        eval_comp(cs_fst(CompSpec::Id), x) == 5 &&
        eval_comp(cs_fst(left), x) == 7
    }),
{
    let x = encode(f);
    let left_enc = encode(mk_forall(var, phi));
    let right_enc = encode(subst(phi, var, t));
    lemma_encode_implies(mk_forall(var, phi), subst(phi, var, t));
    lemma_encode_forall(var, phi);
    lemma_eval_fst(CompSpec::Id, x);
    lemma_unpair1_pair(5nat, pair(left_enc, right_enc));
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(left_enc, right_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(left_enc, right_enc);
    let left = cs_fst(cs_snd(CompSpec::Id));
    lemma_eval_fst(left, x);
    lemma_unpair1_pair(7nat, pair(var, encode(phi)));
}

proof fn universal_inst_subst_check(f: Formula, phi: Formula, var: nat, t: Term)
    requires f == mk_implies(mk_forall(var, phi), subst(phi, var, t)),
    ensures ({
        let x = encode(f);
        let left = cs_fst(cs_snd(CompSpec::Id));
        let result = cs_snd(cs_snd(CompSpec::Id));
        let v_expr = cs_fst(cs_snd(left));
        let phi_inner = cs_snd(cs_snd(left));
        eval_comp(cs_comp(check_subst_comp(),
            cs_pair(phi_inner, cs_pair(result, v_expr))), x) != 0
    }),
{
    let x = encode(f);
    let left_enc = encode(mk_forall(var, phi));
    let right_enc = encode(subst(phi, var, t));
    lemma_encode_implies(mk_forall(var, phi), subst(phi, var, t));
    lemma_encode_forall(var, phi);
    let left = cs_fst(cs_snd(CompSpec::Id));
    let result = cs_snd(cs_snd(CompSpec::Id));
    //  phi_inner = snd(snd(left)) = snd(snd(fst(snd(Id))))
    //  Evaluates to: unpair2(unpair2(left_enc)) = unpair2(pair(var, encode(phi))) = encode(phi)
    lemma_eval_snd(CompSpec::Id, x);
    lemma_unpair2_pair(5nat, pair(left_enc, right_enc));
    lemma_eval_fst(cs_snd(CompSpec::Id), x);
    lemma_unpair1_pair(left_enc, right_enc);
    lemma_eval_snd(cs_snd(CompSpec::Id), x);
    lemma_unpair2_pair(left_enc, right_enc);
    lemma_eval_snd(left, x);
    lemma_unpair2_pair(7nat, pair(var, encode(phi)));
    lemma_eval_fst(cs_snd(left), x);
    lemma_unpair1_pair(var, encode(phi));
    lemma_eval_snd(cs_snd(left), x);
    lemma_unpair2_pair(var, encode(phi));
    let phi_inner = cs_snd(cs_snd(left));
    let v_expr = cs_fst(cs_snd(left));
    //  phi_inner evaluates to encode(phi), v_expr to var, result to right_enc
    lemma_eval_pair(result, v_expr, x);
    lemma_eval_pair(phi_inner, cs_pair(result, v_expr), x);
    lemma_eval_comp(check_subst_comp(), cs_pair(phi_inner, cs_pair(result, v_expr)), x);
    //  eval_comp(check_subst_comp(), pair(encode(phi), pair(encode(subst(phi,var,t)), var))) != 0
    crate::compspec_subst_helpers::lemma_check_subst_comp_backward(phi, var, t);
}

pub proof fn universal_inst_compose(f: Formula, phi: Formula, var: nat, t: Term)
    requires f == mk_implies(mk_forall(var, phi), subst(phi, var, t)),
    ensures eval_comp(check_axiom_universal_inst(), encode(f)) != 0,
{
    let x = encode(f);
    let left = cs_fst(cs_snd(CompSpec::Id));
    let result = cs_snd(cs_snd(CompSpec::Id));
    let v_expr = cs_fst(cs_snd(left));
    let phi_inner = cs_snd(cs_snd(left));

    universal_inst_tags(f, phi, var, t);
    universal_inst_subst_check(f, phi, var, t);

    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(left), cs_const(7));
    let subst_check = cs_comp(check_subst_comp(), cs_pair(phi_inner, cs_pair(result, v_expr)));

    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), x);
    lemma_eval_eq(cs_fst(left), cs_const(7), x);
    lemma_eval_cs_and(c2, subst_check, x);
    lemma_eval_cs_and(c1, cs_and(c2, subst_check), x);
}

} //  verus!
