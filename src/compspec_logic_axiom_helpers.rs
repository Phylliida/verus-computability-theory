use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_free_var_induction::*;
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

pub proof fn eq_refl_compose(f: Formula, t: Term)
    requires f == mk_eq(t, t),
    ensures eval_comp(check_axiom_eq_refl(), encode(f)) != 0,
{
    let x = encode(f);
    eq_refl_evals(t);
    lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(0), x);
    lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), x);
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
pub proof fn eq_subst_left_inner(f: Formula, xt: Term, yt: Term, sl: Formula, sr: Formula)
    requires f == mk_implies(mk_eq(xt, yt), mk_implies(sl, sr)),
    ensures eval_comp(check_axiom_eq_subst_left(), encode(f)) != 0,
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

} //  verus!
