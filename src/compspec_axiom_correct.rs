use vstd::prelude::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_logic_axiom_helpers::*;
use crate::proof_system::*;

verus! {

pub proof fn lemma_check_axiom_identity_correct(f: Formula)
    requires is_axiom_identity(f),
    ensures eval_comp(check_axiom_identity(), encode(f)) != 0,
{
    let phi: Formula = choose|phi: Formula| f == mk_implies(phi, phi);
    identity_compose(f, phi);
}

pub proof fn lemma_check_axiom_eq_refl_correct(f: Formula)
    requires is_axiom_eq_refl(f),
    ensures eval_comp(check_axiom_eq_refl(), encode(f)) != 0,
{
    let t: Term = choose|t: Term| f == mk_eq(t, t);
    eq_refl_compose(f, t);
}

pub proof fn lemma_check_axiom_iff_elim_left_correct(f: Formula)
    requires is_axiom_iff_elim_left(f),
    ensures eval_comp(check_axiom_iff_elim_left(), encode(f)) != 0,
{
    //  is_axiom_iff_elim_left(f) means f = Implies(Iff(phi, psi), Implies(phi, psi))
    //  Extract via match:
    match f {
        Formula::Implies { left, right } => {
            match *left {
                Formula::Iff { left: phi_b, right: psi_b } => {
                    iff_elim_left_compose(f, *phi_b, *psi_b);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_iff_elim_right_correct(f: Formula)
    requires is_axiom_iff_elim_right(f),
    ensures eval_comp(check_axiom_iff_elim_right(), encode(f)) != 0,
{
    match f {
        Formula::Implies { left, right } => {
            match *left {
                Formula::Iff { left: phi_b, right: psi_b } => {
                    iff_elim_right_compose(f, *phi_b, *psi_b);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_eq_subst_left_correct(f: Formula)
    requires is_axiom_eq_subst_left(f),
    ensures eval_comp(check_axiom_eq_subst_left(), encode(f)) != 0,
{
    match f {
        Formula::Implies { left, right } => {
            match (*left, *right) {
                (Formula::Eq { left: xt, right: yt }, Formula::Implies { left: s1, right: s2 }) => {
                    //  Prove eq_subst_compatible from the existential witnesses
                    assert(eq_subst_compatible(*s1, *s2, xt, yt)) by {
                        assert forall|phi: Formula, var: nat|
                            *s1 == subst(phi, var, xt) && *s2 == #[trigger] subst(phi, var, yt)
                            implies eq_subst_compatible(*s1, *s2, xt, yt)
                        by {
                            lemma_subst_eq_subst_compatible(phi, var, xt, yt);
                        }
                    };
                    eq_subst_left_inner(f, xt, yt, *s1, *s2);
                },
                (_, _) => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_eq_subst_right_correct(f: Formula)
    requires is_axiom_eq_subst_right(f),
    ensures eval_comp(check_axiom_eq_subst_right(), encode(f)) != 0,
{
    match f {
        Formula::Implies { left, right } => {
            match (*left, *right) {
                (Formula::Eq { left: xt, right: yt }, Formula::Implies { left: s1, right: s2 }) => {
                    //  Right axiom: s1 = subst(phi, var, yt), s2 = subst(phi, var, xt)
                    //  Compatible with swap pair (yt, xt)
                    assert(eq_subst_compatible(*s1, *s2, yt, xt)) by {
                        assert forall|phi: Formula, var: nat|
                            *s1 == subst(phi, var, yt) && *s2 == #[trigger] subst(phi, var, xt)
                            implies eq_subst_compatible(*s1, *s2, yt, xt)
                        by {
                            lemma_subst_eq_subst_compatible(phi, var, yt, xt);
                        }
                    };
                    eq_subst_right_inner(f, xt, yt, *s1, *s2);
                },
                (_, _) => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_vacuous_quant_correct(f: Formula)
    requires is_axiom_vacuous_quant(f),
    ensures eval_comp(check_axiom_vacuous_quant(), encode(f)) != 0,
{
    //  f = Implies(phi, Forall(var, phi)) where !has_free_var(phi, var)
    match f {
        Formula::Implies { left, right } => {
            match *right {
                Formula::Forall { var, sub } => {
                    vacuous_quant_compose(f, *left, var);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_iff_intro_correct(f: Formula)
    requires is_axiom_iff_intro(f),
    ensures eval_comp(check_axiom_iff_intro(), encode(f)) != 0,
{
    match f {
        Formula::Implies { left, right } => {
            match *left {
                Formula::Implies { left: phi_b, right: psi_b } => {
                    iff_intro_compose(f, *phi_b, *psi_b);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_hyp_syllogism_correct(f: Formula)
    requires is_axiom_hyp_syllogism(f),
    ensures eval_comp(check_axiom_hyp_syllogism(), encode(f)) != 0,
{
    match f {
        Formula::Implies { left, right } => {
            match (*left, *right) {
                (Formula::Implies { left: phi_b, right: psi_b },
                 Formula::Implies { left: m_b, right: n_b }) => {
                    match *m_b {
                        Formula::Implies { left: psi2_b, right: chi_b } => {
                            hyp_syl_compose(f, *phi_b, *psi_b, *chi_b);
                        },
                        _ => {},
                    }
                },
                (_, _) => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_quantifier_dist_correct(f: Formula)
    requires is_axiom_quantifier_dist(f),
    ensures eval_comp(check_axiom_quantifier_dist(), encode(f)) != 0,
{
    match f {
        Formula::Implies { left, right } => {
            match *left {
                Formula::Forall { var, sub } => {
                    match *sub {
                        Formula::Implies { left: phi_b, right: psi_b } => {
                            quant_dist_compose(f, *phi_b, *psi_b, var);
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_check_axiom_universal_inst_correct(f: Formula)
    requires is_axiom_universal_inst(f),
    ensures eval_comp(check_axiom_universal_inst(), encode(f)) != 0,
{
    //  is_axiom_universal_inst: exists|phi, var, t| f == mk_implies(mk_forall(var, phi), subst(phi, var, t))
    match f {
        Formula::Implies { left, right } => {
            match *left {
                Formula::Forall { var: v, sub } => {
                    //  phi = *sub, var = v, t is implicit (subst(phi, v, t) = *right)
                    //  Need: f == mk_implies(mk_forall(v, *sub), subst(*sub, v, t)) for some t
                    //  From is_axiom_universal_inst, we know such t exists
                    //  And *right == subst(*sub, v, t)
                    //  Call the compose helper
                    //  From is_axiom_universal_inst: exists t such that *right == subst(*sub, v, t)
                    let t_wit: Term = choose|t_wit: Term|
                        f == mk_implies(mk_forall(v, *sub), subst(*sub, v, t_wit));
                    universal_inst_compose(f, *sub, v, t_wit);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

} //  verus!
