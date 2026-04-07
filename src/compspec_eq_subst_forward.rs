use vstd::prelude::*;
use crate::formula::*;

verus! {

///  Maximum variable index in all terms of a formula.
///  Used to pick a fresh variable for eq_subst forward proofs.
pub open spec fn max_var(f: Formula) -> nat
    decreases f,
{
    match f {
        Formula::Eq { left: Term::Var { index: a }, right: Term::Var { index: b } } =>
            if a >= b { a } else { b },
        Formula::In { left: Term::Var { index: a }, right: Term::Var { index: b } } =>
            if a >= b { a } else { b },
        Formula::Not { sub } => max_var(*sub),
        Formula::And { left, right } => {
            let ml = max_var(*left); let mr = max_var(*right);
            if ml >= mr { ml } else { mr }
        },
        Formula::Or { left, right } => {
            let ml = max_var(*left); let mr = max_var(*right);
            if ml >= mr { ml } else { mr }
        },
        Formula::Implies { left, right } => {
            let ml = max_var(*left); let mr = max_var(*right);
            if ml >= mr { ml } else { mr }
        },
        Formula::Iff { left, right } => {
            let ml = max_var(*left); let mr = max_var(*right);
            if ml >= mr { ml } else { mr }
        },
        Formula::Forall { var: v, sub } => {
            let ms = max_var(*sub);
            if v >= ms { v } else { ms }
        },
        Formula::Exists { var: v, sub } => {
            let ms = max_var(*sub);
            if v >= ms { v } else { ms }
        },
    }
}

///  A fresh variable substitution is the identity.
pub proof fn lemma_subst_fresh_identity(f: Formula, var_fresh: nat, t: Term)
    requires var_fresh > max_var(f),
    ensures subst(f, var_fresh, t) == f,
    decreases f,
{
    match f {
        Formula::Eq { left: Term::Var { index: a }, right: Term::Var { index: b } } => {},
        Formula::In { left: Term::Var { index: a }, right: Term::Var { index: b } } => {},
        Formula::Not { sub } => {
            lemma_subst_fresh_identity(*sub, var_fresh, t);
        },
        Formula::And { left, right } => {
            lemma_subst_fresh_identity(*left, var_fresh, t);
            lemma_subst_fresh_identity(*right, var_fresh, t);
        },
        Formula::Or { left, right } => {
            lemma_subst_fresh_identity(*left, var_fresh, t);
            lemma_subst_fresh_identity(*right, var_fresh, t);
        },
        Formula::Implies { left, right } => {
            lemma_subst_fresh_identity(*left, var_fresh, t);
            lemma_subst_fresh_identity(*right, var_fresh, t);
        },
        Formula::Iff { left, right } => {
            lemma_subst_fresh_identity(*left, var_fresh, t);
            lemma_subst_fresh_identity(*right, var_fresh, t);
        },
        Formula::Forall { var: v, sub } => {
            if v != var_fresh {
                lemma_subst_fresh_identity(*sub, var_fresh, t);
            }
        },
        Formula::Exists { var: v, sub } => {
            if v != var_fresh {
                lemma_subst_fresh_identity(*sub, var_fresh, t);
            }
        },
    }
}

///  Construct phi from two eq_subst_compatible formulas: replace swap positions with Var(var_fresh).
pub open spec fn extract_phi(f1: Formula, f2: Formula, x: Term, y: Term, var_fresh: nat) -> Formula
    decreases f1,
{
    match f1 {
        Formula::Eq { left: l1, right: r1 } => match f2 {
            Formula::Eq { left: l2, right: r2 } => Formula::Eq {
                left: if l1 == x && l2 == y { Term::Var { index: var_fresh } } else { l1 },
                right: if r1 == x && r2 == y { Term::Var { index: var_fresh } } else { r1 },
            },
            _ => f1,
        },
        Formula::In { left: l1, right: r1 } => match f2 {
            Formula::In { left: l2, right: r2 } => Formula::In {
                left: if l1 == x && l2 == y { Term::Var { index: var_fresh } } else { l1 },
                right: if r1 == x && r2 == y { Term::Var { index: var_fresh } } else { r1 },
            },
            _ => f1,
        },
        Formula::Not { sub: s1 } => match f2 {
            Formula::Not { sub: s2 } => Formula::Not {
                sub: Box::new(extract_phi(*s1, *s2, x, y, var_fresh)),
            },
            _ => f1,
        },
        Formula::And { left: l1, right: r1 } => match f2 {
            Formula::And { left: l2, right: r2 } => Formula::And {
                left: Box::new(extract_phi(*l1, *l2, x, y, var_fresh)),
                right: Box::new(extract_phi(*r1, *r2, x, y, var_fresh)),
            },
            _ => f1,
        },
        Formula::Or { left: l1, right: r1 } => match f2 {
            Formula::Or { left: l2, right: r2 } => Formula::Or {
                left: Box::new(extract_phi(*l1, *l2, x, y, var_fresh)),
                right: Box::new(extract_phi(*r1, *r2, x, y, var_fresh)),
            },
            _ => f1,
        },
        Formula::Implies { left: l1, right: r1 } => match f2 {
            Formula::Implies { left: l2, right: r2 } => Formula::Implies {
                left: Box::new(extract_phi(*l1, *l2, x, y, var_fresh)),
                right: Box::new(extract_phi(*r1, *r2, x, y, var_fresh)),
            },
            _ => f1,
        },
        Formula::Iff { left: l1, right: r1 } => match f2 {
            Formula::Iff { left: l2, right: r2 } => Formula::Iff {
                left: Box::new(extract_phi(*l1, *l2, x, y, var_fresh)),
                right: Box::new(extract_phi(*r1, *r2, x, y, var_fresh)),
            },
            _ => f1,
        },
        Formula::Forall { var: v1, sub: s1 } => match f2 {
            Formula::Forall { var: v2, sub: s2 } => Formula::Forall {
                var: v1,
                sub: Box::new(extract_phi(*s1, *s2, x, y, var_fresh)),
            },
            _ => f1,
        },
        Formula::Exists { var: v1, sub: s1 } => match f2 {
            Formula::Exists { var: v2, sub: s2 } => Formula::Exists {
                var: v1,
                sub: Box::new(extract_phi(*s1, *s2, x, y, var_fresh)),
            },
            _ => f1,
        },
    }
}

///  subst(extract_phi(f1, f2, x, y, var_fresh), var_fresh, x) == f1
///  when eq_subst_compatible and var_fresh is fresh.
pub proof fn lemma_extract_phi_subst_left(
    f1: Formula, f2: Formula, x: Term, y: Term, var_fresh: nat,
)
    requires
        eq_subst_compatible(f1, f2, x, y),
        var_fresh > max_var(f1),
        var_fresh > max_var(f2),
    ensures
        subst(extract_phi(f1, f2, x, y, var_fresh), var_fresh, x) == f1,
    decreases f1,
{
    let phi = extract_phi(f1, f2, x, y, var_fresh);
    match f1 {
        Formula::Eq { left: Term::Var { index: a1 }, right: Term::Var { index: b1 } } => {
            match f2 {
                Formula::Eq { left: Term::Var { index: a2 }, right: Term::Var { index: b2 } } => {
                    //  Term 1: swapped (a1==x.index, a2==y.index) → Var(var_fresh), subst gives x=Var(a1)
                    //  Or same (a1==a2) → Var(a1), subst_term(Var(a1), var_fresh, x) = Var(a1) since a1 < var_fresh
                },
                _ => {},
            }
        },
        Formula::In { left: Term::Var { index: a1 }, right: Term::Var { index: b1 } } => {
            match f2 {
                Formula::In { left: Term::Var { index: a2 }, right: Term::Var { index: b2 } } => {},
                _ => {},
            }
        },
        Formula::Not { sub: s1 } => {
            match f2 {
                Formula::Not { sub: s2 } => {
                    lemma_extract_phi_subst_left(*s1, *s2, x, y, var_fresh);
                },
                _ => {},
            }
        },
        Formula::And { left: l1, right: r1 } => {
            match f2 {
                Formula::And { left: l2, right: r2 } => {
                    lemma_extract_phi_subst_left(*l1, *l2, x, y, var_fresh);
                    lemma_extract_phi_subst_left(*r1, *r2, x, y, var_fresh);
                },
                _ => {},
            }
        },
        Formula::Or { left: l1, right: r1 } => {
            match f2 {
                Formula::Or { left: l2, right: r2 } => {
                    lemma_extract_phi_subst_left(*l1, *l2, x, y, var_fresh);
                    lemma_extract_phi_subst_left(*r1, *r2, x, y, var_fresh);
                },
                _ => {},
            }
        },
        Formula::Implies { left: l1, right: r1 } => {
            match f2 {
                Formula::Implies { left: l2, right: r2 } => {
                    lemma_extract_phi_subst_left(*l1, *l2, x, y, var_fresh);
                    lemma_extract_phi_subst_left(*r1, *r2, x, y, var_fresh);
                },
                _ => {},
            }
        },
        Formula::Iff { left: l1, right: r1 } => {
            match f2 {
                Formula::Iff { left: l2, right: r2 } => {
                    lemma_extract_phi_subst_left(*l1, *l2, x, y, var_fresh);
                    lemma_extract_phi_subst_left(*r1, *r2, x, y, var_fresh);
                },
                _ => {},
            }
        },
        Formula::Forall { var: v1, sub: s1 } => {
            match f2 {
                Formula::Forall { var: v2, sub: s2 } => {
                    //  v1 == v2 from eq_subst_compatible
                    //  v1 <= max_var(f1) < var_fresh, so v1 != var_fresh → subst recurses
                    lemma_extract_phi_subst_left(*s1, *s2, x, y, var_fresh);
                },
                _ => {},
            }
        },
        Formula::Exists { var: v1, sub: s1 } => {
            match f2 {
                Formula::Exists { var: v2, sub: s2 } => {
                    lemma_extract_phi_subst_left(*s1, *s2, x, y, var_fresh);
                },
                _ => {},
            }
        },
    }
}

///  subst(extract_phi(f1, f2, x, y, var_fresh), var_fresh, y) == f2
pub proof fn lemma_extract_phi_subst_right(
    f1: Formula, f2: Formula, x: Term, y: Term, var_fresh: nat,
)
    requires
        eq_subst_compatible(f1, f2, x, y),
        var_fresh > max_var(f1),
        var_fresh > max_var(f2),
    ensures
        subst(extract_phi(f1, f2, x, y, var_fresh), var_fresh, y) == f2,
    decreases f1,
{
    match f1 {
        Formula::Eq { left: Term::Var { index: a1 }, right: Term::Var { index: b1 } } => {
            match f2 {
                Formula::Eq { left: Term::Var { index: a2 }, right: Term::Var { index: b2 } } => {
                    //  swapped: phi_term = Var(var_fresh), subst gives y = Var(a2) ✓
                    //  same: phi_term = Var(a1), subst identity (a1 < var_fresh), and a1 == a2 ✓
                },
                _ => {},
            }
        },
        Formula::In { left: Term::Var { index: a1 }, right: Term::Var { index: b1 } } => {
            match f2 {
                Formula::In { left: Term::Var { index: a2 }, right: Term::Var { index: b2 } } => {},
                _ => {},
            }
        },
        Formula::Not { sub: s1 } => {
            match f2 { Formula::Not { sub: s2 } => {
                lemma_extract_phi_subst_right(*s1, *s2, x, y, var_fresh);
            }, _ => {} }
        },
        Formula::And { left: l1, right: r1 } => {
            match f2 { Formula::And { left: l2, right: r2 } => {
                lemma_extract_phi_subst_right(*l1, *l2, x, y, var_fresh);
                lemma_extract_phi_subst_right(*r1, *r2, x, y, var_fresh);
            }, _ => {} }
        },
        Formula::Or { left: l1, right: r1 } => {
            match f2 { Formula::Or { left: l2, right: r2 } => {
                lemma_extract_phi_subst_right(*l1, *l2, x, y, var_fresh);
                lemma_extract_phi_subst_right(*r1, *r2, x, y, var_fresh);
            }, _ => {} }
        },
        Formula::Implies { left: l1, right: r1 } => {
            match f2 { Formula::Implies { left: l2, right: r2 } => {
                lemma_extract_phi_subst_right(*l1, *l2, x, y, var_fresh);
                lemma_extract_phi_subst_right(*r1, *r2, x, y, var_fresh);
            }, _ => {} }
        },
        Formula::Iff { left: l1, right: r1 } => {
            match f2 { Formula::Iff { left: l2, right: r2 } => {
                lemma_extract_phi_subst_right(*l1, *l2, x, y, var_fresh);
                lemma_extract_phi_subst_right(*r1, *r2, x, y, var_fresh);
            }, _ => {} }
        },
        Formula::Forall { var: v1, sub: s1 } => {
            match f2 { Formula::Forall { var: v2, sub: s2 } => {
                lemma_extract_phi_subst_right(*s1, *s2, x, y, var_fresh);
            }, _ => {} }
        },
        Formula::Exists { var: v1, sub: s1 } => {
            match f2 { Formula::Exists { var: v2, sub: s2 } => {
                lemma_extract_phi_subst_right(*s1, *s2, x, y, var_fresh);
            }, _ => {} }
        },
    }
}

} // verus!
