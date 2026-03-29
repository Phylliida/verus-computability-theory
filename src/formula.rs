use vstd::prelude::*;
use crate::pairing::*;

verus! {

///  A first-order term. For ZFC, we only need variables.
pub enum Term {
    Var { index: nat },
}

///  A first-order formula in the language of set theory (=, ∈).
pub enum Formula {
    Eq { left: Term, right: Term },
    In { left: Term, right: Term },
    Not { sub: Box<Formula> },
    And { left: Box<Formula>, right: Box<Formula> },
    Or { left: Box<Formula>, right: Box<Formula> },
    Implies { left: Box<Formula>, right: Box<Formula> },
    Iff { left: Box<Formula>, right: Box<Formula> },
    Forall { var: nat, sub: Box<Formula> },
    Exists { var: nat, sub: Box<Formula> },
}

//  ============================================================
//  Structural size
//  ============================================================

///  Structural size of a term.
pub open spec fn term_size(t: Term) -> nat {
    match t {
        Term::Var { .. } => 1,
    }
}

///  Structural size of a formula.
pub open spec fn formula_size(f: Formula) -> nat
    decreases f,
{
    match f {
        Formula::Eq { .. } => 1,
        Formula::In { .. } => 1,
        Formula::Not { sub } => 1 + formula_size(*sub),
        Formula::And { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Or { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Implies { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Iff { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Forall { var, sub } => 1 + formula_size(*sub),
        Formula::Exists { var, sub } => 1 + formula_size(*sub),
    }
}

///  Formula size is always positive.
pub proof fn lemma_formula_size_pos(f: Formula)
    ensures
        formula_size(f) >= 1,
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_formula_size_pos(*sub); },
        Formula::And { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Or { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Implies { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Iff { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Forall { var, sub } => { lemma_formula_size_pos(*sub); },
        Formula::Exists { var, sub } => { lemma_formula_size_pos(*sub); },
    }
}

//  ============================================================
//  Free variables
//  ============================================================

///  Free variables of a term.
pub open spec fn term_free_vars(t: Term) -> Set<nat> {
    match t {
        Term::Var { index } => set![index],
    }
}

///  Free variables of a formula.
pub open spec fn free_vars(f: Formula) -> Set<nat>
    decreases f,
{
    match f {
        Formula::Eq { left, right } => term_free_vars(left).union(term_free_vars(right)),
        Formula::In { left, right } => term_free_vars(left).union(term_free_vars(right)),
        Formula::Not { sub } => free_vars(*sub),
        Formula::And { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Or { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Implies { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Iff { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Forall { var, sub } => free_vars(*sub).remove(var),
        Formula::Exists { var, sub } => free_vars(*sub).remove(var),
    }
}

///  A formula is a sentence if it has no free variables.
pub open spec fn is_sentence(f: Formula) -> bool {
    free_vars(f) =~= Set::empty()
}

//  ============================================================
//  Substitution
//  ============================================================

///  Substitute term t for variable var in a term.
pub open spec fn subst_term(term: Term, var: nat, t: Term) -> Term {
    match term {
        Term::Var { index } => if index == var { t } else { term },
    }
}

///  Substitute term t for variable var in a formula (naive, no capture avoidance).
pub open spec fn subst(f: Formula, var: nat, t: Term) -> Formula
    decreases f,
{
    match f {
        Formula::Eq { left, right } =>
            Formula::Eq { left: subst_term(left, var, t), right: subst_term(right, var, t) },
        Formula::In { left, right } =>
            Formula::In { left: subst_term(left, var, t), right: subst_term(right, var, t) },
        Formula::Not { sub } =>
            Formula::Not { sub: Box::new(subst(*sub, var, t)) },
        Formula::And { left, right } =>
            Formula::And { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Or { left, right } =>
            Formula::Or { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Implies { left, right } =>
            Formula::Implies { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Iff { left, right } =>
            Formula::Iff { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Forall { var: v, sub } =>
            if v == var { f } else { Formula::Forall { var: v, sub: Box::new(subst(*sub, var, t)) } },
        Formula::Exists { var: v, sub } =>
            if v == var { f } else { Formula::Exists { var: v, sub: Box::new(subst(*sub, var, t)) } },
    }
}

//  ============================================================
//  Helper constructors
//  ============================================================

pub open spec fn mk_var(i: nat) -> Term {
    Term::Var { index: i }
}

pub open spec fn mk_eq(left: Term, right: Term) -> Formula {
    Formula::Eq { left, right }
}

pub open spec fn mk_in(left: Term, right: Term) -> Formula {
    Formula::In { left, right }
}

pub open spec fn mk_not(f: Formula) -> Formula {
    Formula::Not { sub: Box::new(f) }
}

pub open spec fn mk_and(left: Formula, right: Formula) -> Formula {
    Formula::And { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_or(left: Formula, right: Formula) -> Formula {
    Formula::Or { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_implies(left: Formula, right: Formula) -> Formula {
    Formula::Implies { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_iff(left: Formula, right: Formula) -> Formula {
    Formula::Iff { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_forall(var: nat, sub: Formula) -> Formula {
    Formula::Forall { var, sub: Box::new(sub) }
}

pub open spec fn mk_exists(var: nat, sub: Formula) -> Formula {
    Formula::Exists { var, sub: Box::new(sub) }
}

//  ============================================================
//  Gödel encoding
//  ============================================================

///  Encode a term as a natural number.
pub open spec fn encode_term(t: Term) -> nat {
    match t {
        Term::Var { index } => index,
    }
}

///  Encode a formula as a natural number using Cantor pairing.
///  Tags: 0=Eq, 1=In, 2=Not, 3=And, 4=Or, 5=Implies, 6=Iff, 7=Forall, 8=Exists
pub open spec fn encode(f: Formula) -> nat
    decreases f,
{
    match f {
        Formula::Eq { left, right } =>
            pair(0, pair(encode_term(left), encode_term(right))),
        Formula::In { left, right } =>
            pair(1, pair(encode_term(left), encode_term(right))),
        Formula::Not { sub } =>
            pair(2, encode(*sub)),
        Formula::And { left, right } =>
            pair(3, pair(encode(*left), encode(*right))),
        Formula::Or { left, right } =>
            pair(4, pair(encode(*left), encode(*right))),
        Formula::Implies { left, right } =>
            pair(5, pair(encode(*left), encode(*right))),
        Formula::Iff { left, right } =>
            pair(6, pair(encode(*left), encode(*right))),
        Formula::Forall { var, sub } =>
            pair(7, pair(var, encode(*sub))),
        Formula::Exists { var, sub } =>
            pair(8, pair(var, encode(*sub))),
    }
}

///  Gödel encoding is injective.
pub proof fn lemma_encode_injective(f1: Formula, f2: Formula)
    requires
        encode(f1) == encode(f2),
    ensures
        f1 == f2,
    decreases f1,
{
    //  Different tags => different first component of outer pair => contradiction
    //  Same tag => inner pair equal => recursive injectivity
    match f1 {
        Formula::Eq { left: l1, right: r1 } => {
            //  encode(f1) = pair(0, pair(encode_term(l1), encode_term(r1)))
            //  f2 must also have tag 0
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Eq { left: l2, right: r2 } => {
                    lemma_pair_injective(0, pair(encode_term(l1), encode_term(r1)),
                                         0, pair(encode_term(l2), encode_term(r2)));
                    lemma_pair_injective(encode_term(l1), encode_term(r1),
                                         encode_term(l2), encode_term(r2));
                },
                _ => {},
            }
        },
        Formula::In { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::In { left: l2, right: r2 } => {
                    lemma_pair_injective(1, pair(encode_term(l1), encode_term(r1)),
                                         1, pair(encode_term(l2), encode_term(r2)));
                    lemma_pair_injective(encode_term(l1), encode_term(r1),
                                         encode_term(l2), encode_term(r2));
                },
                _ => {},
            }
        },
        Formula::Not { sub: s1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Not { sub: s2 } => {
                    lemma_pair_injective(2, encode(*s1), 2, encode(*s2));
                    lemma_encode_injective(*s1, *s2);
                },
                _ => {},
            }
        },
        Formula::And { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::And { left: l2, right: r2 } => {
                    lemma_pair_injective(3, pair(encode(*l1), encode(*r1)),
                                         3, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Or { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Or { left: l2, right: r2 } => {
                    lemma_pair_injective(4, pair(encode(*l1), encode(*r1)),
                                         4, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Implies { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Implies { left: l2, right: r2 } => {
                    lemma_pair_injective(5, pair(encode(*l1), encode(*r1)),
                                         5, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Iff { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Iff { left: l2, right: r2 } => {
                    lemma_pair_injective(6, pair(encode(*l1), encode(*r1)),
                                         6, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Forall { var: v1, sub: s1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Forall { var: v2, sub: s2 } => {
                    lemma_pair_injective(7, pair(v1, encode(*s1)),
                                         7, pair(v2, encode(*s2)));
                    lemma_pair_injective(v1, encode(*s1), v2, encode(*s2));
                    lemma_encode_injective(*s1, *s2);
                },
                _ => {},
            }
        },
        Formula::Exists { var: v1, sub: s1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Exists { var: v2, sub: s2 } => {
                    lemma_pair_injective(8, pair(v1, encode(*s1)),
                                         8, pair(v2, encode(*s2)));
                    lemma_pair_injective(v1, encode(*s1), v2, encode(*s2));
                    lemma_encode_injective(*s1, *s2);
                },
                _ => {},
            }
        },
    }
}

///  Helper: the tag (first component of pair) determines the formula variant.
///  If encode(f1) == encode(f2), they must have the same tag.
proof fn lemma_tag_determines_variant(f1: Formula, f2: Formula)
    requires
        encode(f1) == encode(f2),
    ensures
        formula_tag(f1) == formula_tag(f2),
{
    let t1 = formula_tag(f1);
    let c1 = formula_content(f1);
    let t2 = formula_tag(f2);
    let c2 = formula_content(f2);
    //  encode(f1) = pair(t1, c1) = pair(t2, c2) = encode(f2)
    assert(pair(t1, c1) == pair(t2, c2));
    lemma_pair_injective(t1, c1, t2, c2);
}

///  Extract the tag from a formula (matches encoding tag assignment).
pub open spec fn formula_tag(f: Formula) -> nat {
    match f {
        Formula::Eq { .. } => 0,
        Formula::In { .. } => 1,
        Formula::Not { .. } => 2,
        Formula::And { .. } => 3,
        Formula::Or { .. } => 4,
        Formula::Implies { .. } => 5,
        Formula::Iff { .. } => 6,
        Formula::Forall { .. } => 7,
        Formula::Exists { .. } => 8,
    }
}

///  Extract the content (second component of pair) from a formula encoding.
pub open spec fn formula_content(f: Formula) -> nat
    decreases f,
{
    match f {
        Formula::Eq { left, right } => pair(encode_term(left), encode_term(right)),
        Formula::In { left, right } => pair(encode_term(left), encode_term(right)),
        Formula::Not { sub } => encode(*sub),
        Formula::And { left, right } => pair(encode(*left), encode(*right)),
        Formula::Or { left, right } => pair(encode(*left), encode(*right)),
        Formula::Implies { left, right } => pair(encode(*left), encode(*right)),
        Formula::Iff { left, right } => pair(encode(*left), encode(*right)),
        Formula::Forall { var, sub } => pair(var, encode(*sub)),
        Formula::Exists { var, sub } => pair(var, encode(*sub)),
    }
}

///  encode(f) == pair(formula_tag(f), formula_content(f)).
proof fn lemma_encode_is_pair(f: Formula)
    ensures
        encode(f) == pair(formula_tag(f), formula_content(f)),
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { .. } => {},
        Formula::And { .. } => {},
        Formula::Or { .. } => {},
        Formula::Implies { .. } => {},
        Formula::Iff { .. } => {},
        Formula::Forall { .. } => {},
        Formula::Exists { .. } => {},
    }
}

} //  verus!
