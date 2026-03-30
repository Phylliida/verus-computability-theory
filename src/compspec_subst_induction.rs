use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_induction_steps::*;

verus! {

#[verifier::rlimit(200)]
pub proof fn lemma_subst_traversal(
    f: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat,
)
    requires fuel >= formula_size(f),
    ensures compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
            pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var))),
    decreases f,
{
    assert(fuel > 0) by { lemma_formula_size_pos(f); }
    match f {
        Formula::Eq { left, right } => {
            step_eq(f, left, right, var, t, rest, te, ts, pe, re, fuel);
        },
        Formula::In { left, right } => {
            step_in(f, left, right, var, t, rest, te, ts, pe, re, fuel);
        },
        Formula::Not { sub } => {
            step_not(f, *sub, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
        },
        Formula::And { left, right } => {
            step_binary(f, *left, *right, 3, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Or { left, right } => {
            step_binary(f, *left, *right, 4, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Implies { left, right } => {
            step_binary(f, *left, *right, 5, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Iff { left, right } => {
            step_binary(f, *left, *right, 6, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Forall { var: v, sub } => {
            if v == var {
                step_forall_bound(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
            } else {
                step_forall_free(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
            }
        },
        Formula::Exists { var: v, sub } => {
            if v == var {
                step_exists_bound(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
            } else {
                step_exists_free(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
            }
        },
    }
}

} //  verus!
