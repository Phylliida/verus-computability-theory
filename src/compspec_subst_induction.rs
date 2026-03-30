use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_induction_steps::*;

verus! {

#[verifier::rlimit(500)]
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
    hide(encode);
    hide(subst);
    hide(formula_size);
    hide(compspec_iterate);
    assert(fuel > 0) by { reveal(formula_size); lemma_formula_size_pos(f); }
    reveal(encode);
    reveal(subst);
    reveal(formula_size);
    lemma_encode_is_pair(f);
    lemma_encode_is_pair(subst(f, var, t));
    lemma_subst_preserves_tag(f, var, t);
    match f {
        Formula::Eq { left, right } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_eq(f, left, right, var, t, rest, te, ts, pe, re, fuel);
            }
        },
        Formula::In { left, right } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_in(f, left, right, var, t, rest, te, ts, pe, re, fuel);
            }
        },
        Formula::Not { sub } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_not(f, *sub, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
            }
        },
        Formula::And { left, right } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_binary(f, *left, *right, 3, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
                lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
            }
        },
        Formula::Or { left, right } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_binary(f, *left, *right, 4, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
                lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
            }
        },
        Formula::Implies { left, right } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_binary(f, *left, *right, 5, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
                lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
            }
        },
        Formula::Iff { left, right } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                step_binary(f, *left, *right, 6, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
                lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
            }
        },
        Formula::Forall { var: v, sub } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                if v == var {
                    step_forall_bound(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                } else {
                    step_forall_free(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                    lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
                }
            }
        },
        Formula::Exists { var: v, sub } => {
            assert(compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
                pair(pe, pair(re, var)))
            == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
                pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var)))) by {
                reveal(compspec_iterate);
                if v == var {
                    step_exists_bound(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                } else {
                    step_exists_free(f, v, *sub, var, t, rest, te, ts, pe, re, fuel);
                    lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
                }
            }
        },
    }
}

} //  verus!
