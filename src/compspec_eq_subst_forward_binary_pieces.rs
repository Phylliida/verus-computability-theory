use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;

verus! {

///  Backward consume helper: from left+right iterate, derive right-only iterate.
///  Wraps lemma_eq_subst_walk (backward) so the joiner can call it without
///  introducing the backward walk's full signature complexity.
#[verifier::rlimit(2000)]
pub proof fn lemma_eq_subst_binary_consume_left(
    l1: Formula, l2: Formula, x_enc: nat, y_enc: nat,
    er_plus1_rest: nat, valid: nat, pe: nat, re: nat, fuel_minus1: nat,
)
    requires
        valid != 0,
        eq_subst_compatible(l1, l2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
        fuel_minus1 >= formula_size(l1),
    ensures
        exists|v: nat| v != 0 &&
            compspec_iterate(check_eq_subst_step(), fuel_minus1,
                pair(pair(pair(encode(l1), encode(l2)) + 1, er_plus1_rest), valid),
                pair(pe, pair(re, pair(x_enc, y_enc))))
            == compspec_iterate(check_eq_subst_step(),
                (fuel_minus1 - formula_size(l1)) as nat,
                pair(er_plus1_rest, v),
                pair(pe, pair(re, pair(x_enc, y_enc)))),
{
    crate::compspec_eq_subst_backward::lemma_eq_subst_walk(
        l1, l2,
        Term::Var { index: x_enc }, Term::Var { index: y_enc },
        er_plus1_rest, valid, fuel_minus1, pe, re);
}

} // verus!
