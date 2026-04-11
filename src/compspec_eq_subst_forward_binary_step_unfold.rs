use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_forward_step2::lemma_eq_subst_forward_step_binary;
use crate::compspec_eq_subst_forward_walk::lemma_esb_valid_zero_stable;

verus! {

///  Step + unfold for And: from phi-level iterate, prove left+right level iterate.
#[verifier::rlimit(3000)]
pub proof fn lemma_eq_subst_binary_step_unfold(
    f1_enc: nat, f2_enc: nat, tag: nat,
    el: nat, er: nat,
    rest: nat, valid: nat, pe: nat, re: nat, x_enc: nat, y_enc: nat, fuel: nat,
)
    requires
        valid > 0,
        tag >= 3, tag <= 6,
        unpair1(f1_enc) == tag, unpair1(f2_enc) == tag,
        el == pair(unpair1(unpair2(f1_enc)), unpair1(unpair2(f2_enc))),
        er == pair(unpair2(unpair2(f1_enc)), unpair2(unpair2(f2_enc))),
        fuel >= 1,
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(f1_enc, f2_enc) + 1, rest), valid),
                pair(pe, pair(re, pair(x_enc, y_enc))))
        ) != 0,
    ensures
        unpair2(
            compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                pair(pair(el + 1, pair(er + 1, rest)), 1nat),
                pair(pe, pair(re, pair(x_enc, y_enc))))
        ) != 0,
{
    hide(compspec_iterate);
    let acc0 = pair(pair(pair(f1_enc, f2_enc) + 1, rest), valid);
    let s = pair(pe, pair(re, pair(x_enc, y_enc)));

    //  Step valid != 0
    assert(unpair2(eval_comp(check_eq_subst_step(),
        pair((fuel - 1) as nat, pair(acc0, s)))) != 0) by {
        reveal(compspec_iterate);
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
        let sr = eval_comp(check_eq_subst_step(), pair((fuel - 1) as nat, pair(acc0, s)));
        if unpair2(sr) == 0 {
            lemma_pair_surjective(sr);
            lemma_esb_valid_zero_stable((fuel - 1) as nat, unpair1(sr), s);
            lemma_unpair2_pair(unpair1(sr), 0nat);
        }
    };

    //  Use the binary step helper to compute step result
    lemma_eq_subst_forward_step_binary(f1_enc, f2_enc, tag,
        rest, valid, (fuel - 1) as nat, pe, re, x_enc, y_enc);

    //  Unfold iterate
    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
        pair(pair(el + 1, pair(er + 1, rest)), 1nat), s)) != 0) by {
        reveal(compspec_iterate);
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
    };
}

} // verus!
