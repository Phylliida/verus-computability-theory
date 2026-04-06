use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_forward_step_binary::lemma_forward_step_binary;
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;
use crate::compspec_subst_forward_walk_binary_right::lemma_forward_binary_right_and_combine;

verus! {

///  Binary walk: step + tag match + left IH + delegate to right helper.
///  Precondition: the iterate AFTER the step gives valid != 0.
///  The caller (walk_iter) establishes this via step + iterate_unfold.
#[verifier::rlimit(3000)]
pub proof fn lemma_forward_walk_binary(
    phi: Formula, left: Formula, right: Formula,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
) -> (t: Term)
    requires
        phi matches Formula::And{..} || phi matches Formula::Or{..}
            || phi matches Formula::Implies{..} || phi matches Formula::Iff{..},
        encode(phi) == pair(formula_tag(phi), pair(encode(left), encode(right))),
        fuel >= 1,
        fuel - 1 >= subst_traversal_cost(left, var) + subst_traversal_cost(right, var),
        //  Precondition: iterate AFTER the binary step gives valid != 0
        //  (caller establishes via step helper + iterate_unfold)
        ({
            let tag = formula_tag(phi);
            let tag_eq: nat = if unpair1(result_enc) == tag { 1nat } else { 0nat };
            let phi_c = unpair2(encode(phi));
            let result_c = unpair2(result_enc);
            let entry_l = pair(unpair1(phi_c), unpair1(result_c));
            let entry_r = pair(unpair2(phi_c), unpair2(result_c));
            let new_stack = pair(entry_l + 1, pair(entry_r + 1, rest));
            unpair1(unpair2(
                compspec_iterate(check_subst_step(), (fuel - 1) as nat,
                    pair(new_stack, pair(tag_eq, pair(te, ts))),
                    pair(pe, pair(re, var)))
            )) != 0
        }),
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi, 0nat,
{
    let tag = formula_tag(phi);
    let phi_enc = encode(phi);
    let le = encode(left);
    let re_enc = encode(right);

    lemma_unpair1_pair(tag, pair(le, re_enc));
    lemma_unpair2_pair(tag, pair(le, re_enc));
    lemma_unpair1_pair(le, re_enc);
    lemma_unpair2_pair(le, re_enc);

    //  Tag contradiction: if tag_eq == 0, iterate has valid=0 → contradiction
    if unpair1(result_enc) != tag {
        let result_c = unpair2(result_enc);
        let entry_l = pair(le, unpair1(result_c));
        let entry_r = pair(re_enc, unpair2(result_c));
        lemma_iterate_valid_zero_contradiction((fuel-1) as nat,
            pair(entry_l + 1, pair(entry_r + 1, rest)),
            te, ts, pe, re, var);
    }

    //  Extract result sub-encodings
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));
    let rl = unpair1(unpair2(result_enc));
    let rr = unpair2(unpair2(result_enc));
    let rest_r = pair(pair(re_enc, rr)+1, rest);

    //  IH on left
    let t_l = lemma_forward_walk_iterate(left, rl, var,
        rest_r, te, ts, pe, re, (fuel-1) as nat);

    //  Delegate right IH + combine to separate file
    lemma_forward_binary_right_and_combine(
        phi, left, right, tag, result_enc, var,
        rest, te, ts, pe, re, (fuel-1) as nat,
        t_l, rl, rr)
}

} // verus!
