use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;
use crate::compspec_subst_forward_walk_binary_right::lemma_forward_binary_right_and_combine;

verus! {

///  Binary walk: tag check + left IH + delegate right to helper.
///  Caller does step + unfold; this takes the post-step iterate.
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
        ({
            let tag = formula_tag(phi);
            let tag_eq: nat = if unpair1(result_enc) == tag { 1nat } else { 0nat };
            let el = encode(left); let er = encode(right);
            let rl = unpair1(unpair2(result_enc));
            let rr = unpair2(unpair2(result_enc));
            unpair1(unpair2(
                compspec_iterate(check_subst_step(), (fuel - 1) as nat,
                    pair(pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)), pair(tag_eq, pair(te, ts))),
                    pair(pe, pair(re, var)))
            )) != 0
        }),
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi, 0nat,
{
    let tag = formula_tag(phi);
    let el = encode(left);
    let er = encode(right);
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));
    let rl = unpair1(unpair2(result_enc));
    let rr = unpair2(unpair2(result_enc));

    //  Tag contradiction
    if unpair1(result_enc) != tag {
        lemma_iterate_valid_zero_contradiction((fuel-1) as nat,
            pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)),
            te, ts, pe, re, var);
    }

    //  IH on left
    let rest_r = pair(pair(er, rr)+1, rest);
    let t_l = lemma_forward_walk_iterate(left, rl, var,
        rest_r, te, ts, pe, re, (fuel-1) as nat);

    //  Delegate right IH + combine
    lemma_forward_binary_right_and_combine(
        phi, left, right, tag, result_enc, var,
        rest, te, ts, pe, re, (fuel-1) as nat,
        t_l, rl, rr)
}

} // verus!
