use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;
use crate::compspec_subst_forward_walk_binary_right::lemma_forward_binary_right_and_combine;

verus! {

///  Binary walk: tag check + left IH + right delegation.
///  Caller (walk_iter) does step + unfold and passes the post-step iterate.
///  2-way mutual recursion: walk_iter ↔ this ↔ binary_right → walk_iter.
#[verifier::rlimit(5000)]
pub proof fn lemma_forward_walk_binary(
    phi: Formula, left: Formula, right: Formula,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
    //  Post-step values (caller computes from step helper)
    tag: nat, el: nat, er: nat,
) -> (t: Term)
    requires
        tag >= 3, tag <= 6,
        el == encode(left), er == encode(right),
        encode(phi) == pair(tag, pair(el, er)),
        fuel >= subst_traversal_cost(left, var) + subst_traversal_cost(right, var),
        //  Post-step iterate gives valid != 0
        ({
            let tag_eq: nat = if unpair1(result_enc) == tag { 1nat } else { 0nat };
            let rl = unpair1(unpair2(result_enc));
            let rr = unpair2(unpair2(result_enc));
            unpair1(unpair2(
                compspec_iterate(check_subst_step(), fuel,
                    pair(pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)), pair(tag_eq, pair(te, ts))),
                    pair(pe, pair(re, var)))
            )) != 0
        }),
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi, 0nat,
{
    //  Tag check: if tag_eq == 0, iterate has valid=0 → contradiction
    if unpair1(result_enc) != tag {
        lemma_pair_surjective(result_enc);
        lemma_pair_surjective(unpair2(result_enc));
        let rl = unpair1(unpair2(result_enc));
        let rr = unpair2(unpair2(result_enc));
        lemma_iterate_valid_zero_contradiction(fuel,
            pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)),
            te, ts, pe, re, var);
    }

    //  Extract result sub-encodings
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));
    let rl = unpair1(unpair2(result_enc));
    let rr = unpair2(unpair2(result_enc));
    let rest_r = pair(pair(er, rr)+1, rest);

    //  IH on left
    let t_l = lemma_forward_walk_iterate(left, rl, var,
        rest_r, te, ts, pe, re, fuel);

    //  Right IH + combine
    return lemma_forward_binary_right_and_combine(
        phi, left, right, tag, result_enc, var,
        rest, te, ts, pe, re, fuel,
        t_l, rl, rr);
}

} // verus!
