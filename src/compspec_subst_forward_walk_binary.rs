use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_induction2::{subst_state, lemma_subst_state_invariant, lemma_subst_traversal2};
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;
use crate::compspec_subst_forward_binary_combine::lemma_binary_combine;

verus! {

///  Binary walk: NO Formula params for left/right (avoids mutual recursion term blowup).
///  Extracts left/right from phi via match inside the body.
#[verifier::rlimit(20000)]
pub proof fn lemma_forward_walk_binary(
    phi: Formula,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
    tag: nat, el: nat, er: nat,
) -> (t: Term)
    requires
        tag >= 3, tag <= 6,
        encode(phi) == pair(tag, pair(el, er)),
        fuel >= subst_traversal_cost(phi, var),
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
    match phi {
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            //  Tag check
            if unpair1(result_enc) != tag {
                lemma_pair_surjective(result_enc);
                lemma_pair_surjective(unpair2(result_enc));
                lemma_iterate_valid_zero_contradiction(fuel,
                    pair(pair(el,unpair1(unpair2(result_enc)))+1,
                         pair(pair(er,unpair2(unpair2(result_enc)))+1, rest)),
                    te, ts, pe, re, var);
            }

            lemma_pair_surjective(result_enc);
            lemma_pair_surjective(unpair2(result_enc));
            let rl = unpair1(unpair2(result_enc));
            let rr = unpair2(unpair2(result_enc));
            let rest_r = pair(pair(er, rr)+1, rest);

            //  IH on left (*left < phi — structural from match)
            let t_l = lemma_forward_walk_iterate(*left, rl, var,
                rest_r, te, ts, pe, re, fuel);

            //  Backward decomposition + right IH
            let (te_l, ts_l) = subst_state(*left, var, encode_term(t_l), te, ts);
            lemma_subst_state_invariant(*left, var, encode_term(t_l), te, ts);
            lemma_subst_traversal2(*left, var, t_l, rest_r, te, ts, pe, re, fuel);
            let fuel_r = (fuel - subst_traversal_cost(*left, var)) as nat;
            let t_r = lemma_forward_walk_iterate(*right, rr, var,
                rest, te_l, ts_l, pe, re, fuel_r);

            //  Combine
            lemma_subst_preserves_tag(phi, var, t_l);
            lemma_subst_preserves_tag(phi, var, t_r);
            return lemma_binary_combine(phi, *left, *right, tag, result_enc, var, te, ts,
                t_l, t_r, rl, rr, te_l, ts_l);
        },
        _ => { return Term::Var { index: 0 }; },
    }
}

} // verus!
