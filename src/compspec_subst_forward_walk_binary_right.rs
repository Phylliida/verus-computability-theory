use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_induction2::{subst_state, lemma_subst_state_invariant, lemma_subst_traversal2};
use crate::compspec_subst_forward_binary_combine::lemma_binary_combine;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;

verus! {

///  Binary walk Phase 2: backward decomposition + right IH + combine.
///  Takes left IH result as parameter. Isolated to reduce Z3 context.
#[verifier::rlimit(5000)]
pub proof fn lemma_forward_binary_right_and_combine(
    phi: Formula, left: Formula, right: Formula, tag: nat,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel_left: nat,
    t_l: Term, rl: nat, rr: nat,
) -> (t: Term)
    requires
        tag >= 3, tag <= 6,
        encode(phi) == pair(tag, pair(encode(left), encode(right))),
        //  Left IH result
        rl == encode(subst(left, var, t_l)),
        ts != 0nat ==> encode_term(t_l) == te,
        //  Result structure
        result_enc == pair(tag, pair(rl, rr)),
        //  Remaining iterate (after left processing) gives valid != 0
        fuel_left >= subst_traversal_cost(left, var),
        ({
            let rest_r = pair(pair(encode(right), rr)+1, rest);
            unpair1(unpair2(
                compspec_iterate(check_subst_step(), fuel_left,
                    pair(pair(pair(encode(left), rl) + 1, rest_r),
                         pair(1nat, pair(te, ts))),
                    pair(pe, pair(re, var)))
            )) != 0
        }),
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi, 0nat,
{
    let rest_r = pair(pair(encode(right), rr)+1, rest);
    let input = pair(pe, pair(re, var));

    //  Backward decomposition: left traversal gives right iterate state
    let (te_l, ts_l) = subst_state(left, var, encode_term(t_l), te, ts);
    lemma_subst_state_invariant(left, var, encode_term(t_l), te, ts);
    lemma_subst_traversal2(left, var, t_l, rest_r, te, ts, pe, re, fuel_left);

    //  Right IH
    let fuel_r = (fuel_left - subst_traversal_cost(left, var)) as nat;
    let t_r = lemma_forward_walk_iterate(right, rr, var,
        rest, te_l, ts_l, pe, re, fuel_r);

    //  Combine
    lemma_subst_preserves_tag(phi, var, t_l);
    lemma_subst_preserves_tag(phi, var, t_r);
    lemma_binary_combine(phi, left, right, tag, result_enc, var, te, ts,
        t_l, t_r, rl, rr, te_l, ts_l)
}

} // verus!
