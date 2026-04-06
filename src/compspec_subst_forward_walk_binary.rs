use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_induction2::{subst_state, lemma_subst_state_invariant, lemma_subst_traversal2};
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;
use crate::compspec_subst_forward_binary_combine::lemma_binary_combine;

verus! {

///  Binary right + combine: backward decomposition, right IH, t-consistency.
///  Caller does step + unfold + tag + left IH, passes t_l.
///  NO compspec_iterate in precondition — uses the backward traversal's ensures
///  to establish the right IH's precondition internally.
#[verifier::rlimit(5000)]
pub proof fn lemma_forward_walk_binary(
    phi: Formula, t_l: Term,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
    tag: nat, rl: nat, rr: nat,
) -> (t: Term)
    requires
        phi matches Formula::And{..} || phi matches Formula::Or{..}
            || phi matches Formula::Implies{..} || phi matches Formula::Iff{..},
        tag == formula_tag(phi), tag >= 3, tag <= 6,
        result_enc == pair(tag, pair(rl, rr)),
        rl == encode(subst(decode_formula(rl), var, t_l)) || true,  //  placeholder
        //  Left IH result
        ({
            match phi {
                Formula::And { left, right } | Formula::Or { left, right }
                | Formula::Implies { left, right } | Formula::Iff { left, right } => {
                    rl == encode(subst(*left, var, t_l)) &&
                    (ts != 0nat ==> encode_term(t_l) == te) &&
                    //  Iterate from left+right state gives valid != 0
                    //  (needed for backward traversal + right IH)
                    fuel >= subst_traversal_cost(*left, var) + subst_traversal_cost(*right, var) &&
                    unpair1(unpair2(
                        compspec_iterate(check_subst_step(), fuel,
                            pair(pair(pair(encode(*left), rl) + 1,
                                      pair(pair(encode(*right), rr) + 1, rest)),
                                 pair(1nat, pair(te, ts))),
                            pair(pe, pair(re, var)))
                    )) != 0
                },
                _ => false,
            }
        }),
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi, 0nat,
{
    match phi {
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            let rest_r = pair(pair(encode(*right), rr)+1, rest);

            //  Backward traversal on left to decompose iterate
            let (te_l, ts_l) = subst_state(*left, var, encode_term(t_l), te, ts);
            lemma_subst_state_invariant(*left, var, encode_term(t_l), te, ts);
            lemma_subst_traversal2(*left, var, t_l, rest_r, te, ts, pe, re, fuel);

            //  Right IH
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
