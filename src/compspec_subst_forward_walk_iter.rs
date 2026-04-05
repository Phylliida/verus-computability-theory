use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_forward_eq_iter_tag::*;
use crate::compspec_subst_forward_walk_atomic::lemma_forward_atomic_eq_iter;
use crate::compspec_subst_forward_walk_atomic_in::lemma_forward_atomic_in_iter;
use crate::compspec_subst_forward_step_not::lemma_forward_step_not;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Iterate-level forward walk: structural induction on phi.
#[verifier::rlimit(3000)]
pub proof fn lemma_forward_walk_iterate(
    phi: Formula, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
) -> (t: Term)
    requires
        //  TEMPORARY: restrict to implemented cases. Remove when all cases done.
        phi matches Formula::Eq{..} || phi matches Formula::In{..} || phi matches Formula::Not{..},
        fuel >= subst_traversal_cost(phi, var),
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(phi), result_enc) + 1, rest),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0,
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
    decreases phi,
{
    let phi_enc = encode(phi);

    match phi {
        Formula::Eq { left, right } => {
            lemma_subst_traversal_cost_pos(phi, var);
            lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_forward_eq_tag_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel);
            lemma_forward_atomic_eq_iter(left, right, result_enc, var, rest, te, ts, pe, re, fuel)
        },
        Formula::In { left, right } => {
            lemma_subst_traversal_cost_pos(phi, var);
            lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_forward_in_tag_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel);
            lemma_forward_atomic_in_iter(left, right, result_enc, var, rest, te, ts, pe, re, fuel)
        },
        Formula::Not { sub } => {
            lemma_subst_traversal_cost_pos(phi, var);
            lemma_unpair1_pair(2nat, encode(*sub));
            lemma_unpair2_pair(2nat, encode(*sub));

            //  Step result
            lemma_forward_step_not((fuel - 1) as nat, phi_enc, result_enc, rest,
                1nat, te, ts, pe, re, var);
            let tag_eq: nat = if unpair1(result_enc) == 2nat { 1nat } else { 0nat };
            let sub_enc = encode(*sub);
            let result_sub_enc = unpair2(result_enc);
            let sub_entry = pair(sub_enc, result_sub_enc);

            //  Unfold iterate
            let acc0 = pair(pair(pair(phi_enc, result_enc) + 1, rest), pair(1nat, pair(te, ts)));
            let input = pair(pe, pair(re, var));
            lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);

            //  Tag contradiction if tags differ
            if tag_eq == 0nat {
                lemma_subst_valid_zero_stable((fuel - 1) as nat, pair(sub_entry + 1, rest),
                    te, ts, pe, re, var);
                lemma_unpair2_pair(pair(sub_entry + 1, rest), pair(0nat, pair(te, ts)));
                lemma_unpair1_pair(0nat, pair(te, ts));
            }

            //  IH on sub
            let t = lemma_forward_walk_iterate(*sub, result_sub_enc, var,
                rest, te, ts, pe, re, (fuel - 1) as nat);

            //  Combine: result_enc = pair(2, result_sub_enc) = pair(2, encode(subst(sub, var, t)))
            lemma_pair_surjective(result_enc);
            t
        },
        //  PLACEHOLDER — will be filled in
        _ => {
            //  Return arbitrary t — postcondition won't be satisfied for compound cases yet
            Term::Var { index: 0 }
        },
    }
}

} // verus!
