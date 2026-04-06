use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_induction2::{subst_state, lemma_subst_state_invariant, lemma_subst_traversal2};
use crate::compspec_subst_forward_step_binary::lemma_forward_step_binary;
use crate::compspec_subst_forward_binary_combine::lemma_binary_combine;
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;

verus! {

///  Binary case of the iterate walk. Separated to reduce Z3 context per file.
///  Uses `decreases (phi, 0nat)` — the main walk uses `decreases (phi, 1nat)`.
///  Recursive IH calls go through lemma_forward_walk_iterate on *left/*right (smaller phi).
#[verifier::rlimit(5000)]
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
    decreases phi, 0nat,
{
    let tag = formula_tag(phi);
    let phi_enc = encode(phi);
    let acc0 = pair(pair(pair(phi_enc, result_enc) + 1, rest), pair(1nat, pair(te, ts)));
    let input = pair(pe, pair(re, var));

    lemma_unpair1_pair(tag, pair(encode(left), encode(right)));
    lemma_unpair2_pair(tag, pair(encode(left), encode(right)));

    //  Step: pushes left+right entries
    lemma_forward_step_binary((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
    lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);

    //  Tag contradiction
    if unpair1(result_enc) != tag {
        let pc = unpair2(phi_enc); let rc = unpair2(result_enc);
        lemma_iterate_valid_zero_contradiction((fuel-1) as nat,
            pair(pair(unpair1(pc),unpair1(rc))+1, pair(pair(unpair2(pc),unpair2(rc))+1, rest)),
            te, ts, pe, re, var);
    }

    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));
    let rl = unpair1(unpair2(result_enc));
    let rr = unpair2(unpair2(result_enc));

    //  IH on left (rest includes right entry)
    let rest_r = pair(pair(encode(right), rr)+1, rest);
    let t_l = lemma_forward_walk_iterate(left, rl, var,
        rest_r, te, ts, pe, re, (fuel-1) as nat);

    //  Backward traversal decomposes iterate after left
    lemma_subst_state_invariant(left, var, encode_term(t_l), te, ts);
    let (te_l, ts_l) = subst_state(left, var, encode_term(t_l), te, ts);
    lemma_subst_traversal2(left, var, t_l, rest_r, te, ts, pe, re, (fuel-1) as nat);

    //  IH on right
    let fuel_r = ((fuel-1) as nat - subst_traversal_cost(left, var)) as nat;
    let t_r = lemma_forward_walk_iterate(right, rr, var,
        rest, te_l, ts_l, pe, re, fuel_r);

    //  T-consistency combine
    lemma_subst_preserves_tag(phi, var, t_l);
    lemma_subst_preserves_tag(phi, var, t_r);
    return lemma_binary_combine(phi, left, right, tag, result_enc, var, te, ts,
        t_l, t_r, rl, rr, te_l, ts_l);
}

} // verus!
