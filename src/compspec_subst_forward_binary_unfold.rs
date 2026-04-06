use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::check_subst_step;
use crate::compspec_subst_forward_step_binary::lemma_forward_step_binary;
use crate::compspec_subst_forward_helpers::lemma_iterate_valid_zero_contradiction;

verus! {

///  Binary step + unfold + tag match: converts phi-level iterate to left+right-level iterate.
///  Non-recursive — isolated in own file to keep step/unfold facts out of the walk's Z3 context.
#[verifier::rlimit(2000)]
pub proof fn lemma_binary_step_unfold(
    phi: Formula, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
)
    requires
        formula_tag(phi) >= 3, formula_tag(phi) <= 6,
        fuel >= 1,
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(encode(phi), result_enc) + 1, rest),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0,
    ensures ({
        let tag = formula_tag(phi);
        let el = unpair1(unpair2(encode(phi)));
        let er = unpair2(unpair2(encode(phi)));
        let rl = unpair1(unpair2(result_enc));
        let rr = unpair2(unpair2(result_enc));
        unpair1(result_enc) == tag &&
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), (fuel - 1) as nat,
                pair(pair(pair(el,rl)+1, pair(pair(er,rr)+1, rest)),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0
    }),
{
    let tag = formula_tag(phi);
    let phi_enc = encode(phi);
    let el = unpair1(unpair2(phi_enc));
    let er = unpair2(unpair2(phi_enc));
    let acc0 = pair(pair(pair(phi_enc, result_enc) + 1, rest), pair(1nat, pair(te, ts)));
    let input = pair(pe, pair(re, var));

    lemma_encode_is_pair(phi);
    lemma_pair_surjective(unpair2(phi_enc));
    lemma_unpair1_pair(tag, pair(el, er));
    lemma_unpair2_pair(tag, pair(el, er));

    lemma_forward_step_binary((fuel-1) as nat, phi_enc, result_enc, rest, 1, te, ts, pe, re, var);
    lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc0, input);

    if unpair1(result_enc) != tag {
        //  tag_eq=0, step result has valid=0 → contradiction with precondition
        lemma_pair_surjective(result_enc);
        lemma_pair_surjective(unpair2(result_enc));
        lemma_iterate_valid_zero_contradiction((fuel-1) as nat,
            pair(pair(el,unpair1(unpair2(result_enc)))+1,
                 pair(pair(er,unpair2(unpair2(result_enc)))+1, rest)),
            te, ts, pe, re, var);
    }
}

} // verus!
