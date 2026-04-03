use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_step_binary::lemma_forward_step_binary;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Tag match for Binary (tags 3-6): if checker accepts, result tag matches phi tag.
pub proof fn lemma_forward_binary_tag_match(phi_enc: nat, result_enc: nat, var: nat)
    requires
        unpair1(phi_enc) >= 3nat,
        unpair1(phi_enc) <= 6nat,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        unpair1(result_enc) == unpair1(phi_enc),
{
    if unpair1(result_enc) != unpair1(phi_enc) {
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));

        lemma_check_subst_unfold(phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);

        //  One step: tag_eq = 0 since tags differ
        lemma_forward_step_binary(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        let phi_c = unpair2(phi_enc);
        let result_c = unpair2(result_enc);
        let entry_l = pair(unpair1(phi_c), unpair1(result_c));
        let entry_r = pair(unpair2(phi_c), unpair2(result_c));
        let new_stack = pair(entry_l + 1, pair(entry_r + 1, 0nat));

        //  valid = 0. valid_zero_stable.
        lemma_subst_valid_zero_stable(phi_enc, new_stack,
            0nat, 0nat, phi_enc, result_enc, var);
        lemma_unpair2_pair(new_stack, pair(0nat, pair(0nat, 0nat)));
        lemma_unpair1_pair(0nat, pair(0nat, 0nat));
    }
}

} // verus!
