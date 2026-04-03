use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_forward_step_not::lemma_forward_step_not;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Tag match for Not (tag 2): if checker accepts and phi has tag 2, result has tag 2.
///  Uses lemma_forward_step_not for the step evaluation (isolated in own file).
pub proof fn lemma_forward_not_tag_match(phi_enc: nat, result_enc: nat, var: nat)
    requires
        unpair1(phi_enc) == 2nat,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        unpair1(result_enc) == 2nat,
{
    if unpair1(result_enc) != 2 {
        let input = pair(phi_enc, pair(result_enc, var));
        let entry = pair(phi_enc, result_enc);
        let base = pair(pair(entry + 1, 0nat), pair(1nat, pair(0nat, 0nat)));

        lemma_check_subst_unfold(phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), (phi_enc + 1) as nat, base, input);

        //  One step: produces pair(sub_stack, pair(0, pair(0, 0))) since tags differ
        lemma_forward_step_not(phi_enc, phi_enc, result_enc, 0nat, 1nat, 0nat, 0nat,
            phi_enc, result_enc, var);
        let sub_entry = pair(unpair2(phi_enc), unpair2(result_enc));
        let step_result = pair(pair(sub_entry + 1, 0nat), pair(0nat, pair(0nat, 0nat)));

        //  valid = 0. valid_zero_stable for remaining fuel.
        lemma_subst_valid_zero_stable(phi_enc, pair(sub_entry + 1, 0nat),
            0nat, 0nat, phi_enc, result_enc, var);
        lemma_unpair2_pair(pair(sub_entry + 1, 0nat), pair(0nat, pair(0nat, 0nat)));
        lemma_unpair1_pair(0nat, pair(0nat, 0nat));
    }
}

} // verus!
