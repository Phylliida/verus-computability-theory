use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::lemma_check_subst_unfold;
use crate::compspec_subst_forward_walk_iter::lemma_forward_walk_iterate;

verus! {

///  Forward soundness of check_subst_comp:
///  If the checker accepts (phi_enc, result_enc, var), then
///  result = subst(phi, var, t) for some term t.
pub proof fn lemma_check_subst_comp_forward(phi: Formula, result_enc: nat, var: nat) -> (t: Term)
    requires
        eval_comp(check_subst_comp(), pair(encode(phi), pair(result_enc, var))) != 0,
        exists|f: Formula| encode(f) == result_enc,
    ensures
        result_enc == encode(subst(phi, var, t)),
{
    let phi_enc = encode(phi);

    //  Bridge: eval_comp(check_subst_comp(), ...) == unpair1(unpair2(compspec_iterate(...)))
    lemma_check_subst_unfold(phi_enc, result_enc, var);

    //  Fuel adequacy: phi_enc + 1 >= subst_traversal_cost(phi, var)
    lemma_subst_traversal_cost_pos(phi, var);
    if phi_enc > 0 {
        lemma_encode_ge_subst_cost(phi, var);
    }

    //  Forward walk at iterate level
    lemma_forward_walk_iterate(phi, result_enc, var,
        0nat, 0nat, 0nat, phi_enc, result_enc, (phi_enc + 1) as nat)
}

} // verus!
