use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_backward::lemma_esb_pair_unfold;
use crate::compspec_eq_subst_forward_walk::lemma_eq_subst_forward_walk;

verus! {

///  Forward entry point for the parallel walk checker.
///  Given two formulas f1 and f2 such that the parallel walk accepts their encodings,
///  prove that they are eq_subst_compatible.
pub proof fn lemma_check_eq_subst_pair_forward(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
)
    requires
        eval_comp(check_eq_subst_pair(),
            pair(encode(f1), pair(encode(f2), pair(x_enc, y_enc)))) != 0,
    ensures
        eq_subst_compatible(f1, f2,
            Term::Var { index: x_enc }, Term::Var { index: y_enc }),
{
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);

    //  Bridge: eval_comp(check_eq_subst_pair(), input) == unpair2(iterate)
    //  with fuel = f1_enc + 1
    lemma_esb_pair_unfold(f1_enc, f2_enc, x_enc, y_enc);

    //  Fuel adequacy: f1_enc + 1 >= formula_size(f1)
    lemma_formula_size_pos(f1);
    if f1_enc == 0 {
        //  f1 = Eq(Var(0), Var(0)), formula_size = 1, fuel = 1 ✓
    } else {
        lemma_encode_ge_formula_size(f1);
        //  f1_enc >= formula_size(f1), so f1_enc + 1 > formula_size(f1)
    }

    //  Walk with valid = 1 (initial state from the checker)
    lemma_eq_subst_forward_walk(f1, f2, x_enc, y_enc,
        0nat, 1nat, f1_enc, f2_enc, (f1_enc + 1) as nat);
}

} // verus!
