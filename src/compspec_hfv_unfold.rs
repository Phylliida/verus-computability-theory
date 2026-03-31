use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

///  Unfold: eval_comp(has_free_var_comp(), input) in terms of compspec_iterate.
///  Fuel is f_enc + 1 (ensures at least 1 step even when f_enc == 0).
pub proof fn lemma_hfv_comp_eval(f_enc: nat, v: nat)
    ensures ({
        let input = pair(f_enc, v);
        let base_val = pair(pair(f_enc + 1, 0nat), 0nat);
        eval_comp(has_free_var_comp(), input)
            == unpair2(compspec_iterate(has_free_var_step(), (f_enc + 1) as nat, base_val, input))
    }),
{
    let input = pair(f_enc, v);

    //  Match the definition's let bindings exactly
    let f_enc_expr = cs_fst(CompSpec::Id);
    let f_enc_plus_1 = CompSpec::Add { left: Box::new(f_enc_expr), right: Box::new(cs_const(1)) };
    let stack_entry = CompSpec::Add { left: Box::new(f_enc_expr), right: Box::new(cs_const(1)) };
    let base_cs = cs_pair(cs_pair(stack_entry, cs_const(0)), cs_const(0));
    let br = CompSpec::BoundedRec {
        count_fn: Box::new(f_enc_plus_1),
        base: Box::new(base_cs),
        step: Box::new(has_free_var_step()),
    };

    //  Structural equality
    assert(has_free_var_comp() == cs_comp(cs_snd(CompSpec::Id), br));

    lemma_eval_comp(cs_snd(CompSpec::Id), br, input);
    lemma_eval_bounded_rec(f_enc_plus_1, base_cs, has_free_var_step(), input);

    //  Fuel = f_enc + 1
    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(f_enc, v);
    lemma_eval_add(f_enc_expr, cs_const(1), input);

    //  Base
    lemma_eval_pair(stack_entry, cs_const(0), input);
    lemma_eval_pair(cs_pair(stack_entry, cs_const(0)), cs_const(0), input);

    //  Chain
    let base_val = pair(pair(f_enc + 1, 0nat), 0nat);
    assert(eval_comp(f_enc_plus_1, input) == (f_enc + 1) as nat);
    assert(eval_comp(base_cs, input) == base_val);
    let br_result = compspec_iterate(has_free_var_step(), (f_enc + 1) as nat, base_val, input);
    assert(eval_comp(br, input) == br_result);
    lemma_eval_snd(CompSpec::Id, br_result);
}

} // verus!
