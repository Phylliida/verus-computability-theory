use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_step_helpers::*;

verus! {

///  Chain one step of compspec_iterate for check_subst_step.
proof fn lemma_subst_csi_chain(
    fuel: nat, old_acc: nat, new_acc: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        fuel > 0,
        eval_comp(check_subst_step(),
            pair((fuel - 1) as nat, pair(old_acc, pair(phi_enc, pair(result_enc, var)))))
            == new_acc,
    ensures
        compspec_iterate(check_subst_step(), fuel, old_acc,
            pair(phi_enc, pair(result_enc, var)))
        == compspec_iterate(check_subst_step(), (fuel - 1) as nat, new_acc,
            pair(phi_enc, pair(result_enc, var))),
{
    lemma_compspec_iterate_unfold(check_subst_step(), fuel, old_acc,
        pair(phi_enc, pair(result_enc, var)));
}

///  Main structural induction: processing formula f from the stack.
///  Shows: starting from stack = [(fe, re) | rest], valid=1, t_enc, t_set,
///  after formula_size(f) iterations, the result is:
///  stack = rest, valid = 1, t_enc, t_set unchanged.
///
///  This mirrors lemma_traversal_no_free_var from compspec_free_var_induction.rs.
pub proof fn lemma_subst_traversal(
    f: Formula, var: nat, t: Term, rest: nat,
    t_enc_val: nat, t_set_val: nat,
    phi_enc: nat, result_enc: nat, fuel: nat,
)
    requires
        fuel >= formula_size(f),
    ensures
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f), encode(subst(f, var, t))) + 1, rest),
                pair(1nat, pair(t_enc_val, t_set_val))),
            pair(phi_enc, pair(result_enc, var)))
        == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
            pair(rest, pair(1nat, pair(t_enc_val, t_set_val))),
            pair(phi_enc, pair(result_enc, var))),
    decreases f,
{
    hide(eval_comp);
    let fe = encode(f);
    let re = encode(subst(f, var, t));
    let entry = pair(fe, re);
    let acc = pair(pair(entry + 1, rest), pair(1nat, pair(t_enc_val, t_set_val)));
    let orig = pair(phi_enc, pair(result_enc, var));
    assert(fuel > 0) by { lemma_formula_size_pos(f); }
    lemma_subst_preserves_tag(f, var, t);

    //  One step: dispatch to process_pair
    lemma_subst_step_dispatch((fuel - 1) as nat, entry + 1, rest, 1nat,
        t_enc_val, t_set_val, phi_enc, result_enc, var);

    match f {
        Formula::Eq { left, right } => {
            //  formula_size = 1, one step processes the entry
            lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(0nat, pair(encode_term(subst_term(left, var, t)),
                encode_term(subst_term(right, var, t))));
            lemma_subst_process_pair_atomic_eq((fuel - 1) as nat, fe, re, rest,
                1, t_enc_val, t_set_val, phi_enc, result_enc, var);
            lemma_subst_csi_chain(fuel, acc,
                pair(rest, pair(1nat, pair(t_enc_val, t_set_val))),
                phi_enc, result_enc, var);
        },
        Formula::In { left, right } => {
            lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(1nat, pair(encode_term(subst_term(left, var, t)),
                encode_term(subst_term(right, var, t))));
            lemma_subst_process_pair_atomic_in((fuel - 1) as nat, fe, re, rest,
                1, t_enc_val, t_set_val, phi_enc, result_enc, var);
            lemma_subst_csi_chain(fuel, acc,
                pair(rest, pair(1nat, pair(t_enc_val, t_set_val))),
                phi_enc, result_enc, var);
        },
        Formula::Not { sub } => {
            //  formula_size = 1 + formula_size(sub)
            //  One step: process Not, push (encode(sub), encode(subst(sub, var, t)))
            lemma_unpair1_pair(2nat, encode(*sub));
            lemma_unpair1_pair(2nat, encode(subst(*sub, var, t)));
            lemma_subst_process_pair_unary((fuel - 1) as nat, fe, re, rest,
                1, t_enc_val, t_set_val, phi_enc, result_enc, var);
            let sub_fe = encode(*sub);
            let sub_re = encode(subst(*sub, var, t));
            let new_entry = pair(sub_fe, sub_re);
            let new_stack = pair(new_entry + 1, rest);
            let new_acc = pair(new_stack, pair(1nat, pair(t_enc_val, t_set_val)));
            //  unpair2(phi_node) for Not = encode(sub), unpair2(result_node) for Not = encode(subst(sub))
            lemma_unpair2_pair(2nat, encode(*sub));
            lemma_unpair2_pair(2nat, encode(subst(*sub, var, t)));
            assert(unpair2(fe) == sub_fe);
            assert(unpair2(re) == sub_re);
            lemma_subst_csi_chain(fuel, acc, new_acc, phi_enc, result_enc, var);
            //  Now recurse on sub
            lemma_subst_traversal(*sub, var, t, rest,
                t_enc_val, t_set_val, phi_enc, result_enc, (fuel - 1) as nat);
        },
        //  TODO: binary + quantifier cases
        _ => {},
    }
}

} //  verus!
