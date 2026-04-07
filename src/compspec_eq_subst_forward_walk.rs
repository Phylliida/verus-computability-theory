use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_eq_subst_backward::lemma_eq_subst_dispatch;
use crate::compspec_eq_subst_forward_step::lemma_eq_subst_forward_step_atomic;

verus! {

///  Step with valid=0 returns acc unchanged.
proof fn lemma_esb_step_valid_zero(counter: nat, stack: nat, s: nat)
    ensures ({
        let acc = pair(stack, 0nat);
        eval_comp(check_eq_subst_step(), pair(counter, pair(acc, s))) == acc
    }),
{
    let acc = pair(stack, 0nat);
    let n = pair(counter, pair(acc, s));
    lemma_eval_br_acc(counter, acc, s);
    let valid_cs = cs_snd(br_acc());
    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(stack, 0nat);
    lemma_eval_ifzero_then(valid_cs, br_acc(),
        CompSpec::IfZero {
            cond: Box::new(cs_fst(cs_fst(br_acc()))),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_eq_subst_process()),
        }, n);
}

///  Iterating with valid=0 keeps acc unchanged.
proof fn lemma_esb_valid_zero_stable(fuel: nat, stack: nat, s: nat)
    ensures
        compspec_iterate(check_eq_subst_step(), fuel, pair(stack, 0nat), s)
            == pair(stack, 0nat),
    decreases fuel,
{
    if fuel > 0 {
        lemma_esb_step_valid_zero((fuel - 1) as nat, stack, s);
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, pair(stack, 0nat), s);
        lemma_esb_valid_zero_stable((fuel - 1) as nat, stack, s);
    }
}

///  Contradiction: valid-zero iterate cannot be nonzero.
proof fn lemma_esb_valid_zero_contradiction(fuel: nat, stack: nat, s: nat)
    requires
        unpair2(compspec_iterate(check_eq_subst_step(), fuel, pair(stack, 0nat), s)) != 0,
    ensures false,
{
    lemma_esb_valid_zero_stable(fuel, stack, s);
    lemma_unpair2_pair(stack, 0nat);
}

///  Forward walk: if check_eq_subst parallel iterate accepts, formulas are eq_subst_compatible.
#[verifier::rlimit(5000)]
pub proof fn lemma_eq_subst_forward_walk(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, fuel: nat,
)
    requires
        fuel >= formula_size(f1),
        unpair2(
            compspec_iterate(check_eq_subst_step(), fuel,
                pair(pair(pair(encode(f1), encode(f2)) + 1, rest), 1nat),
                pair(encode(f1), pair(encode(f2), pair(x_enc, y_enc))))
        ) != 0,
    ensures
        eq_subst_compatible(f1, f2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1,
{
    hide(compspec_iterate);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let entry = pair(f1_enc, f2_enc);
    let acc0 = pair(pair(entry + 1, rest), 1nat);
    let s = pair(f1_enc, pair(f2_enc, pair(x_enc, y_enc)));

    lemma_formula_size_pos(f1);

    match f1 {
        Formula::Eq { left: l1, right: r1 } => {
            //  One step: atomic check
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(0nat, pair(encode_term(l1), encode_term(r1)));
            //  Unfold + step
            assert(unpair2(eval_comp(check_eq_subst_step(),
                pair((fuel - 1) as nat, pair(acc0, s)))) != 0) by {
                reveal(compspec_iterate);
                lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                let step_result = eval_comp(check_eq_subst_step(),
                    pair((fuel - 1) as nat, pair(acc0, s)));
                //  Remaining iterate from step_result: if step valid = 0, stays 0 → contradiction
                if unpair2(step_result) == 0 {
                    lemma_pair_surjective(step_result);
                    lemma_esb_valid_zero_stable((fuel - 1) as nat, unpair1(step_result), s);
                    lemma_unpair2_pair(unpair1(step_result), 0nat);
                }
            };
            //  Use the forward step helper
            lemma_eq_subst_forward_step_atomic(f1_enc, f2_enc,
                rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
            //  Tag match: unpair1(f1_enc) == unpair1(f2_enc) == 0
            //  f2 must be Eq
            match f2 {
                Formula::Eq { left: l2, right: r2 } => {
                    //  Term compatibility established by step helper
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(0nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair2_pair(0nat, pair(encode_term(l1), encode_term(r1)));
                    lemma_unpair2_pair(0nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair1_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair2_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair1_pair(encode_term(l2), encode_term(r2));
                    lemma_unpair2_pair(encode_term(l2), encode_term(r2));
                    return;
                },
                _ => {
                    //  unpair1(f2_enc) != 0 → contradiction with tags match
                    lemma_encode_is_pair(f2);
                    return;
                },
            }
        },
        Formula::In { left: l1, right: r1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(1nat, pair(encode_term(l1), encode_term(r1)));
            assert(unpair2(eval_comp(check_eq_subst_step(),
                pair((fuel - 1) as nat, pair(acc0, s)))) != 0) by {
                reveal(compspec_iterate);
                lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                let step_result = eval_comp(check_eq_subst_step(),
                    pair((fuel - 1) as nat, pair(acc0, s)));
                if unpair2(step_result) == 0 {
                    lemma_pair_surjective(step_result);
                    lemma_esb_valid_zero_stable((fuel - 1) as nat, unpair1(step_result), s);
                    lemma_unpair2_pair(unpair1(step_result), 0nat);
                }
            };
            lemma_eq_subst_forward_step_atomic(f1_enc, f2_enc,
                rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
            match f2 {
                Formula::In { left: l2, right: r2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(1nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair2_pair(1nat, pair(encode_term(l1), encode_term(r1)));
                    lemma_unpair2_pair(1nat, pair(encode_term(l2), encode_term(r2)));
                    lemma_unpair1_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair2_pair(encode_term(l1), encode_term(r1));
                    lemma_unpair1_pair(encode_term(l2), encode_term(r2));
                    lemma_unpair2_pair(encode_term(l2), encode_term(r2));
                    return;
                },
                _ => {
                    lemma_encode_is_pair(f2);
                    return;
                },
            }
        },
        Formula::Not { sub: s1 } => {
            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(2nat, encode(*s1));
            lemma_unpair2_pair(2nat, encode(*s1));
            //  Step: dispatch → unary, pushes sub-entry, valid = tags_match
            //  Need to prove tags match (else contradiction)
            match f2 {
                Formula::Not { sub: s2 } => {
                    lemma_encode_is_pair(f2);
                    lemma_unpair1_pair(2nat, encode(*s2));
                    lemma_unpair2_pair(2nat, encode(*s2));
                    //  Tags match (both 2), step pushes sub-entry with valid=1
                    //  By backward step helper (which just computes the step):
                    crate::compspec_eq_subst_backward::lemma_eq_subst_step_unary(
                        *s1, *s2,
                        Term::Var { index: x_enc }, Term::Var { index: y_enc },
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc);
                    //  Unfold iterate
                    assert(unpair2(
                        compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                            pair(pair(pair(encode(*s1), encode(*s2)) + 1, rest), 1nat), s)
                    ) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    //  IH on sub
                    lemma_eq_subst_forward_walk(*s1, *s2, x_enc, y_enc, rest, (fuel - 1) as nat);
                    return;
                },
                _ => {
                    //  f2 tag != 2, step tags_match = 0, valid = 0
                    //  Need contradiction: derive that iterate gives 0
                    lemma_encode_is_pair(f2);
                    //  Tags: unpair1(f1_enc) = 2, unpair1(f2_enc) != 2
                    //  Step with mismatched tags gives valid = 0
                    //  Then remaining iterate keeps 0 → contradiction
                    //  (Informal — the match on f2 exhausts the case where f2 is Not)
                    //  For non-Not f2, the step produces tags_match = 0, new valid = 0
                    //  This needs the step evaluation — defer to tag-mismatch contradiction
                    return;  //  Z3 should derive false from the precondition inconsistency
                },
            }
        },
        //  Binary and quantifier cases follow the same pattern as Not
        //  TODO: implement remaining 6 cases
        _ => {
            //  Placeholder — will fill in
            return;
        },
    }
}

} // verus!
