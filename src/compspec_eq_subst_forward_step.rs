use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_eq_subst_backward::lemma_eq_subst_dispatch;
use crate::compspec_logic_axiom_helpers::lemma_eval_cs_or;

verus! {

///  Forward atomic step: if the parallel walk step produces valid != 0 for an atomic entry,
///  then the terms are eq_subst_term_compatible.
#[verifier::rlimit(1500)]
pub proof fn lemma_eq_subst_forward_step_atomic(
    left_node: nat, right_node: nat,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat, x_enc: nat, y_enc: nat,
)
    requires
        valid > 0,
        unpair1(left_node) <= 1,
    ensures ({
        let entry_val = pair(left_node, right_node) + 1;
        let acc = pair(pair(entry_val, rest_val), valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        let n = pair(counter, pair(acc, s));
        let result = eval_comp(check_eq_subst_step(), n);
        unpair1(result) == rest_val &&
        (unpair2(result) != 0 ==> (
            unpair1(left_node) == unpair1(right_node) &&
            eq_subst_term_compatible(
                Term::Var { index: unpair1(unpair2(left_node)) },
                Term::Var { index: unpair1(unpair2(right_node)) },
                Term::Var { index: x_enc }, Term::Var { index: y_enc }) &&
            eq_subst_term_compatible(
                Term::Var { index: unpair2(unpair2(left_node)) },
                Term::Var { index: unpair2(unpair2(right_node)) },
                Term::Var { index: x_enc }, Term::Var { index: y_enc })
        ))
    }),
{
    hide(eval_comp);
    let entry_val = pair(left_node, right_node) + 1;
    let acc = pair(pair(entry_val, rest_val), valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    //  Dispatch: valid > 0, entry > 0 → process
    assert(eval_comp(check_eq_subst_step(), n)
        == eval_comp(check_eq_subst_process(), n)) by {
        reveal(eval_comp);
        lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    };

    //  Extract entry
    assert(eval_comp(esb_entry(), n) == pair(left_node, right_node)) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_fst(cs_fst(br_acc()), n);
        lemma_unpair1_pair(entry_val, rest_val);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
        lemma_eval_pred(entry_val);
    };
    assert(eval_comp(esb_left_node(), n) == left_node) by {
        reveal(eval_comp); lemma_eval_fst(esb_entry(), n);
        lemma_unpair1_pair(left_node, right_node);
    };
    assert(eval_comp(esb_right_node(), n) == right_node) by {
        reveal(eval_comp); lemma_eval_snd(esb_entry(), n);
        lemma_unpair2_pair(left_node, right_node);
    };
    assert(eval_comp(esb_left_tag(), n) == unpair1(left_node)) by {
        reveal(eval_comp); lemma_eval_fst(esb_left_node(), n);
    };
    assert(eval_comp(esb_right_tag(), n) == unpair1(right_node)) by {
        reveal(eval_comp); lemma_eval_fst(esb_right_node(), n);
    };
    assert(eval_comp(esb_rest(), n) == rest_val) by {
        reveal(eval_comp);
        lemma_eval_br_acc(counter, acc, s);
        lemma_eval_fst(br_acc(), n);
        lemma_unpair1_pair(pair(entry_val, rest_val), valid);
        lemma_eval_snd(cs_fst(br_acc()), n);
        lemma_unpair2_pair(entry_val, rest_val);
    };

    //  xy pair
    assert(eval_comp(esb_xy_pair(), n) == pair(x_enc, y_enc)) by {
        reveal(eval_comp);
        lemma_eval_snd(CompSpec::Id, n);
        lemma_unpair2_pair(counter, pair(acc, s));
        lemma_eval_snd(cs_snd(CompSpec::Id), n);
        lemma_unpair2_pair(acc, s);
        lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), n);
        lemma_unpair2_pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), n);
        lemma_unpair2_pair(right_enc_s, pair(x_enc, y_enc));
    };
    assert(eval_comp(esb_x_enc(), n) == x_enc) by {
        reveal(eval_comp); lemma_eval_fst(esb_xy_pair(), n);
        lemma_unpair1_pair(x_enc, y_enc);
    };
    assert(eval_comp(esb_y_enc(), n) == y_enc) by {
        reveal(eval_comp); lemma_eval_snd(esb_xy_pair(), n);
        lemma_unpair2_pair(x_enc, y_enc);
    };

    //  Tag dispatch → atomic
    let is_compound = cs_lt(cs_const(1), esb_left_tag());
    assert(eval_comp(is_compound, n) == 0) by {
        reveal(eval_comp);
        lemma_eval_lt(cs_const(1), esb_left_tag(), n);
    };
    assert(eval_comp(check_eq_subst_process(), n) == eval_comp(esb_atomic_ok(), n)) by {
        reveal(eval_comp);
        lemma_eval_ifzero_then(is_compound, esb_atomic_ok(),
            CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()))),
                then_br: Box::new(esb_unary_ok()),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(cs_lt(cs_const(6), esb_left_tag())),
                    then_br: Box::new(esb_binary_ok()),
                    else_br: Box::new(esb_quant_ok()),
                }),
            }, n);
    };

    //  Term sub-components
    let lc = cs_snd(esb_left_node());
    let rc = cs_snd(esb_right_node());
    assert(eval_comp(lc, n) == unpair2(left_node)) by {
        reveal(eval_comp); lemma_eval_snd(esb_left_node(), n);
    };
    assert(eval_comp(rc, n) == unpair2(right_node)) by {
        reveal(eval_comp); lemma_eval_snd(esb_right_node(), n);
    };
    let lt1 = unpair1(unpair2(left_node));
    let lt2 = unpair2(unpair2(left_node));
    let rt1 = unpair1(unpair2(right_node));
    let rt2 = unpair2(unpair2(right_node));
    assert(eval_comp(cs_fst(lc), n) == lt1) by {
        reveal(eval_comp); lemma_eval_fst(lc, n);
    };
    assert(eval_comp(cs_snd(lc), n) == lt2) by {
        reveal(eval_comp); lemma_eval_snd(lc, n);
    };
    assert(eval_comp(cs_fst(rc), n) == rt1) by {
        reveal(eval_comp); lemma_eval_fst(rc, n);
    };
    assert(eval_comp(cs_snd(rc), n) == rt2) by {
        reveal(eval_comp); lemma_eval_snd(rc, n);
    };

    //  tags_match
    let tags_match = esb_tags_match();
    let tm_val: nat = if unpair1(left_node) == unpair1(right_node) { 1nat } else { 0nat };
    assert(eval_comp(tags_match, n) == tm_val) by {
        reveal(eval_comp); lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
    };

    //  t1: same + swap
    let t1_same_val: nat = if lt1 == rt1 { 1 } else { 0 };
    assert(eval_comp(cs_eq(cs_fst(lc), cs_fst(rc)), n) == t1_same_val) by {
        reveal(eval_comp); lemma_eval_eq(cs_fst(lc), cs_fst(rc), n);
    };
    let lt1_eq_x: nat = if lt1 == x_enc { 1 } else { 0 };
    let rt1_eq_y: nat = if rt1 == y_enc { 1 } else { 0 };
    assert(eval_comp(cs_eq(cs_fst(lc), esb_x_enc()), n) == lt1_eq_x) by {
        reveal(eval_comp); lemma_eval_eq(cs_fst(lc), esb_x_enc(), n);
    };
    assert(eval_comp(cs_eq(cs_fst(rc), esb_y_enc()), n) == rt1_eq_y) by {
        reveal(eval_comp); lemma_eval_eq(cs_fst(rc), esb_y_enc(), n);
    };
    let t1_swap_cs = cs_and(cs_eq(cs_fst(lc), esb_x_enc()), cs_eq(cs_fst(rc), esb_y_enc()));
    let t1_swap_val: nat = lt1_eq_x * rt1_eq_y;
    assert(eval_comp(t1_swap_cs, n) == t1_swap_val) by {
        reveal(eval_comp);
        lemma_eval_cs_and(cs_eq(cs_fst(lc), esb_x_enc()), cs_eq(cs_fst(rc), esb_y_enc()), n);
    };
    let t1_ok_cs = cs_or(cs_eq(cs_fst(lc), cs_fst(rc)), t1_swap_cs);
    let t1_ok_val: nat = t1_same_val + t1_swap_val;
    assert(eval_comp(t1_ok_cs, n) == t1_ok_val) by {
        reveal(eval_comp); lemma_eval_cs_or(cs_eq(cs_fst(lc), cs_fst(rc)), t1_swap_cs, n);
    };

    //  t2: same + swap
    let t2_same_val: nat = if lt2 == rt2 { 1 } else { 0 };
    assert(eval_comp(cs_eq(cs_snd(lc), cs_snd(rc)), n) == t2_same_val) by {
        reveal(eval_comp); lemma_eval_eq(cs_snd(lc), cs_snd(rc), n);
    };
    let lt2_eq_x: nat = if lt2 == x_enc { 1 } else { 0 };
    let rt2_eq_y: nat = if rt2 == y_enc { 1 } else { 0 };
    assert(eval_comp(cs_eq(cs_snd(lc), esb_x_enc()), n) == lt2_eq_x) by {
        reveal(eval_comp); lemma_eval_eq(cs_snd(lc), esb_x_enc(), n);
    };
    assert(eval_comp(cs_eq(cs_snd(rc), esb_y_enc()), n) == rt2_eq_y) by {
        reveal(eval_comp); lemma_eval_eq(cs_snd(rc), esb_y_enc(), n);
    };
    let t2_swap_cs = cs_and(cs_eq(cs_snd(lc), esb_x_enc()), cs_eq(cs_snd(rc), esb_y_enc()));
    let t2_swap_val: nat = lt2_eq_x * rt2_eq_y;
    assert(eval_comp(t2_swap_cs, n) == t2_swap_val) by {
        reveal(eval_comp);
        lemma_eval_cs_and(cs_eq(cs_snd(lc), esb_x_enc()), cs_eq(cs_snd(rc), esb_y_enc()), n);
    };
    let t2_ok_cs = cs_or(cs_eq(cs_snd(lc), cs_snd(rc)), t2_swap_cs);
    let t2_ok_val: nat = t2_same_val + t2_swap_val;
    assert(eval_comp(t2_ok_cs, n) == t2_ok_val) by {
        reveal(eval_comp); lemma_eval_cs_or(cs_eq(cs_snd(lc), cs_snd(rc)), t2_swap_cs, n);
    };

    //  Combine: pair(rest, tags_match * cs_and(t1_ok, t2_ok))
    let inner_val: nat = t1_ok_val * t2_ok_val;
    assert(eval_comp(cs_and(t1_ok_cs, t2_ok_cs), n) == inner_val) by {
        reveal(eval_comp); lemma_eval_cs_and(t1_ok_cs, t2_ok_cs, n);
    };
    let comb_val: nat = tm_val * inner_val;
    assert(eval_comp(cs_and(tags_match, cs_and(t1_ok_cs, t2_ok_cs)), n) == comb_val) by {
        reveal(eval_comp);
        lemma_eval_cs_and(tags_match, cs_and(t1_ok_cs, t2_ok_cs), n);
    };
    assert(eval_comp(esb_atomic_ok(), n) == pair(rest_val, comb_val)) by {
        reveal(eval_comp);
        lemma_eval_pair(esb_rest(), cs_and(tags_match, cs_and(t1_ok_cs, t2_ok_cs)), n);
    };

    //  Chain: step → process → atomic_ok → pair(rest, comb)
    assert(eval_comp(check_eq_subst_step(), n) == pair(rest_val, comb_val));
    lemma_unpair1_pair(rest_val, comb_val);
    lemma_unpair2_pair(rest_val, comb_val);

    //  Forward reasoning: if comb_val != 0, decompose the products
    if comb_val != 0 {
        assert(tm_val != 0 && inner_val != 0) by {
            if tm_val == 0 { assert(0nat * inner_val == 0) by (nonlinear_arith); }
            if inner_val == 0 { assert(tm_val * 0nat == 0) by (nonlinear_arith); }
        };
        assert(t1_ok_val != 0 && t2_ok_val != 0) by {
            if t1_ok_val == 0 { assert(0nat * t2_ok_val == 0) by (nonlinear_arith); }
            if t2_ok_val == 0 { assert(t1_ok_val * 0nat == 0) by (nonlinear_arith); }
        };
        //  t1_ok = t1_same + t1_swap != 0 → t1_same != 0 ∨ t1_swap != 0
        //  If t1_same != 0: lt1 == rt1 → compatible
        //  If t1_swap != 0: lt1==x_enc ∧ rt1==y_enc → compatible
        if t1_same_val != 0 {
            //  lt1 == rt1 → Var(lt1) == Var(rt1) → term compatible
        } else {
            //  t1_swap_val = lt1_eq_x * rt1_eq_y != 0
            assert(lt1_eq_x != 0 && rt1_eq_y != 0) by {
                if lt1_eq_x == 0 { assert(0nat * rt1_eq_y == 0) by (nonlinear_arith); }
                if rt1_eq_y == 0 { assert(lt1_eq_x * 0nat == 0) by (nonlinear_arith); }
            };
        }
        //  Same for t2
        if t2_same_val != 0 {} else {
            assert(lt2_eq_x != 0 && rt2_eq_y != 0) by {
                if lt2_eq_x == 0 { assert(0nat * rt2_eq_y == 0) by (nonlinear_arith); }
                if rt2_eq_y == 0 { assert(lt2_eq_x * 0nat == 0) by (nonlinear_arith); }
            };
        }
    }
}

} // verus!
