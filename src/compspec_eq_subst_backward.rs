use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;

verus! {

//  ====================================================================
//  Backward proof: check_eq_subst_pair accepts for compatible formula pairs
//  ====================================================================

//  Dispatch: when valid != 0 and stack non-empty, step evaluates to process block.
pub proof fn lemma_eq_subst_dispatch(
    counter: nat, entry_val: nat, rest: nat, valid: nat, s: nat,
)
    requires valid > 0, entry_val > 0,
    ensures ({
        let stack = pair(entry_val, rest);
        let acc = pair(stack, valid);
        let n = pair(counter, pair(acc, s));
        eval_comp(check_eq_subst_step(), n)
            == eval_comp(check_eq_subst_process(), n)
    }),
{
    let stack = pair(entry_val, rest);
    let acc = pair(stack, valid);
    let n = pair(counter, pair(acc, s));

    lemma_eval_br_acc(counter, acc, s);
    let valid_cs = cs_snd(br_acc());
    let stack_cs = cs_fst(br_acc());
    let fst_stack = cs_fst(stack_cs);

    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(stack, valid);
    lemma_eval_fst(stack_cs, n);
    lemma_unpair1_pair(stack, valid);
    lemma_eval_fst(cs_fst(br_acc()), n);
    lemma_unpair1_pair(entry_val, rest);

    lemma_eval_ifzero_else(valid_cs, br_acc(),
        CompSpec::IfZero {
            cond: Box::new(fst_stack),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_eq_subst_process()),
        }, n);
    lemma_eval_ifzero_else(fst_stack, br_acc(), check_eq_subst_process(), n);
}

//  Tag dispatch: navigate the is_compound / tag==2 / is_quantifier cascade.
proof fn lemma_esb_dispatch_atomic(n: nat, left_tag_val: nat)
    requires left_tag_val <= 1, eval_comp(esb_left_tag(), n) == left_tag_val,
    ensures eval_comp(check_eq_subst_process(), n) == eval_comp(esb_atomic_ok(), n),
{
    let is_compound = cs_lt(cs_const(1), esb_left_tag());
    lemma_eval_lt(cs_const(1), esb_left_tag(), n);
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
}

proof fn lemma_esb_dispatch_unary(n: nat, left_tag_val: nat)
    requires left_tag_val == 2, eval_comp(esb_left_tag(), n) == left_tag_val,
    ensures eval_comp(check_eq_subst_process(), n) == eval_comp(esb_unary_ok(), n),
{
    let is_compound = cs_lt(cs_const(1), esb_left_tag());
    let inner_dispatch = CompSpec::IfZero {
        cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()))),
        then_br: Box::new(esb_unary_ok()),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_lt(cs_const(6), esb_left_tag())),
            then_br: Box::new(esb_binary_ok()),
            else_br: Box::new(esb_quant_ok()),
        }),
    };
    lemma_eval_lt(cs_const(1), esb_left_tag(), n);
    lemma_eval_ifzero_else(is_compound, esb_atomic_ok(), inner_dispatch, n);
    //  Pred(Pred(2)) = 0 → unary
    let pp = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()));
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()), n);
    lemma_eval_comp(CompSpec::Pred, esb_left_tag(), n);
    lemma_eval_pred(2);
    lemma_eval_pred(1);
    lemma_eval_ifzero_then(pp, esb_unary_ok(),
        CompSpec::IfZero {
            cond: Box::new(cs_lt(cs_const(6), esb_left_tag())),
            then_br: Box::new(esb_binary_ok()),
            else_br: Box::new(esb_quant_ok()),
        }, n);
}

proof fn lemma_esb_dispatch_binary(n: nat, left_tag_val: nat)
    requires left_tag_val >= 3, left_tag_val <= 6, eval_comp(esb_left_tag(), n) == left_tag_val,
    ensures eval_comp(check_eq_subst_process(), n) == eval_comp(esb_binary_ok(), n),
{
    let is_compound = cs_lt(cs_const(1), esb_left_tag());
    let inner_dispatch = CompSpec::IfZero {
        cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()))),
        then_br: Box::new(esb_unary_ok()),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_lt(cs_const(6), esb_left_tag())),
            then_br: Box::new(esb_binary_ok()),
            else_br: Box::new(esb_quant_ok()),
        }),
    };
    lemma_eval_lt(cs_const(1), esb_left_tag(), n);
    lemma_eval_ifzero_else(is_compound, esb_atomic_ok(), inner_dispatch, n);
    let pp = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()));
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()), n);
    lemma_eval_comp(CompSpec::Pred, esb_left_tag(), n);
    lemma_eval_pred(left_tag_val);
    lemma_eval_pred((left_tag_val - 1) as nat);
    let inner2 = CompSpec::IfZero {
        cond: Box::new(cs_lt(cs_const(6), esb_left_tag())),
        then_br: Box::new(esb_binary_ok()),
        else_br: Box::new(esb_quant_ok()),
    };
    lemma_eval_ifzero_else(pp, esb_unary_ok(), inner2, n);
    lemma_eval_lt(cs_const(6), esb_left_tag(), n);
    lemma_eval_ifzero_then(cs_lt(cs_const(6), esb_left_tag()), esb_binary_ok(), esb_quant_ok(), n);
}

proof fn lemma_esb_dispatch_quant(n: nat, left_tag_val: nat)
    requires left_tag_val >= 7, eval_comp(esb_left_tag(), n) == left_tag_val,
    ensures eval_comp(check_eq_subst_process(), n) == eval_comp(esb_quant_ok(), n),
{
    let is_compound = cs_lt(cs_const(1), esb_left_tag());
    let inner_dispatch = CompSpec::IfZero {
        cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()))),
        then_br: Box::new(esb_unary_ok()),
        else_br: Box::new(CompSpec::IfZero {
            cond: Box::new(cs_lt(cs_const(6), esb_left_tag())),
            then_br: Box::new(esb_binary_ok()),
            else_br: Box::new(esb_quant_ok()),
        }),
    };
    lemma_eval_lt(cs_const(1), esb_left_tag(), n);
    lemma_eval_ifzero_else(is_compound, esb_atomic_ok(), inner_dispatch, n);
    let pp = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()));
    lemma_eval_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, esb_left_tag()), n);
    lemma_eval_comp(CompSpec::Pred, esb_left_tag(), n);
    lemma_eval_pred(left_tag_val);
    lemma_eval_pred((left_tag_val - 1) as nat);
    let inner2 = CompSpec::IfZero {
        cond: Box::new(cs_lt(cs_const(6), esb_left_tag())),
        then_br: Box::new(esb_binary_ok()),
        else_br: Box::new(esb_quant_ok()),
    };
    lemma_eval_ifzero_else(pp, esb_unary_ok(), inner2, n);
    lemma_eval_lt(cs_const(6), esb_left_tag(), n);
    lemma_eval_ifzero_else(cs_lt(cs_const(6), esb_left_tag()), esb_binary_ok(), esb_quant_ok(), n);
}

//  ====================================================================
//  Common extraction: establish eval values for shared sub-expressions.
//  ====================================================================

proof fn lemma_esb_extract(
    counter: nat, entry_val: nat, rest_val: nat, valid: nat,
    left_enc_s: nat, right_enc_s: nat, x_enc: nat, y_enc: nat,
    f1_enc: nat, f2_enc: nat,
)
    requires
        entry_val == pair(f1_enc, f2_enc) + 1,
        entry_val > 0,
    ensures ({
        let stack = pair(entry_val, rest_val);
        let acc = pair(stack, valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
        let n = pair(counter, pair(acc, s));
        eval_comp(esb_entry(), n) == pair(f1_enc, f2_enc) &&
        eval_comp(esb_rest(), n) == rest_val &&
        eval_comp(esb_left_node(), n) == f1_enc &&
        eval_comp(esb_right_node(), n) == f2_enc &&
        eval_comp(esb_left_tag(), n) == unpair1(f1_enc) &&
        eval_comp(esb_right_tag(), n) == unpair1(f2_enc) &&
        eval_comp(esb_x_enc(), n) == x_enc &&
        eval_comp(esb_y_enc(), n) == y_enc
    }),
{
    let stack = pair(entry_val, rest_val);
    let acc = pair(stack, valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    //  br_acc extraction
    lemma_eval_br_acc(counter, acc, s);
    lemma_eval_fst(br_acc(), n);
    lemma_unpair1_pair(stack, valid);

    //  stack components
    lemma_eval_fst(cs_fst(br_acc()), n);
    lemma_unpair1_pair(entry_val, rest_val);
    lemma_eval_snd(cs_fst(br_acc()), n);
    lemma_unpair2_pair(entry_val, rest_val);

    //  entry = Pred(stack_top)
    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
    lemma_eval_pred(entry_val);

    //  left_node, right_node
    lemma_eval_fst(esb_entry(), n);
    lemma_unpair1_pair(f1_enc, f2_enc);
    lemma_eval_snd(esb_entry(), n);
    lemma_unpair2_pair(f1_enc, f2_enc);

    //  tags
    lemma_eval_fst(esb_left_node(), n);
    lemma_eval_fst(esb_right_node(), n);

    //  xy extraction (4 snd from Id)
    lemma_eval_snd(CompSpec::Id, n);
    lemma_unpair2_pair(counter, pair(acc, s));
    lemma_eval_snd(cs_snd(CompSpec::Id), n);
    lemma_unpair2_pair(acc, s);
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), n);
    lemma_unpair2_pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), n);
    lemma_unpair2_pair(right_enc_s, pair(x_enc, y_enc));
    lemma_eval_fst(esb_xy_pair(), n);
    lemma_unpair1_pair(x_enc, y_enc);
    lemma_eval_snd(esb_xy_pair(), n);
    lemma_unpair2_pair(x_enc, y_enc);
}

//  ====================================================================
//  Chain: one step of iterate unfolds to step function result.
//  ====================================================================

proof fn esc_chain(fuel: nat, old_acc: nat, new_acc: nat, s: nat)
    requires fuel > 0,
        eval_comp(check_eq_subst_step(),
            pair((fuel - 1) as nat, pair(old_acc, s))) == new_acc,
    ensures compspec_iterate(check_eq_subst_step(), fuel, old_acc, s)
        == compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat, new_acc, s),
{
    lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, old_acc, s);
}

//  ====================================================================
//  Per-variant step helpers: prove step result for compatible pairs.
//  ====================================================================

//  Atomic (Eq/In): consumes entry, valid nonzero.
#[verifier::rlimit(500)]
pub proof fn lemma_eq_subst_step_atomic(
    f1: Formula, f2: Formula, x: Term, y: Term,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat,
)
    requires
        eq_subst_compatible(f1, f2, x, y),
        match f1 { Formula::Eq{..} => true, Formula::In{..} => true, _ => false },
        valid > 0,
    ensures ({
        let entry = pair(encode(f1), encode(f2));
        let stack = pair(entry + 1, rest_val);
        let acc = pair(stack, valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(encode_term(x), encode_term(y))));
        let n = pair(counter, pair(acc, s));
        let result = eval_comp(check_eq_subst_step(), n);
        unpair1(result) == rest_val && unpair2(result) != 0
    }),
{
    let x_enc = encode_term(x);
    let y_enc = encode_term(y);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let entry = pair(f1_enc, f2_enc);
    let entry_val = entry + 1;
    let stack = pair(entry_val, rest_val);
    let acc = pair(stack, valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    lemma_esb_extract(counter, entry_val, rest_val, valid, left_enc_s, right_enc_s, x_enc, y_enc, f1_enc, f2_enc);
    lemma_encode_is_pair(f1);
    lemma_encode_is_pair(f2);

    match f1 {
        Formula::Eq { left: l1, right: r1 } => { match f2 {
            Formula::Eq { left: l2, right: r2 } => {
                lemma_unpair1_pair(0nat, pair(encode_term(l1), encode_term(r1)));
                lemma_unpair1_pair(0nat, pair(encode_term(l2), encode_term(r2)));
                lemma_esb_dispatch_atomic(n, 0);

                //  Now eval_comp(check_eq_subst_step(), n) == eval_comp(esb_atomic_ok(), n)
                //  Evaluate esb_atomic_ok components
                lemma_eval_snd(esb_left_node(), n);
                lemma_unpair2_pair(0nat, pair(encode_term(l1), encode_term(r1)));
                lemma_eval_snd(esb_right_node(), n);
                lemma_unpair2_pair(0nat, pair(encode_term(l2), encode_term(r2)));

                let lc = cs_snd(esb_left_node());
                let rc = cs_snd(esb_right_node());
                lemma_eval_fst(lc, n);
                lemma_unpair1_pair(encode_term(l1), encode_term(r1));
                lemma_eval_snd(lc, n);
                lemma_unpair2_pair(encode_term(l1), encode_term(r1));
                lemma_eval_fst(rc, n);
                lemma_unpair1_pair(encode_term(l2), encode_term(r2));
                lemma_eval_snd(rc, n);
                lemma_unpair2_pair(encode_term(l2), encode_term(r2));

                //  tags_match, term checks, xy comparison
                lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
                let lt1_cs = cs_fst(lc); let rt1_cs = cs_fst(rc);
                let lt2_cs = cs_snd(lc); let rt2_cs = cs_snd(rc);
                lemma_eval_eq(lt1_cs, rt1_cs, n);
                lemma_eval_eq(lt1_cs, esb_x_enc(), n);
                lemma_eval_eq(rt1_cs, esb_y_enc(), n);
                lemma_eval_cs_and(cs_eq(lt1_cs, esb_x_enc()), cs_eq(rt1_cs, esb_y_enc()), n);
                lemma_eval_add(cs_eq(lt1_cs, rt1_cs), cs_and(cs_eq(lt1_cs, esb_x_enc()), cs_eq(rt1_cs, esb_y_enc())), n);
                lemma_eval_eq(lt2_cs, rt2_cs, n);
                lemma_eval_eq(lt2_cs, esb_x_enc(), n);
                lemma_eval_eq(rt2_cs, esb_y_enc(), n);
                lemma_eval_cs_and(cs_eq(lt2_cs, esb_x_enc()), cs_eq(rt2_cs, esb_y_enc()), n);
                lemma_eval_add(cs_eq(lt2_cs, rt2_cs), cs_and(cs_eq(lt2_cs, esb_x_enc()), cs_eq(rt2_cs, esb_y_enc())), n);
                let t1_ok = cs_or(cs_eq(lt1_cs, rt1_cs), cs_and(cs_eq(lt1_cs, esb_x_enc()), cs_eq(rt1_cs, esb_y_enc())));
                let t2_ok = cs_or(cs_eq(lt2_cs, rt2_cs), cs_and(cs_eq(lt2_cs, esb_x_enc()), cs_eq(rt2_cs, esb_y_enc())));
                lemma_eval_cs_and(t1_ok, t2_ok, n);
                lemma_eval_cs_and(esb_tags_match(), cs_and(t1_ok, t2_ok), n);
                lemma_eval_pair(esb_rest(), cs_and(esb_tags_match(), cs_and(t1_ok, t2_ok)), n);

                //  Nonzero valid from compatibility
                let lt1 = encode_term(l1); let rt1 = encode_term(l2);
                let lt2 = encode_term(r1); let rt2 = encode_term(r2);
                let t1s: nat = if lt1 == rt1 { 1 } else { 0 };
                let t1w: nat = (if lt1 == x_enc { 1nat } else { 0nat }) * (if rt1 == y_enc { 1nat } else { 0nat });
                let t2s: nat = if lt2 == rt2 { 1 } else { 0 };
                let t2w: nat = (if lt2 == x_enc { 1nat } else { 0nat }) * (if rt2 == y_enc { 1nat } else { 0nat });
                assert((t1s + t1w) != 0) by {
                    if l1 == l2 {} else {
                        assert(t1w != 0) by (nonlinear_arith) requires lt1 == x_enc, rt1 == y_enc,
                            t1w == (if lt1 == x_enc { 1nat } else { 0nat }) * (if rt1 == y_enc { 1nat } else { 0nat });
                    }
                }
                assert((t2s + t2w) != 0) by {
                    if r1 == r2 {} else {
                        assert(t2w != 0) by (nonlinear_arith) requires lt2 == x_enc, rt2 == y_enc,
                            t2w == (if lt2 == x_enc { 1nat } else { 0nat }) * (if rt2 == y_enc { 1nat } else { 0nat });
                    }
                }
                assert(1nat * ((t1s + t1w) * (t2s + t2w)) != 0) by (nonlinear_arith)
                    requires (t1s + t1w) != 0, (t2s + t2w) != 0;
                lemma_unpair1_pair(rest_val, 1nat * ((t1s + t1w) * (t2s + t2w)));
                lemma_unpair2_pair(rest_val, 1nat * ((t1s + t1w) * (t2s + t2w)));
            },
            _ => {},
        }},
        Formula::In { left: l1, right: r1 } => { match f2 {
            Formula::In { left: l2, right: r2 } => {
                lemma_unpair1_pair(1nat, pair(encode_term(l1), encode_term(r1)));
                lemma_unpair1_pair(1nat, pair(encode_term(l2), encode_term(r2)));
                lemma_esb_dispatch_atomic(n, 1);

                lemma_eval_snd(esb_left_node(), n);
                lemma_unpair2_pair(1nat, pair(encode_term(l1), encode_term(r1)));
                lemma_eval_snd(esb_right_node(), n);
                lemma_unpair2_pair(1nat, pair(encode_term(l2), encode_term(r2)));

                let lc = cs_snd(esb_left_node());
                let rc = cs_snd(esb_right_node());
                lemma_eval_fst(lc, n); lemma_unpair1_pair(encode_term(l1), encode_term(r1));
                lemma_eval_snd(lc, n); lemma_unpair2_pair(encode_term(l1), encode_term(r1));
                lemma_eval_fst(rc, n); lemma_unpair1_pair(encode_term(l2), encode_term(r2));
                lemma_eval_snd(rc, n); lemma_unpair2_pair(encode_term(l2), encode_term(r2));

                lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
                let lt1_cs = cs_fst(lc); let rt1_cs = cs_fst(rc);
                let lt2_cs = cs_snd(lc); let rt2_cs = cs_snd(rc);
                lemma_eval_eq(lt1_cs, rt1_cs, n);
                lemma_eval_eq(lt1_cs, esb_x_enc(), n);
                lemma_eval_eq(rt1_cs, esb_y_enc(), n);
                lemma_eval_cs_and(cs_eq(lt1_cs, esb_x_enc()), cs_eq(rt1_cs, esb_y_enc()), n);
                lemma_eval_add(cs_eq(lt1_cs, rt1_cs), cs_and(cs_eq(lt1_cs, esb_x_enc()), cs_eq(rt1_cs, esb_y_enc())), n);
                lemma_eval_eq(lt2_cs, rt2_cs, n);
                lemma_eval_eq(lt2_cs, esb_x_enc(), n);
                lemma_eval_eq(rt2_cs, esb_y_enc(), n);
                lemma_eval_cs_and(cs_eq(lt2_cs, esb_x_enc()), cs_eq(rt2_cs, esb_y_enc()), n);
                lemma_eval_add(cs_eq(lt2_cs, rt2_cs), cs_and(cs_eq(lt2_cs, esb_x_enc()), cs_eq(rt2_cs, esb_y_enc())), n);
                let t1_ok = cs_or(cs_eq(lt1_cs, rt1_cs), cs_and(cs_eq(lt1_cs, esb_x_enc()), cs_eq(rt1_cs, esb_y_enc())));
                let t2_ok = cs_or(cs_eq(lt2_cs, rt2_cs), cs_and(cs_eq(lt2_cs, esb_x_enc()), cs_eq(rt2_cs, esb_y_enc())));
                lemma_eval_cs_and(t1_ok, t2_ok, n);
                lemma_eval_cs_and(esb_tags_match(), cs_and(t1_ok, t2_ok), n);
                lemma_eval_pair(esb_rest(), cs_and(esb_tags_match(), cs_and(t1_ok, t2_ok)), n);

                let lt1 = encode_term(l1); let rt1 = encode_term(l2);
                let lt2 = encode_term(r1); let rt2 = encode_term(r2);
                let t1s: nat = if lt1 == rt1 { 1 } else { 0 };
                let t1w: nat = (if lt1 == x_enc { 1nat } else { 0nat }) * (if rt1 == y_enc { 1nat } else { 0nat });
                let t2s: nat = if lt2 == rt2 { 1 } else { 0 };
                let t2w: nat = (if lt2 == x_enc { 1nat } else { 0nat }) * (if rt2 == y_enc { 1nat } else { 0nat });
                assert((t1s + t1w) != 0) by {
                    if l1 == l2 {} else {
                        assert(t1w != 0) by (nonlinear_arith) requires lt1 == x_enc, rt1 == y_enc,
                            t1w == (if lt1 == x_enc { 1nat } else { 0nat }) * (if rt1 == y_enc { 1nat } else { 0nat });
                    }
                }
                assert((t2s + t2w) != 0) by {
                    if r1 == r2 {} else {
                        assert(t2w != 0) by (nonlinear_arith) requires lt2 == x_enc, rt2 == y_enc,
                            t2w == (if lt2 == x_enc { 1nat } else { 0nat }) * (if rt2 == y_enc { 1nat } else { 0nat });
                    }
                }
                assert(1nat * ((t1s + t1w) * (t2s + t2w)) != 0) by (nonlinear_arith)
                    requires (t1s + t1w) != 0, (t2s + t2w) != 0;
                lemma_unpair1_pair(rest_val, 1nat * ((t1s + t1w) * (t2s + t2w)));
                lemma_unpair2_pair(rest_val, 1nat * ((t1s + t1w) * (t2s + t2w)));
            },
            _ => {},
        }},
        _ => {},
    }
}

//  Compound step helper: for unary/binary/quantifier, shows exact new accumulator.
//  Unary (Not): pushes one sub-entry, valid = 1.
#[verifier::rlimit(300)]
pub proof fn lemma_eq_subst_step_unary(
    s1: Formula, s2: Formula, x: Term, y: Term,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat,
)
    requires
        eq_subst_compatible(Formula::Not { sub: Box::new(s1) }, Formula::Not { sub: Box::new(s2) }, x, y),
        valid > 0,
    ensures ({
        let f1 = Formula::Not { sub: Box::new(s1) };
        let f2 = Formula::Not { sub: Box::new(s2) };
        let entry = pair(encode(f1), encode(f2));
        let sub_entry = pair(encode(s1), encode(s2));
        let stack = pair(entry + 1, rest_val);
        let acc = pair(stack, valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(encode_term(x), encode_term(y))));
        let n = pair(counter, pair(acc, s));
        eval_comp(check_eq_subst_step(), n) == pair(pair(sub_entry + 1, rest_val), 1nat)
    }),
{
    let f1 = Formula::Not { sub: Box::new(s1) };
    let f2 = Formula::Not { sub: Box::new(s2) };
    let x_enc = encode_term(x);
    let y_enc = encode_term(y);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let entry = pair(f1_enc, f2_enc);
    let entry_val = entry + 1;
    let stack = pair(entry_val, rest_val);
    let acc = pair(stack, valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    lemma_esb_extract(counter, entry_val, rest_val, valid, left_enc_s, right_enc_s, x_enc, y_enc, f1_enc, f2_enc);
    lemma_encode_is_pair(f1);
    lemma_encode_is_pair(f2);
    lemma_unpair1_pair(2nat, encode(s1));
    lemma_unpair1_pair(2nat, encode(s2));

    lemma_esb_dispatch_unary(n, 2);

    //  Evaluate esb_unary_ok
    //  unary_entry = pair(snd(left_node), snd(right_node)) = pair(encode(s1), encode(s2))
    lemma_eval_snd(esb_left_node(), n);
    lemma_unpair2_pair(2nat, encode(s1));
    lemma_eval_snd(esb_right_node(), n);
    lemma_unpair2_pair(2nat, encode(s2));

    let ue_cs = cs_pair(cs_snd(esb_left_node()), cs_snd(esb_right_node()));
    lemma_eval_pair(cs_snd(esb_left_node()), cs_snd(esb_right_node()), n);

    //  Add(unary_entry, 1)
    let sub_entry = pair(encode(s1), encode(s2));
    lemma_eval_add(ue_cs, cs_const(1), n);

    //  tags_match = (2 == 2) = 1
    lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);

    //  Pair result
    let stack_part = cs_pair(CompSpec::Add { left: Box::new(ue_cs), right: Box::new(cs_const(1)) }, esb_rest());
    lemma_eval_pair(CompSpec::Add { left: Box::new(ue_cs), right: Box::new(cs_const(1)) }, esb_rest(), n);
    lemma_eval_pair(stack_part, esb_tags_match(), n);
}

//  Binary (And/Or/Implies/Iff): pushes two sub-entries, valid = 1.
#[verifier::rlimit(300)]
pub proof fn lemma_eq_subst_step_binary(
    f1: Formula, f2: Formula, x: Term, y: Term,
    l1: Formula, r1: Formula, l2: Formula, r2: Formula,
    tag: nat,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat,
)
    requires
        eq_subst_compatible(f1, f2, x, y),
        tag >= 3, tag <= 6,
        encode(f1) == pair(tag, pair(encode(l1), encode(r1))),
        encode(f2) == pair(tag, pair(encode(l2), encode(r2))),
        valid > 0,
    ensures ({
        let entry = pair(encode(f1), encode(f2));
        let el = pair(encode(l1), encode(l2));
        let er = pair(encode(r1), encode(r2));
        let stack = pair(entry + 1, rest_val);
        let acc = pair(stack, valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(encode_term(x), encode_term(y))));
        let n = pair(counter, pair(acc, s));
        eval_comp(check_eq_subst_step(), n) == pair(pair(el + 1, pair(er + 1, rest_val)), 1nat)
    }),
{
    let x_enc = encode_term(x);
    let y_enc = encode_term(y);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let entry = pair(f1_enc, f2_enc);
    let entry_val = entry + 1;
    let stack = pair(entry_val, rest_val);
    let acc = pair(stack, valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    lemma_esb_extract(counter, entry_val, rest_val, valid, left_enc_s, right_enc_s, x_enc, y_enc, f1_enc, f2_enc);
    lemma_unpair1_pair(tag, pair(encode(l1), encode(r1)));
    lemma_unpair1_pair(tag, pair(encode(l2), encode(r2)));

    lemma_esb_dispatch_binary(n, tag);

    //  Evaluate esb_binary_ok
    lemma_eval_snd(esb_left_node(), n);
    lemma_unpair2_pair(tag, pair(encode(l1), encode(r1)));
    lemma_eval_snd(esb_right_node(), n);
    lemma_unpair2_pair(tag, pair(encode(l2), encode(r2)));

    let lc = cs_snd(esb_left_node());
    let rc = cs_snd(esb_right_node());
    lemma_eval_fst(lc, n);
    lemma_unpair1_pair(encode(l1), encode(r1));
    lemma_eval_snd(lc, n);
    lemma_unpair2_pair(encode(l1), encode(r1));
    lemma_eval_fst(rc, n);
    lemma_unpair1_pair(encode(l2), encode(r2));
    lemma_eval_snd(rc, n);
    lemma_unpair2_pair(encode(l2), encode(r2));

    //  entry_l, entry_r
    let el_cs = cs_pair(cs_fst(lc), cs_fst(rc));
    let er_cs = cs_pair(cs_snd(lc), cs_snd(rc));
    lemma_eval_pair(cs_fst(lc), cs_fst(rc), n);
    lemma_eval_pair(cs_snd(lc), cs_snd(rc), n);

    //  Add + 1
    lemma_eval_add(el_cs, cs_const(1), n);
    lemma_eval_add(er_cs, cs_const(1), n);

    //  tags_match
    lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);

    //  Assemble result
    let el = pair(encode(l1), encode(l2));
    let er = pair(encode(r1), encode(r2));
    let er_plus = CompSpec::Add { left: Box::new(er_cs), right: Box::new(cs_const(1)) };
    lemma_eval_pair(er_plus, esb_rest(), n);
    let el_plus = CompSpec::Add { left: Box::new(el_cs), right: Box::new(cs_const(1)) };
    let inner_stack = cs_pair(er_plus, esb_rest());
    lemma_eval_pair(el_plus, inner_stack, n);
    let full_stack = cs_pair(el_plus, inner_stack);
    lemma_eval_pair(full_stack, esb_tags_match(), n);
}

//  Quantifier (Forall/Exists): pushes one sub-entry, valid = 1 when bvars match.
#[verifier::rlimit(300)]
pub proof fn lemma_eq_subst_step_quant(
    f1: Formula, f2: Formula, x: Term, y: Term,
    v: nat, s1: Formula, s2: Formula,
    tag: nat,
    rest_val: nat, valid: nat, counter: nat,
    left_enc_s: nat, right_enc_s: nat,
)
    requires
        eq_subst_compatible(f1, f2, x, y),
        tag >= 7,
        encode(f1) == pair(tag, pair(v, encode(s1))),
        encode(f2) == pair(tag, pair(v, encode(s2))),
        valid > 0,
    ensures ({
        let entry = pair(encode(f1), encode(f2));
        let sub_entry = pair(encode(s1), encode(s2));
        let stack = pair(entry + 1, rest_val);
        let acc = pair(stack, valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(encode_term(x), encode_term(y))));
        let n = pair(counter, pair(acc, s));
        eval_comp(check_eq_subst_step(), n) == pair(pair(sub_entry + 1, rest_val), 1nat)
    }),
{
    let x_enc = encode_term(x);
    let y_enc = encode_term(y);
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let entry = pair(f1_enc, f2_enc);
    let entry_val = entry + 1;
    let stack = pair(entry_val, rest_val);
    let acc = pair(stack, valid);
    let s = pair(left_enc_s, pair(right_enc_s, pair(x_enc, y_enc)));
    let n = pair(counter, pair(acc, s));

    lemma_eq_subst_dispatch(counter, entry_val, rest_val, valid, s);
    lemma_esb_extract(counter, entry_val, rest_val, valid, left_enc_s, right_enc_s, x_enc, y_enc, f1_enc, f2_enc);
    lemma_unpair1_pair(tag, pair(v, encode(s1)));
    lemma_unpair1_pair(tag, pair(v, encode(s2)));

    lemma_esb_dispatch_quant(n, tag);

    //  Evaluate esb_quant_ok
    lemma_eval_snd(esb_left_node(), n);
    lemma_unpair2_pair(tag, pair(v, encode(s1)));
    lemma_eval_snd(esb_right_node(), n);
    lemma_unpair2_pair(tag, pair(v, encode(s2)));

    let lsub = cs_snd(esb_left_node());
    let rsub = cs_snd(esb_right_node());
    lemma_eval_fst(lsub, n);
    lemma_unpair1_pair(v, encode(s1));
    lemma_eval_fst(rsub, n);
    lemma_unpair1_pair(v, encode(s2));
    lemma_eval_snd(lsub, n);
    lemma_unpair2_pair(v, encode(s1));
    lemma_eval_snd(rsub, n);
    lemma_unpair2_pair(v, encode(s2));

    //  quant_entry
    let qe_cs = cs_pair(cs_snd(cs_snd(esb_left_node())), cs_snd(cs_snd(esb_right_node())));
    lemma_eval_pair(cs_snd(lsub), cs_snd(rsub), n);
    lemma_eval_add(qe_cs, cs_const(1), n);

    //  tags_match * bv_match = 1 * 1 = 1
    lemma_eval_eq(esb_left_tag(), esb_right_tag(), n);
    lemma_eval_eq(cs_fst(lsub), cs_fst(rsub), n);
    lemma_eval_cs_and(esb_tags_match(), cs_eq(cs_fst(lsub), cs_fst(rsub)), n);

    //  Assemble
    let qe_plus = CompSpec::Add { left: Box::new(qe_cs), right: Box::new(cs_const(1)) };
    lemma_eval_pair(qe_plus, esb_rest(), n);
    let stack_part = cs_pair(qe_plus, esb_rest());
    let valid_cs = cs_and(esb_tags_match(), cs_eq(cs_fst(lsub), cs_fst(rsub)));
    lemma_eval_pair(stack_part, valid_cs, n);
}

//  ====================================================================
//  Iterate stability: when stack is empty and valid != 0, iterate is a no-op.
//  ====================================================================

proof fn lemma_eq_subst_step_empty(counter: nat, stack: nat, valid: nat, s: nat)
    requires unpair1(stack) == 0, valid != 0,
    ensures eval_comp(check_eq_subst_step(), pair(counter, pair(pair(stack, valid), s)))
        == pair(stack, valid),
{
    let acc = pair(stack, valid);
    let n = pair(counter, pair(acc, s));
    lemma_eval_br_acc(counter, acc, s);
    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(stack, valid);
    lemma_eval_fst(br_acc(), n);
    lemma_unpair1_pair(stack, valid);
    lemma_eval_fst(cs_fst(br_acc()), n);
    //  valid != 0 → else branch; fst(stack) = 0 → then branch → return acc
    let valid_cs = cs_snd(br_acc());
    let fst_stack = cs_fst(cs_fst(br_acc()));
    lemma_eval_ifzero_else(valid_cs, br_acc(),
        CompSpec::IfZero {
            cond: Box::new(fst_stack),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_eq_subst_process()),
        }, n);
    lemma_eval_ifzero_then(fst_stack, br_acc(), check_eq_subst_process(), n);
}

proof fn lemma_iterate_empty_stable(fuel: nat, stack: nat, valid: nat, s: nat)
    requires unpair1(stack) == 0, valid != 0,
    ensures compspec_iterate(check_eq_subst_step(), fuel, pair(stack, valid), s)
        == pair(stack, valid),
    decreases fuel,
{
    if fuel > 0 {
        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, pair(stack, valid), s);
        lemma_eq_subst_step_empty((fuel - 1) as nat, stack, valid, s);
        lemma_iterate_empty_stable((fuel - 1) as nat, stack, valid, s);
    }
}

//  ====================================================================
//  Main traversal: structural induction on f1.
//  After formula_size(f1) steps, the entry is fully consumed.
//  ====================================================================

#[verifier::rlimit(500)]
pub proof fn lemma_eq_subst_walk(
    f1: Formula, f2: Formula, x: Term, y: Term,
    rest: nat, valid: nat, fuel: nat,
    left_enc_s: nat, right_enc_s: nat,
)
    requires
        eq_subst_compatible(f1, f2, x, y),
        valid != 0,
        fuel >= formula_size(f1),
    ensures ({
        let entry = pair(encode(f1), encode(f2));
        let acc = pair(pair(entry + 1, rest), valid);
        let s = pair(left_enc_s, pair(right_enc_s, pair(encode_term(x), encode_term(y))));
        exists|v: nat| v != 0 &&
            compspec_iterate(check_eq_subst_step(), fuel, acc, s)
            == compspec_iterate(check_eq_subst_step(), (fuel - formula_size(f1)) as nat,
                pair(rest, v), s)
    }),
    decreases f1,
{
    let entry = pair(encode(f1), encode(f2));
    let entry_val = entry + 1;
    let s = pair(left_enc_s, pair(right_enc_s, pair(encode_term(x), encode_term(y))));
    let acc = pair(pair(entry_val, rest), valid);

    lemma_formula_size_pos(f1);

    match f1 {
        Formula::Eq { left: l1, right: r1 } => { match f2 {
            Formula::Eq { left: l2, right: r2 } => {
                //  One step: atomic, consumes entry
                lemma_eq_subst_step_atomic(f1, f2, x, y, rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let result = eval_comp(check_eq_subst_step(), pair((fuel-1) as nat, pair(acc, s)));
                lemma_pair_surjective(result);
                esc_chain(fuel, acc, result, s);
            },
            _ => {},
        }},
        Formula::In { left: l1, right: r1 } => { match f2 {
            Formula::In { left: l2, right: r2 } => {
                lemma_eq_subst_step_atomic(f1, f2, x, y, rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let result = eval_comp(check_eq_subst_step(), pair((fuel-1) as nat, pair(acc, s)));
                lemma_pair_surjective(result);
                esc_chain(fuel, acc, result, s);
            },
            _ => {},
        }},
        Formula::Not { sub: s1 } => { match f2 {
            Formula::Not { sub: s2 } => {
                //  One step: pushes sub-entry, valid = 1
                lemma_eq_subst_step_unary(*s1, *s2, x, y, rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let sub_entry = pair(encode(*s1), encode(*s2));
                let new_acc = pair(pair(sub_entry + 1, rest), 1nat);
                esc_chain(fuel, acc, new_acc, s);
                //  IH on sub: consume sub_entry in formula_size(s1) steps
                lemma_eq_subst_walk(*s1, *s2, x, y, rest, 1nat, (fuel - 1) as nat, left_enc_s, right_enc_s);
            },
            _ => {},
        }},
        Formula::And { left: l1, right: r1 } => { match f2 {
            Formula::And { left: l2, right: r2 } => {
                lemma_encode_is_pair(f1);
                lemma_encode_is_pair(f2);
                lemma_eq_subst_step_binary(f1, f2, x, y, *l1, *r1, *l2, *r2, 3,
                    rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let el = pair(encode(*l1), encode(*l2));
                let er = pair(encode(*r1), encode(*r2));
                let new_acc = pair(pair(el + 1, pair(er + 1, rest)), 1nat);
                esc_chain(fuel, acc, new_acc, s);
                //  IH on left: consume left entry
                lemma_eq_subst_walk(*l1, *l2, x, y, pair(er + 1, rest), 1nat,
                    (fuel - 1) as nat, left_enc_s, right_enc_s);
                //  After left IH: some v1 != 0, remaining fuel = fuel-1-size(l1)
                let v1: nat = choose|v: nat| v != 0 &&
                    compspec_iterate(check_eq_subst_step(), (fuel-1) as nat, new_acc, s)
                    == #[trigger] compspec_iterate(check_eq_subst_step(), (fuel - 1 - formula_size(*l1)) as nat,
                        pair(pair(er + 1, rest), v), s);
                //  IH on right: consume right entry
                lemma_eq_subst_walk(*r1, *r2, x, y, rest, v1,
                    (fuel - 1 - formula_size(*l1)) as nat, left_enc_s, right_enc_s);
            },
            _ => {},
        }},
        Formula::Or { left: l1, right: r1 } => { match f2 {
            Formula::Or { left: l2, right: r2 } => {
                lemma_encode_is_pair(f1);
                lemma_encode_is_pair(f2);
                lemma_eq_subst_step_binary(f1, f2, x, y, *l1, *r1, *l2, *r2, 4,
                    rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let el = pair(encode(*l1), encode(*l2));
                let er = pair(encode(*r1), encode(*r2));
                let new_acc = pair(pair(el + 1, pair(er + 1, rest)), 1nat);
                esc_chain(fuel, acc, new_acc, s);
                lemma_eq_subst_walk(*l1, *l2, x, y, pair(er + 1, rest), 1nat,
                    (fuel - 1) as nat, left_enc_s, right_enc_s);
                let v1: nat = choose|v: nat| v != 0 &&
                    compspec_iterate(check_eq_subst_step(), (fuel-1) as nat, new_acc, s)
                    == #[trigger] compspec_iterate(check_eq_subst_step(), (fuel - 1 - formula_size(*l1)) as nat,
                        pair(pair(er + 1, rest), v), s);
                lemma_eq_subst_walk(*r1, *r2, x, y, rest, v1,
                    (fuel - 1 - formula_size(*l1)) as nat, left_enc_s, right_enc_s);
            },
            _ => {},
        }},
        Formula::Implies { left: l1, right: r1 } => { match f2 {
            Formula::Implies { left: l2, right: r2 } => {
                lemma_encode_is_pair(f1);
                lemma_encode_is_pair(f2);
                lemma_eq_subst_step_binary(f1, f2, x, y, *l1, *r1, *l2, *r2, 5,
                    rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let el = pair(encode(*l1), encode(*l2));
                let er = pair(encode(*r1), encode(*r2));
                let new_acc = pair(pair(el + 1, pair(er + 1, rest)), 1nat);
                esc_chain(fuel, acc, new_acc, s);
                lemma_eq_subst_walk(*l1, *l2, x, y, pair(er + 1, rest), 1nat,
                    (fuel - 1) as nat, left_enc_s, right_enc_s);
                let v1: nat = choose|v: nat| v != 0 &&
                    compspec_iterate(check_eq_subst_step(), (fuel-1) as nat, new_acc, s)
                    == #[trigger] compspec_iterate(check_eq_subst_step(), (fuel - 1 - formula_size(*l1)) as nat,
                        pair(pair(er + 1, rest), v), s);
                lemma_eq_subst_walk(*r1, *r2, x, y, rest, v1,
                    (fuel - 1 - formula_size(*l1)) as nat, left_enc_s, right_enc_s);
            },
            _ => {},
        }},
        Formula::Iff { left: l1, right: r1 } => { match f2 {
            Formula::Iff { left: l2, right: r2 } => {
                lemma_encode_is_pair(f1);
                lemma_encode_is_pair(f2);
                lemma_eq_subst_step_binary(f1, f2, x, y, *l1, *r1, *l2, *r2, 6,
                    rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let el = pair(encode(*l1), encode(*l2));
                let er = pair(encode(*r1), encode(*r2));
                let new_acc = pair(pair(el + 1, pair(er + 1, rest)), 1nat);
                esc_chain(fuel, acc, new_acc, s);
                lemma_eq_subst_walk(*l1, *l2, x, y, pair(er + 1, rest), 1nat,
                    (fuel - 1) as nat, left_enc_s, right_enc_s);
                let v1: nat = choose|v: nat| v != 0 &&
                    compspec_iterate(check_eq_subst_step(), (fuel-1) as nat, new_acc, s)
                    == #[trigger] compspec_iterate(check_eq_subst_step(), (fuel - 1 - formula_size(*l1)) as nat,
                        pair(pair(er + 1, rest), v), s);
                lemma_eq_subst_walk(*r1, *r2, x, y, rest, v1,
                    (fuel - 1 - formula_size(*l1)) as nat, left_enc_s, right_enc_s);
            },
            _ => {},
        }},
        Formula::Forall { var: v1, sub: sub1 } => { match f2 {
            Formula::Forall { var: v2, sub: sub2 } => {
                lemma_encode_is_pair(f1);
                lemma_encode_is_pair(f2);
                lemma_eq_subst_step_quant(f1, f2, x, y, v1, *sub1, *sub2, 7,
                    rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let sub_entry = pair(encode(*sub1), encode(*sub2));
                let new_acc = pair(pair(sub_entry + 1, rest), 1nat);
                esc_chain(fuel, acc, new_acc, s);
                lemma_eq_subst_walk(*sub1, *sub2, x, y, rest, 1nat,
                    (fuel - 1) as nat, left_enc_s, right_enc_s);
            },
            _ => {},
        }},
        Formula::Exists { var: v1, sub: sub1 } => { match f2 {
            Formula::Exists { var: v2, sub: sub2 } => {
                lemma_encode_is_pair(f1);
                lemma_encode_is_pair(f2);
                lemma_eq_subst_step_quant(f1, f2, x, y, v1, *sub1, *sub2, 8,
                    rest, valid, (fuel-1) as nat, left_enc_s, right_enc_s);
                let sub_entry = pair(encode(*sub1), encode(*sub2));
                let new_acc = pair(pair(sub_entry + 1, rest), 1nat);
                esc_chain(fuel, acc, new_acc, s);
                lemma_eq_subst_walk(*sub1, *sub2, x, y, rest, 1nat,
                    (fuel - 1) as nat, left_enc_s, right_enc_s);
            },
            _ => {},
        }},
    }
}

//  ====================================================================
//  Wrapper: check_eq_subst_pair accepts for compatible pairs.
//  ====================================================================

pub proof fn lemma_check_eq_subst_pair_backward(
    f1: Formula, f2: Formula, x: Term, y: Term,
)
    requires eq_subst_compatible(f1, f2, x, y),
    ensures eval_comp(check_eq_subst_pair(),
        pair(encode(f1), pair(encode(f2), pair(encode_term(x), encode_term(y))))) != 0,
{
    let f1_enc = encode(f1);
    let f2_enc = encode(f2);
    let x_enc = encode_term(x);
    let y_enc = encode_term(y);
    let input = pair(f1_enc, pair(f2_enc, pair(x_enc, y_enc)));

    //  Unfold check_eq_subst_pair to BoundedRec
    let left_enc_cs = cs_fst(CompSpec::Id);
    let right_enc_cs = cs_fst(cs_snd(CompSpec::Id));
    let entry_cs = cs_pair(left_enc_cs, right_enc_cs);

    lemma_eval_bounded_rec(
        left_enc_cs,
        cs_pair(
            cs_pair(CompSpec::Add { left: Box::new(entry_cs), right: Box::new(cs_const(1)) }, cs_const(0)),
            cs_const(1)),
        check_eq_subst_step(),
        input);

    //  Fuel = f1_enc
    lemma_eval_fst(CompSpec::Id, input);

    //  Base evaluation
    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(f1_enc, pair(f2_enc, pair(x_enc, y_enc)));
    lemma_unpair1_pair(f2_enc, pair(x_enc, y_enc));
    lemma_eval_pair(left_enc_cs, right_enc_cs, input);
    let entry = pair(f1_enc, f2_enc);
    lemma_eval_add(entry_cs, cs_const(1), input);
    lemma_eval_pair(CompSpec::Add { left: Box::new(entry_cs), right: Box::new(cs_const(1)) }, cs_const(0), input);
    lemma_eval_pair(
        cs_pair(CompSpec::Add { left: Box::new(entry_cs), right: Box::new(cs_const(1)) }, cs_const(0)),
        cs_const(1), input);

    let base_val = pair(pair(entry + 1, 0nat), 1nat);
    let fuel = f1_enc;

    if fuel == 0 {
        //  Zero steps: result = base, valid = 1
        lemma_eval_comp(cs_snd(CompSpec::Id),
            CompSpec::BoundedRec {
                count_fn: Box::new(left_enc_cs),
                base: Box::new(cs_pair(
                    cs_pair(CompSpec::Add { left: Box::new(entry_cs), right: Box::new(cs_const(1)) }, cs_const(0)),
                    cs_const(1))),
                step: Box::new(check_eq_subst_step()),
            }, input);
        lemma_eval_snd(CompSpec::Id, base_val);
        lemma_unpair2_pair(pair(entry + 1, 0nat), 1nat);
    } else {
        //  fuel > 0: use traversal
        lemma_encode_ge_formula_size(f1);
        lemma_eq_subst_compatible_same_size(f1, f2, x, y);

        lemma_eq_subst_walk(f1, f2, x, y, 0nat, 1nat, fuel,
            f1_enc, f2_enc);

        //  After walk: remaining fuel, stack = 0, valid = v != 0
        let v: nat = choose|v: nat| v != 0 &&
            compspec_iterate(check_eq_subst_step(), fuel, base_val, input)
            == compspec_iterate(check_eq_subst_step(), (fuel - formula_size(f1)) as nat,
                pair(0nat, v), input);

        //  Stack empty: iterate is stable
        lemma_unpair1_pair(0nat, v);
        lemma_iterate_empty_stable((fuel - formula_size(f1)) as nat, 0nat, v, input);

        //  Final result: pair(0, v), extract valid
        lemma_eval_comp(cs_snd(CompSpec::Id),
            CompSpec::BoundedRec {
                count_fn: Box::new(left_enc_cs),
                base: Box::new(cs_pair(
                    cs_pair(CompSpec::Add { left: Box::new(entry_cs), right: Box::new(cs_const(1)) }, cs_const(0)),
                    cs_const(1))),
                step: Box::new(check_eq_subst_step()),
            }, input);
        lemma_eval_snd(CompSpec::Id, pair(0nat, v));
        lemma_unpair2_pair(0nat, v);
    }
}

} //  verus!
