use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::*;

verus! {

///  Extract accumulator components from check_subst BoundedRec step input.
///  Step input: pair(iter, pair(acc, orig)) where acc = pair(stack, pair(valid, pair(t_enc, t_set)))
pub proof fn lemma_subst_acc_extract(
    i: nat, stack: nat, valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    ensures ({
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(br_acc(), input) == acc &&
        eval_comp(cs_fst(br_acc()), input) == stack &&
        eval_comp(cs_fst(cs_snd(br_acc())), input) == valid
    }),
{
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));
    lemma_eval_br_acc(i, acc, orig);
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
    lemma_eval_fst(cs_snd(br_acc()), input);
    lemma_unpair1_pair(valid, pair(t_enc, t_set));
}

///  Dispatch: when valid > 0 and stack non-empty, check_subst_step dispatches
///  to check_subst_process_pair. Shows the outer two IfZero layers.
pub proof fn lemma_subst_step_dispatch(
    i: nat, entry_plus_1: nat, rest: nat, valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        entry_plus_1 > 0,
    ensures ({
        let stack = pair(entry_plus_1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(check_subst_step(), input)
            == eval_comp(check_subst_process_pair(), input)
    }),
{
    let stack = pair(entry_plus_1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));

    lemma_subst_acc_extract(i, stack, valid, t_enc, t_set, phi_enc, result_enc, var);
    let valid_cs = cs_fst(cs_snd(br_acc()));
    let stack_cs = cs_fst(br_acc());
    let fst_stack = cs_fst(stack_cs);
    lemma_eval_fst(stack_cs, input);
    lemma_unpair1_pair(entry_plus_1, rest);

    //  valid > 0 → outer IfZero else branch
    //  fst(stack) = entry_plus_1 > 0 → inner IfZero else branch → process_pair
    lemma_eval_ifzero_else(fst_stack, br_acc(), check_subst_process_pair(), input);
    lemma_eval_ifzero_else(valid_cs, br_acc(),
        CompSpec::IfZero {
            cond: Box::new(fst_stack),
            then_br: Box::new(br_acc()),
            else_br: Box::new(check_subst_process_pair()),
        }, input);
}

///  For the atomic case (tag 0): show process_pair dispatches to atomic_terms
///  and atomic_terms produces pair(rest, pair(valid, pair(t_enc, t_set)))
///  (when phi_tag == result_tag).
///
///  This is the most critical per-variant step lemma.
///  Shows that process_pair on input with phi_tag==0 evaluates to
///  the check_subst_atomic_terms result, which only multiplies valid
///  by cs_eq(phi_tag, result_tag) * 1.
pub proof fn lemma_subst_process_pair_atomic_eq(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) == 0,  //  Eq tag
        unpair1(result_node) == 0,  //  Eq tag (tags match)
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(check_subst_process_pair(), input)
            == pair(rest, pair(1nat, pair(t_enc, t_set)))
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));

    //  First, establish what br_acc sub-expressions evaluate to on this input
    assert(eval_comp(br_acc(), input) == acc) by {
        reveal(eval_comp);
        lemma_eval_br_acc(i, acc, orig);
    }
    assert(eval_comp(cs_fst(br_acc()), input) == stack) by {
        reveal(eval_comp);
        lemma_eval_fst(br_acc(), input);
        lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    }

    //  entry = Pred(fst(stack)) = Pred(entry + 1) = entry
    assert(eval_comp(cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc()))), input) == entry) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(br_acc()), input);
        lemma_unpair1_pair(entry + 1, rest);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
        lemma_eval_pred(entry + 1);
    }

    //  rest = snd(stack)
    assert(eval_comp(cs_snd(cs_fst(br_acc())), input) == rest) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_fst(br_acc()), input);
        lemma_unpair2_pair(entry + 1, rest);
    }

    //  phi_node = fst(entry), result_node = snd(entry)
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node) by {
        reveal(eval_comp);
        lemma_eval_fst(entry_cs, input);
        lemma_unpair1_pair(phi_node, result_node);
    }
    assert(eval_comp(cs_snd(entry_cs), input) == result_node) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_unpair2_pair(phi_node, result_node);
    }

    //  phi_tag = fst(phi_node) = 0
    assert(eval_comp(cs_fst(cs_fst(entry_cs)), input) == 0) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(entry_cs), input);
    }

    //  phi_tag == 0 → IfZero then branch → check_subst_atomic_terms
    //  Now: check_subst_atomic_terms on this input produces:
    //  cs_pair(rest_cs, cs_pair(cs_and(cs_eq(phi_tag_cs, result_tag_cs), 1), cs_pair(t_enc_cs, t_set_cs)))
    //  = pair(rest, pair(valid * (0 == 0 ? 1 : 0) * 1, pair(t_enc, t_set)))
    //  = pair(rest, pair(valid * 1 * 1, pair(t_enc, t_set)))
    //  = pair(rest, pair(valid, pair(t_enc, t_set)))

    //  result_tag = fst(result_node) = 0
    assert(eval_comp(cs_fst(cs_snd(entry_cs)), input) == 0) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_eval_fst(cs_snd(entry_cs), input);
        lemma_unpair1_pair(result_node, 0nat);
        //  Hmm, this isn't right. result_node is a nat, fst(result_node) should be unpair1(result_node)
        //  and we know unpair1(result_node) == 0 from precondition.
    }

    //  Actually, the check_subst_atomic_terms references are expressed in terms of
    //  the SAME br_acc() + cs_fst(stack) pattern. Since check_subst_process_pair
    //  and check_subst_atomic_terms both reconstruct these expressions identically,
    //  they evaluate to the same values.

    //  cs_eq(phi_tag, result_tag) where both are 0 → 1
    let phi_tag_cs = cs_fst(cs_fst(entry_cs));
    let result_tag_cs = cs_fst(cs_snd(entry_cs));
    assert(eval_comp(cs_eq(phi_tag_cs, result_tag_cs), input) == 1) by {
        reveal(eval_comp);
        lemma_eval_eq(phi_tag_cs, result_tag_cs, input);
    }

    //  cs_and(cs_eq(phi_tag, result_tag), cs_const(1)) = 1 * 1 = 1
    assert(eval_comp(cs_and(cs_eq(phi_tag_cs, result_tag_cs), cs_const(1)), input) == 1) by {
        reveal(eval_comp);
        lemma_eval_cs_and(cs_eq(phi_tag_cs, result_tag_cs), cs_const(1), input);
    }

    //  t_enc and t_set extraction
    assert(eval_comp(cs_fst(cs_snd(cs_snd(br_acc()))), input) == t_enc
        && eval_comp(cs_snd(cs_snd(cs_snd(br_acc()))), input) == t_set) by {
        reveal(eval_comp);
        lemma_eval_snd(br_acc(), input);
        lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
        lemma_eval_snd(cs_snd(br_acc()), input);
        lemma_unpair2_pair(valid, pair(t_enc, t_set));
        lemma_eval_fst(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair1_pair(t_enc, t_set);
        lemma_eval_snd(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair2_pair(t_enc, t_set);
    }

    //  Now compose the full check_subst_atomic_terms result
    let rest_cs = cs_snd(cs_fst(br_acc()));
    let t_enc_cs = cs_fst(cs_snd(cs_snd(br_acc())));
    let t_set_cs = cs_snd(cs_snd(cs_snd(br_acc())));
    let valid_new = cs_and(cs_eq(phi_tag_cs, result_tag_cs), cs_const(1));

    assert(eval_comp(cs_pair(t_enc_cs, t_set_cs), input) == pair(t_enc, t_set)) by {
        reveal(eval_comp);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
    }
    assert(eval_comp(cs_pair(valid_new, cs_pair(t_enc_cs, t_set_cs)), input)
        == pair(1nat, pair(t_enc, t_set))) by {
        reveal(eval_comp);
        lemma_eval_pair(valid_new, cs_pair(t_enc_cs, t_set_cs), input);
    }
    //  But check_subst_atomic_terms multiplies with EXISTING valid, not replaces it.
    //  Actually looking at the code: cs_and(cs_eq(phi_tag, result_tag), cs_const(1))
    //  This is the NEW valid = cs_eq * 1 = 1. It does NOT multiply by old valid!
    //  The old valid is lost. Wait, is that right?
    //
    //  Looking at check_subst_atomic_terms:
    //  cs_pair(rest, cs_pair(cs_and(cs_eq(phi_tag, result_tag), cs_const(1)), cs_pair(t_enc, t_set)))
    //  The second component is cs_and(cs_eq(...), 1) — this REPLACES valid, not multiplies.
    //  But wait, this is the entire new acc. The valid field IS this value.
    //  So new_valid = cs_eq(phi_tag, result_tag) * 1 = 1 (when tags match).
    //  The OLD valid is not preserved!
    //
    //  This means: if valid was already > 1 (which it can't be, it's always 0 or 1),
    //  the new valid would be 1 regardless. But if valid was > 0, the step function
    //  already checked valid > 0 before dispatching. So the result replaces valid with
    //  the tag check result. This means valid is always 0 or 1.
    //
    //  For our backward proof: tags match → cs_eq returns 1 → new valid = 1 * 1 = 1.
    //  We need: result == pair(rest, pair(1, pair(t_enc, t_set))).
    //  But the ensures says pair(rest, pair(valid, pair(t_enc, t_set))) — using OLD valid.
    //  If old valid was 1, this is pair(rest, pair(1, pair(t_enc, t_set))). ✓
    //  If old valid > 1... well, the step replaces it with 1. So the ensures is wrong
    //  unless valid == 1.
    //
    //  Hmm, actually, valid in our traversal starts at 1 and is always replaced by
    //  cs_and(tag_check, ...) which is 0 or 1. So valid is always 0 or 1.
    //  For the backward proof: valid starts at 1, each step replaces with 1 (tags match),
    //  so valid stays 1 throughout.
    //
    //  Let me fix the ensures: the result has NEW valid = 1 (not old valid).
    //  Actually, let me recheck. The ensures says:
    //  eval_comp(check_subst_process_pair(), input) == pair(rest, pair(valid, pair(t_enc, t_set)))
    //  Since valid == 1 in our use case, and the result has valid=1, this IS correct
    //  when we require valid == 1. But the requires only says valid > 0.
    //
    //  For generality, I should either:
    //  a) Add requires valid == 1 (fine for backward proof)
    //  b) Change ensures to pair(rest, pair(1, pair(t_enc, t_set)))
    //
    //  Let me go with (b) since it's more accurate.

    //  The process_pair dispatches: IfZero(phi_tag) → phi_tag == 0 → then → atomic_terms
    assert(eval_comp(check_subst_process_pair(), input)
        == eval_comp(check_subst_atomic_terms(), input)) by {
        reveal(eval_comp);
        lemma_eval_ifzero_then(phi_tag_cs,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, phi_tag_cs)),
                then_br: Box::new(check_subst_atomic_terms()),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs))),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }),
            },
            input);
    }

    //  atomic_terms result: chain all cs_pair evaluations
    assert(eval_comp(check_subst_atomic_terms(), input)
        == pair(rest, pair(1nat, pair(t_enc, t_set)))) by {
        reveal(eval_comp);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_pair(valid_new, cs_pair(t_enc_cs, t_set_cs), input);
        lemma_eval_pair(rest_cs, cs_pair(valid_new, cs_pair(t_enc_cs, t_set_cs)), input);
    }
}

///  Atomic In (tag 1): same result as Eq, different dispatch path.
pub proof fn lemma_subst_process_pair_atomic_in(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) == 1,
        unpair1(result_node) == 1,
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(check_subst_process_pair(), input)
            == pair(rest, pair(1nat, pair(t_enc, t_set)))
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));

    assert(eval_comp(br_acc(), input) == acc) by {
        reveal(eval_comp); lemma_eval_br_acc(i, acc, orig);
    }
    assert(eval_comp(cs_fst(br_acc()), input) == stack) by {
        reveal(eval_comp);
        lemma_eval_fst(br_acc(), input);
        lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    }
    assert(eval_comp(cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc()))), input) == entry) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(br_acc()), input);
        lemma_unpair1_pair(entry + 1, rest);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
        lemma_eval_pred(entry + 1);
    }
    assert(eval_comp(cs_snd(cs_fst(br_acc())), input) == rest) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_fst(br_acc()), input);
        lemma_unpair2_pair(entry + 1, rest);
    }

    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node) by {
        reveal(eval_comp);
        lemma_eval_fst(entry_cs, input);
        lemma_unpair1_pair(phi_node, result_node);
    }
    assert(eval_comp(cs_snd(entry_cs), input) == result_node) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_unpair2_pair(phi_node, result_node);
    }
    let phi_tag_cs = cs_fst(cs_fst(entry_cs));
    assert(eval_comp(phi_tag_cs, input) == 1) by {
        reveal(eval_comp); lemma_eval_fst(cs_fst(entry_cs), input);
    }
    let result_tag_cs = cs_fst(cs_snd(entry_cs));
    assert(eval_comp(result_tag_cs, input) == 1) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_eval_fst(cs_snd(entry_cs), input);
    }

    //  phi_tag == 1 → IfZero(phi_tag) → else → IfZero(pred(phi_tag)) → then
    assert(eval_comp(cs_comp(CompSpec::Pred, phi_tag_cs), input) == 0) by {
        reveal(eval_comp);
        lemma_eval_comp(CompSpec::Pred, phi_tag_cs, input);
        lemma_eval_pred(1nat);
    }
    assert(eval_comp(check_subst_process_pair(), input)
        == eval_comp(check_subst_atomic_terms(), input)) by {
        reveal(eval_comp);
        let pred_tag = cs_comp(CompSpec::Pred, phi_tag_cs);
        lemma_eval_ifzero_then(pred_tag,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs))),
                then_br: Box::new(check_subst_unary()),
                else_br: Box::new(check_subst_compound()),
            }, input);
        lemma_eval_ifzero_else(phi_tag_cs,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(pred_tag),
                then_br: Box::new(check_subst_atomic_terms()),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs))),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }),
            }, input);
    }

    //  cs_eq(phi_tag, result_tag) = cs_eq(1, 1) = 1
    assert(eval_comp(cs_eq(phi_tag_cs, result_tag_cs), input) == 1) by {
        reveal(eval_comp);
        lemma_eval_eq(phi_tag_cs, result_tag_cs, input);
    }
    assert(eval_comp(cs_and(cs_eq(phi_tag_cs, result_tag_cs), cs_const(1)), input) == 1) by {
        reveal(eval_comp);
        lemma_eval_cs_and(cs_eq(phi_tag_cs, result_tag_cs), cs_const(1), input);
    }

    //  t_enc and t_set
    let t_enc_cs = cs_fst(cs_snd(cs_snd(br_acc())));
    let t_set_cs = cs_snd(cs_snd(cs_snd(br_acc())));
    assert(eval_comp(t_enc_cs, input) == t_enc && eval_comp(t_set_cs, input) == t_set) by {
        reveal(eval_comp);
        lemma_eval_snd(br_acc(), input);
        lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
        lemma_eval_snd(cs_snd(br_acc()), input);
        lemma_unpair2_pair(valid, pair(t_enc, t_set));
        lemma_eval_fst(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair1_pair(t_enc, t_set);
        lemma_eval_snd(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair2_pair(t_enc, t_set);
    }

    let rest_cs = cs_snd(cs_fst(br_acc()));
    let valid_new = cs_and(cs_eq(phi_tag_cs, result_tag_cs), cs_const(1));
    assert(eval_comp(check_subst_atomic_terms(), input)
        == pair(rest, pair(1nat, pair(t_enc, t_set)))) by {
        reveal(eval_comp);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_pair(valid_new, cs_pair(t_enc_cs, t_set_cs), input);
        lemma_eval_pair(rest_cs, cs_pair(valid_new, cs_pair(t_enc_cs, t_set_cs)), input);
    }
}

///  Unary Not (tag 2): check tags, push sub-pair (phi_sub, result_sub).
pub proof fn lemma_subst_process_pair_unary(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) == 2,
        unpair1(result_node) == 2,
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        let new_entry = pair(unpair2(phi_node), unpair2(result_node));
        let new_stack = pair(new_entry + 1, rest);
        eval_comp(check_subst_process_pair(), input)
            == pair(new_stack, pair(1nat, pair(t_enc, t_set)))
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));

    //  Reuse: extract br_acc, stack, entry, phi_node, result_node, phi_tag
    assert(eval_comp(br_acc(), input) == acc) by {
        reveal(eval_comp); lemma_eval_br_acc(i, acc, orig);
    }
    assert(eval_comp(cs_fst(br_acc()), input) == stack) by {
        reveal(eval_comp);
        lemma_eval_fst(br_acc(), input);
        lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    }
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    assert(eval_comp(entry_cs, input) == entry) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(br_acc()), input);
        lemma_unpair1_pair(entry + 1, rest);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
        lemma_eval_pred(entry + 1);
    }
    assert(eval_comp(cs_snd(cs_fst(br_acc())), input) == rest) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_fst(br_acc()), input);
        lemma_unpair2_pair(entry + 1, rest);
    }
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node) by {
        reveal(eval_comp); lemma_eval_fst(entry_cs, input); lemma_unpair1_pair(phi_node, result_node);
    }
    assert(eval_comp(cs_snd(entry_cs), input) == result_node) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input); lemma_unpair2_pair(phi_node, result_node);
    }

    let phi_tag_cs = cs_fst(cs_fst(entry_cs));
    assert(eval_comp(phi_tag_cs, input) == 2) by {
        reveal(eval_comp); lemma_eval_fst(cs_fst(entry_cs), input);
    }
    let result_tag_cs = cs_fst(cs_snd(entry_cs));
    assert(eval_comp(result_tag_cs, input) == 2) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input);
        lemma_eval_fst(cs_snd(entry_cs), input);
    }

    //  Dispatch: phi_tag == 2
    //  IfZero(phi_tag=2) → else → IfZero(pred(2)=1) → else → IfZero(pred(pred(2))=0) → then → unary
    assert(eval_comp(cs_comp(CompSpec::Pred, phi_tag_cs), input) == 1) by {
        reveal(eval_comp);
        lemma_eval_comp(CompSpec::Pred, phi_tag_cs, input);
        lemma_eval_pred(2nat);
    }
    let pred_tag = cs_comp(CompSpec::Pred, phi_tag_cs);
    let pred_pred_tag = cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs));
    assert(eval_comp(pred_pred_tag, input) == 0) by {
        reveal(eval_comp);
        lemma_eval_comp(CompSpec::Pred, pred_tag, input);
        lemma_eval_pred(1nat);
    }

    assert(eval_comp(check_subst_process_pair(), input)
        == eval_comp(check_subst_unary(), input)) by {
        reveal(eval_comp);
        //  Inner: IfZero(pred_pred_tag=0) → then → unary
        lemma_eval_ifzero_then(pred_pred_tag,
            check_subst_unary(), check_subst_compound(), input);
        //  Middle: IfZero(pred_tag=1) → else
        lemma_eval_ifzero_else(pred_tag,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(pred_pred_tag),
                then_br: Box::new(check_subst_unary()),
                else_br: Box::new(check_subst_compound()),
            }, input);
        //  Outer: IfZero(phi_tag=2) → else
        lemma_eval_ifzero_else(phi_tag_cs,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(pred_tag),
                then_br: Box::new(check_subst_atomic_terms()),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(pred_pred_tag),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }),
            }, input);
    }

    //  cs_eq(phi_tag, result_tag) = cs_eq(2, 2) = 1
    assert(eval_comp(cs_eq(phi_tag_cs, result_tag_cs), input) == 1) by {
        reveal(eval_comp); lemma_eval_eq(phi_tag_cs, result_tag_cs, input);
    }

    //  sub-pair: phi_sub = snd(phi_node), result_sub = snd(result_node)
    let phi_sub_cs = cs_snd(cs_fst(entry_cs));
    let result_sub_cs = cs_snd(cs_snd(entry_cs));
    assert(eval_comp(phi_sub_cs, input) == unpair2(phi_node)) by {
        reveal(eval_comp); lemma_eval_snd(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_sub_cs, input) == unpair2(result_node)) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_eval_snd(cs_snd(entry_cs), input);
    }

    //  t_enc and t_set
    let t_enc_cs = cs_fst(cs_snd(cs_snd(br_acc())));
    let t_set_cs = cs_snd(cs_snd(cs_snd(br_acc())));
    assert(eval_comp(t_enc_cs, input) == t_enc && eval_comp(t_set_cs, input) == t_set) by {
        reveal(eval_comp);
        lemma_eval_snd(br_acc(), input);
        lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
        lemma_eval_snd(cs_snd(br_acc()), input);
        lemma_unpair2_pair(valid, pair(t_enc, t_set));
        lemma_eval_fst(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair1_pair(t_enc, t_set);
        lemma_eval_snd(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair2_pair(t_enc, t_set);
    }

    //  Compose check_subst_unary result
    let rest_cs = cs_snd(cs_fst(br_acc()));
    let new_entry_cs = cs_pair(phi_sub_cs, result_sub_cs);
    assert(eval_comp(check_subst_unary(), input)
        == pair(pair(pair(unpair2(phi_node), unpair2(result_node)) + 1, rest),
            pair(1nat, pair(t_enc, t_set)))) by {
        reveal(eval_comp);
        lemma_eval_pair(phi_sub_cs, result_sub_cs, input);
        lemma_eval_add(new_entry_cs, cs_const(1), input);
        let new_entry_plus_1 = CompSpec::Add { left: Box::new(new_entry_cs), right: Box::new(cs_const(1)) };
        lemma_eval_pair(new_entry_plus_1, rest_cs, input);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_pair(cs_eq(phi_tag_cs, result_tag_cs), cs_pair(t_enc_cs, t_set_cs), input);
        let new_stack_cs = cs_pair(new_entry_plus_1, rest_cs);
        lemma_eval_pair(new_stack_cs,
            cs_pair(cs_eq(phi_tag_cs, result_tag_cs), cs_pair(t_enc_cs, t_set_cs)), input);
    }
}

///  Dispatch: for tags >= 3, process_pair routes to check_subst_compound.
proof fn lemma_subst_dispatch_compound(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) >= 3,
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        eval_comp(check_subst_process_pair(), input)
            == eval_comp(check_subst_compound(), input)
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));
    let tag = unpair1(phi_node);

    assert(eval_comp(br_acc(), input) == acc) by {
        reveal(eval_comp); lemma_eval_br_acc(i, acc, orig);
    }
    assert(eval_comp(cs_fst(br_acc()), input) == stack) by {
        reveal(eval_comp);
        lemma_eval_fst(br_acc(), input);
        lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    }
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    assert(eval_comp(entry_cs, input) == entry) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(br_acc()), input);
        lemma_unpair1_pair(entry + 1, rest);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
        lemma_eval_pred(entry + 1);
    }
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node) by {
        reveal(eval_comp); lemma_eval_fst(entry_cs, input); lemma_unpair1_pair(phi_node, result_node);
    }
    let phi_tag_cs = cs_fst(cs_fst(entry_cs));
    assert(eval_comp(phi_tag_cs, input) == tag) by {
        reveal(eval_comp); lemma_eval_fst(cs_fst(entry_cs), input);
    }
    //  tag >= 3: all three IfZero take else
    let pred_tag = cs_comp(CompSpec::Pred, phi_tag_cs);
    let pred_pred_tag = cs_comp(CompSpec::Pred, pred_tag);
    assert(eval_comp(pred_tag, input) == (tag - 1) as nat) by {
        reveal(eval_comp);
        lemma_eval_comp(CompSpec::Pred, phi_tag_cs, input);
        lemma_eval_pred(tag);
    }
    assert(eval_comp(pred_pred_tag, input) == (tag - 2) as nat) by {
        reveal(eval_comp);
        lemma_eval_comp(CompSpec::Pred, pred_tag, input);
        lemma_eval_pred((tag - 1) as nat);
    }
    assert(eval_comp(check_subst_process_pair(), input)
        == eval_comp(check_subst_compound(), input)) by {
        reveal(eval_comp);
        //  Inner: IfZero(pred_pred_tag >= 1) → else → compound
        lemma_eval_ifzero_else(pred_pred_tag,
            check_subst_unary(), check_subst_compound(), input);
        //  Middle: IfZero(pred_tag >= 2) → else
        lemma_eval_ifzero_else(pred_tag,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(pred_pred_tag),
                then_br: Box::new(check_subst_unary()),
                else_br: Box::new(check_subst_compound()),
            }, input);
        //  Outer: IfZero(tag >= 3) → else
        lemma_eval_ifzero_else(phi_tag_cs,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(pred_tag),
                then_br: Box::new(check_subst_atomic_terms()),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(pred_pred_tag),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }),
            }, input);
    }
}

///  Binary compound (tags 3-6): push two sub-pairs.
pub proof fn lemma_subst_process_pair_binary(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) >= 3,
        unpair1(phi_node) <= 6,
        unpair1(phi_node) == unpair1(result_node),
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        let phi_c = unpair2(phi_node);
        let result_c = unpair2(result_node);
        let entry_l = pair(unpair1(phi_c), unpair1(result_c));
        let entry_r = pair(unpair2(phi_c), unpair2(result_c));
        let new_stack = pair(entry_l + 1, pair(entry_r + 1, rest));
        eval_comp(check_subst_process_pair(), input)
            == pair(new_stack, pair(1nat, pair(t_enc, t_set)))
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));
    let tag = unpair1(phi_node);

    //  Dispatch to compound
    lemma_subst_dispatch_compound(i, phi_node, result_node, rest,
        valid, t_enc, t_set, phi_enc, result_enc, var);

    //  Now show compound evaluates to the binary result
    //  First: extract entry, phi/result content
    assert(eval_comp(br_acc(), input) == acc) by {
        reveal(eval_comp); lemma_eval_br_acc(i, acc, orig);
    }
    assert(eval_comp(cs_fst(br_acc()), input) == stack) by {
        reveal(eval_comp);
        lemma_eval_fst(br_acc(), input);
        lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    }
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    assert(eval_comp(entry_cs, input) == entry) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(br_acc()), input);
        lemma_unpair1_pair(entry + 1, rest);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
        lemma_eval_pred(entry + 1);
    }
    assert(eval_comp(cs_snd(cs_fst(br_acc())), input) == rest) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_fst(br_acc()), input);
        lemma_unpair2_pair(entry + 1, rest);
    }
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node) by {
        reveal(eval_comp); lemma_eval_fst(entry_cs, input); lemma_unpair1_pair(phi_node, result_node);
    }
    assert(eval_comp(cs_snd(entry_cs), input) == result_node) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input); lemma_unpair2_pair(phi_node, result_node);
    }

    //  Tags and content
    let phi_tag_cs = cs_fst(cs_fst(entry_cs));
    let result_tag_cs = cs_fst(cs_snd(entry_cs));
    let phi_content_cs = cs_snd(cs_fst(entry_cs));
    let result_content_cs = cs_snd(cs_snd(entry_cs));
    assert(eval_comp(phi_tag_cs, input) == tag) by {
        reveal(eval_comp); lemma_eval_fst(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_tag_cs, input) == tag) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_eval_fst(cs_snd(entry_cs), input);
    }
    assert(eval_comp(phi_content_cs, input) == unpair2(phi_node)) by {
        reveal(eval_comp); lemma_eval_snd(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_content_cs, input) == unpair2(result_node)) by {
        reveal(eval_comp);
        lemma_eval_snd(entry_cs, input);
        lemma_eval_snd(cs_snd(entry_cs), input);
    }

    //  is_quantifier = cs_lt(6, tag): tag <= 6 → 0
    let is_quant = cs_lt(cs_const(6), phi_tag_cs);
    assert(eval_comp(is_quant, input) == 0) by {
        reveal(eval_comp); lemma_eval_lt(cs_const(6), phi_tag_cs, input);
    }

    //  tags_match = cs_eq(phi_tag, result_tag) = 1
    let tags_match = cs_eq(phi_tag_cs, result_tag_cs);
    assert(eval_comp(tags_match, input) == 1) by {
        reveal(eval_comp); lemma_eval_eq(phi_tag_cs, result_tag_cs, input);
    }

    //  Content sub-parts
    let phi_c = unpair2(phi_node);
    let result_c = unpair2(result_node);
    assert(eval_comp(cs_fst(phi_content_cs), input) == unpair1(phi_c)) by {
        reveal(eval_comp); lemma_eval_fst(phi_content_cs, input);
    }
    assert(eval_comp(cs_fst(result_content_cs), input) == unpair1(result_c)) by {
        reveal(eval_comp); lemma_eval_fst(result_content_cs, input);
    }
    assert(eval_comp(cs_snd(phi_content_cs), input) == unpair2(phi_c)) by {
        reveal(eval_comp); lemma_eval_snd(phi_content_cs, input);
    }
    assert(eval_comp(cs_snd(result_content_cs), input) == unpair2(result_c)) by {
        reveal(eval_comp); lemma_eval_snd(result_content_cs, input);
    }

    //  t_enc, t_set
    let t_enc_cs = cs_fst(cs_snd(cs_snd(br_acc())));
    let t_set_cs = cs_snd(cs_snd(cs_snd(br_acc())));
    assert(eval_comp(t_enc_cs, input) == t_enc && eval_comp(t_set_cs, input) == t_set) by {
        reveal(eval_comp);
        lemma_eval_snd(br_acc(), input);
        lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
        lemma_eval_snd(cs_snd(br_acc()), input);
        lemma_unpair2_pair(valid, pair(t_enc, t_set));
        lemma_eval_fst(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair1_pair(t_enc, t_set);
        lemma_eval_snd(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair2_pair(t_enc, t_set);
    }

    //  Build result: binary push two sub-pairs
    let rest_cs = cs_snd(cs_fst(br_acc()));
    let left_pair_cs = cs_pair(cs_fst(phi_content_cs), cs_fst(result_content_cs));
    let right_pair_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));

    //  IfZero(is_quant=0) → then branch (binary)
    assert(eval_comp(check_subst_compound(), input) == ({
        let entry_l = pair(unpair1(phi_c), unpair1(result_c));
        let entry_r = pair(unpair2(phi_c), unpair2(result_c));
        let new_stack = pair(entry_l + 1, pair(entry_r + 1, rest));
        pair(new_stack, pair(1nat, pair(t_enc, t_set)))
    })) by {
        reveal(eval_comp);
        lemma_eval_pair(cs_fst(phi_content_cs), cs_fst(result_content_cs), input);
        lemma_eval_add(left_pair_cs, cs_const(1), input);
        lemma_eval_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs), input);
        lemma_eval_add(right_pair_cs, cs_const(1), input);
        let lp1 = CompSpec::Add { left: Box::new(left_pair_cs), right: Box::new(cs_const(1)) };
        let rp1 = CompSpec::Add { left: Box::new(right_pair_cs), right: Box::new(cs_const(1)) };
        lemma_eval_pair(rp1, rest_cs, input);
        lemma_eval_pair(lp1, cs_pair(rp1, rest_cs), input);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_pair(tags_match, cs_pair(t_enc_cs, t_set_cs), input);
        let new_stack_cs = cs_pair(lp1, cs_pair(rp1, rest_cs));
        lemma_eval_pair(new_stack_cs, cs_pair(tags_match, cs_pair(t_enc_cs, t_set_cs)), input);
        //  IfZero(is_quant=0) → then branch
        let then_br = cs_pair(new_stack_cs, cs_pair(tags_match, cs_pair(t_enc_cs, t_set_cs)));
        lemma_eval_ifzero_then(is_quant, then_br,
            CompSpec::IfZero {
                cond: Box::new(cs_eq(cs_fst(phi_content_cs), cs_snd(cs_snd(cs_snd(CompSpec::Id))))),
                then_br: Box::new(cs_pair(
                    cs_pair(rp1, rest_cs),
                    cs_pair(cs_and(tags_match, cs_eq(cs_fst(phi_content_cs), cs_fst(result_content_cs))),
                        cs_pair(t_enc_cs, t_set_cs)),
                )),
                else_br: Box::new(cs_pair(
                    rest_cs,
                    cs_pair(cs_and(tags_match, cs_eq(cs_fst(entry_cs), cs_snd(entry_cs))),
                        cs_pair(t_enc_cs, t_set_cs)),
                )),
            },
            input);
    }
}

///  Quantifier (tags 7-8): push sub-pair, check tag + bound var match.
///  The "var" in check_subst_step is pair(result_enc, var_actual) which != bound_var,
///  so the checker always takes the "push sub-pair" branch.
pub proof fn lemma_subst_process_pair_quantifier(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    requires
        valid > 0,
        unpair1(phi_node) >= 7,
        unpair1(phi_node) == unpair1(result_node),
        //  Bound vars match (subst preserves bound vars)
        unpair1(unpair2(phi_node)) == unpair1(unpair2(result_node)),
        //  Bound var != checker's "var" (= pair(result_enc, var))
        //  This is the condition for taking the "push sub-pair" branch
        unpair1(unpair2(phi_node)) != pair(result_enc, var),
    ensures ({
        let entry = pair(phi_node, result_node);
        let stack = pair(entry + 1, rest);
        let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
        let input = pair(i, pair(acc, pair(phi_enc, pair(result_enc, var))));
        let phi_sub = unpair2(unpair2(phi_node));
        let result_sub = unpair2(unpair2(result_node));
        let new_entry = pair(phi_sub, result_sub);
        let new_stack = pair(new_entry + 1, rest);
        eval_comp(check_subst_process_pair(), input)
            == pair(new_stack, pair(1nat, pair(t_enc, t_set)))
    }),
{
    hide(eval_comp);
    let entry = pair(phi_node, result_node);
    let stack = pair(entry + 1, rest);
    let acc = pair(stack, pair(valid, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let input = pair(i, pair(acc, orig));
    let tag = unpair1(phi_node);

    //  Dispatch to compound (tag >= 3 since tag >= 7)
    lemma_subst_dispatch_compound(i, phi_node, result_node, rest,
        valid, t_enc, t_set, phi_enc, result_enc, var);

    //  Extract entry components
    assert(eval_comp(br_acc(), input) == acc) by {
        reveal(eval_comp); lemma_eval_br_acc(i, acc, orig);
    }
    assert(eval_comp(cs_fst(br_acc()), input) == stack) by {
        reveal(eval_comp);
        lemma_eval_fst(br_acc(), input);
        lemma_unpair1_pair(stack, pair(valid, pair(t_enc, t_set)));
    }
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    assert(eval_comp(entry_cs, input) == entry) by {
        reveal(eval_comp);
        lemma_eval_fst(cs_fst(br_acc()), input);
        lemma_unpair1_pair(entry + 1, rest);
        lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), input);
        lemma_eval_pred(entry + 1);
    }
    assert(eval_comp(cs_snd(cs_fst(br_acc())), input) == rest) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_fst(br_acc()), input);
        lemma_unpair2_pair(entry + 1, rest);
    }
    assert(eval_comp(cs_fst(entry_cs), input) == phi_node) by {
        reveal(eval_comp); lemma_eval_fst(entry_cs, input); lemma_unpair1_pair(phi_node, result_node);
    }
    assert(eval_comp(cs_snd(entry_cs), input) == result_node) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input); lemma_unpair2_pair(phi_node, result_node);
    }

    let phi_tag_cs = cs_fst(cs_fst(entry_cs));
    let result_tag_cs = cs_fst(cs_snd(entry_cs));
    let phi_content_cs = cs_snd(cs_fst(entry_cs));
    let result_content_cs = cs_snd(cs_snd(entry_cs));
    assert(eval_comp(phi_tag_cs, input) == tag) by {
        reveal(eval_comp); lemma_eval_fst(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_tag_cs, input) == tag) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input);
        lemma_eval_fst(cs_snd(entry_cs), input);
    }
    assert(eval_comp(phi_content_cs, input) == unpair2(phi_node)) by {
        reveal(eval_comp); lemma_eval_snd(cs_fst(entry_cs), input);
    }
    assert(eval_comp(result_content_cs, input) == unpair2(result_node)) by {
        reveal(eval_comp); lemma_eval_snd(entry_cs, input);
        lemma_eval_snd(cs_snd(entry_cs), input);
    }

    //  is_quantifier = cs_lt(6, tag): tag >= 7 → 1
    let is_quant = cs_lt(cs_const(6), phi_tag_cs);
    assert(eval_comp(is_quant, input) == 1) by {
        reveal(eval_comp); lemma_eval_lt(cs_const(6), phi_tag_cs, input);
    }

    //  tags_match = cs_eq(phi_tag, result_tag) = 1
    let tags_match = cs_eq(phi_tag_cs, result_tag_cs);
    assert(eval_comp(tags_match, input) == 1) by {
        reveal(eval_comp); lemma_eval_eq(phi_tag_cs, result_tag_cs, input);
    }

    //  bound var and "var" from original input
    let bound_var_cs = cs_fst(phi_content_cs);
    let result_bound_cs = cs_fst(result_content_cs);
    let var_cs = cs_snd(cs_snd(cs_snd(CompSpec::Id)));
    assert(eval_comp(bound_var_cs, input) == unpair1(unpair2(phi_node))) by {
        reveal(eval_comp); lemma_eval_fst(phi_content_cs, input);
    }
    assert(eval_comp(result_bound_cs, input) == unpair1(unpair2(result_node))) by {
        reveal(eval_comp); lemma_eval_fst(result_content_cs, input);
    }
    assert(eval_comp(var_cs, input) == pair(result_enc, var)) by {
        reveal(eval_comp);
        lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), input);
        lemma_eval_snd(cs_snd(CompSpec::Id), input);
        lemma_eval_snd(CompSpec::Id, input);
        lemma_unpair2_pair(i, pair(acc, orig));
        lemma_unpair2_pair(acc, orig);
        lemma_unpair2_pair(phi_enc, pair(result_enc, var));
    }

    //  cs_eq(bound_var, var) = cs_eq(unpair1(unpair2(phi_node)), pair(result_enc, var)) = 0
    //  because bound_var != pair(result_enc, var) by requires
    let bound_eq_var = cs_eq(bound_var_cs, var_cs);
    assert(eval_comp(bound_eq_var, input) == 0) by {
        reveal(eval_comp); lemma_eval_eq(bound_var_cs, var_cs, input);
    }

    //  bound vars match
    let bound_match = cs_eq(bound_var_cs, result_bound_cs);
    assert(eval_comp(bound_match, input) == 1) by {
        reveal(eval_comp); lemma_eval_eq(bound_var_cs, result_bound_cs, input);
    }

    //  cs_and(tags_match, bound_match) = 1 * 1 = 1
    assert(eval_comp(cs_and(tags_match, bound_match), input) == 1) by {
        reveal(eval_comp);
        lemma_eval_cs_and(tags_match, bound_match, input);
    }

    //  Sub-formula parts
    let phi_sub_cs = cs_snd(phi_content_cs);
    let result_sub_cs = cs_snd(result_content_cs);
    assert(eval_comp(phi_sub_cs, input) == unpair2(unpair2(phi_node))) by {
        reveal(eval_comp); lemma_eval_snd(phi_content_cs, input);
    }
    assert(eval_comp(result_sub_cs, input) == unpair2(unpair2(result_node))) by {
        reveal(eval_comp); lemma_eval_snd(result_content_cs, input);
    }

    //  t_enc, t_set
    let t_enc_cs = cs_fst(cs_snd(cs_snd(br_acc())));
    let t_set_cs = cs_snd(cs_snd(cs_snd(br_acc())));
    assert(eval_comp(t_enc_cs, input) == t_enc && eval_comp(t_set_cs, input) == t_set) by {
        reveal(eval_comp);
        lemma_eval_snd(br_acc(), input);
        lemma_unpair2_pair(stack, pair(valid, pair(t_enc, t_set)));
        lemma_eval_snd(cs_snd(br_acc()), input);
        lemma_unpair2_pair(valid, pair(t_enc, t_set));
        lemma_eval_fst(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair1_pair(t_enc, t_set);
        lemma_eval_snd(cs_snd(cs_snd(br_acc())), input);
        lemma_unpair2_pair(t_enc, t_set);
    }

    //  Build compound result for quantifier (IfZero(is_quant=1) → else → IfZero(bound_eq_var=0) → then → push sub)
    let rest_cs = cs_snd(cs_fst(br_acc()));
    let sub_pair_cs = cs_pair(phi_sub_cs, result_sub_cs);
    assert(eval_comp(check_subst_compound(), input) == ({
        let phi_sub = unpair2(unpair2(phi_node));
        let result_sub = unpair2(unpair2(result_node));
        let new_entry = pair(phi_sub, result_sub);
        let new_stack = pair(new_entry + 1, rest);
        pair(new_stack, pair(1nat, pair(t_enc, t_set)))
    })) by {
        reveal(eval_comp);
        //  Build the then branch (push sub-pair + check bound var match)
        lemma_eval_pair(phi_sub_cs, result_sub_cs, input);
        lemma_eval_add(sub_pair_cs, cs_const(1), input);
        let sp1 = CompSpec::Add { left: Box::new(sub_pair_cs), right: Box::new(cs_const(1)) };
        lemma_eval_pair(sp1, rest_cs, input);
        lemma_eval_pair(t_enc_cs, t_set_cs, input);
        lemma_eval_pair(cs_and(tags_match, bound_match), cs_pair(t_enc_cs, t_set_cs), input);
        let new_stack_cs = cs_pair(sp1, rest_cs);
        let new_valid_cs = cs_pair(cs_and(tags_match, bound_match), cs_pair(t_enc_cs, t_set_cs));
        lemma_eval_pair(new_stack_cs, new_valid_cs, input);

        //  IfZero(bound_eq_var=0) → then branch (push sub)
        let then_br = cs_pair(new_stack_cs, new_valid_cs);
        let else_br = cs_pair(
            rest_cs,
            cs_pair(cs_and(tags_match, cs_eq(cs_fst(entry_cs), cs_snd(entry_cs))),
                cs_pair(t_enc_cs, t_set_cs)),
        );
        lemma_eval_ifzero_then(bound_eq_var, then_br, else_br, input);

        //  IfZero(is_quant=1) → else branch
        //  Build the binary then_br for reference
        let lp_cs = cs_pair(cs_fst(phi_content_cs), cs_fst(result_content_cs));
        let rp_cs = cs_pair(cs_snd(phi_content_cs), cs_snd(result_content_cs));
        let lp1 = CompSpec::Add { left: Box::new(lp_cs), right: Box::new(cs_const(1)) };
        let rp1 = CompSpec::Add { left: Box::new(rp_cs), right: Box::new(cs_const(1)) };
        let binary_then = cs_pair(
            cs_pair(lp1, cs_pair(rp1, rest_cs)),
            cs_pair(tags_match, cs_pair(t_enc_cs, t_set_cs)),
        );
        let quant_else = CompSpec::IfZero {
            cond: Box::new(bound_eq_var),
            then_br: Box::new(then_br),
            else_br: Box::new(else_br),
        };
        lemma_eval_ifzero_else(is_quant, binary_then, quant_else, input);
    }
}

} //  verus!
