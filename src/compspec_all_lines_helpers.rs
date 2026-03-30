use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::*;
use crate::proof_encoding::*;
use crate::proof_system::*;

verus! {

///  The step function for check_all_lines.
///  Extract it as a spec fn for readability.
pub open spec fn cal_step() -> CompSpec {
    let remaining = cs_fst(br_acc());
    let valid = cs_fst(cs_snd(br_acc()));
    let idx = cs_snd(cs_snd(br_acc()));
    let orig_seq = cs_snd(cs_snd(CompSpec::Id));

    CompSpec::IfZero {
        cond: Box::new(cs_fst(remaining)),
        then_br: Box::new(br_acc()),
        else_br: Box::new(CompSpec::CantorPair {
            left: Box::new(cs_snd(remaining)),
            right: Box::new(CompSpec::CantorPair {
                left: Box::new(cs_and(
                    valid,
                    cs_comp(check_line(), CompSpec::CantorPair {
                        left: Box::new(orig_seq),
                        right: Box::new(idx),
                    }),
                )),
                right: Box::new(CompSpec::Add {
                    left: Box::new(idx),
                    right: Box::new(cs_const(1)),
                }),
            }),
        }),
    }
}

///  When remaining is empty (fst == 0), the step returns acc unchanged.
proof fn lemma_cal_step_done(
    i: nat, remaining: nat, valid: nat, idx: nat, s: nat,
)
    requires
        unpair1(remaining) == 0,
    ensures ({
        let acc = pair(remaining, pair(valid, idx));
        let input = pair(i, pair(acc, s));
        eval_comp(cal_step(), input) == acc
    }),
{
    let acc = pair(remaining, pair(valid, idx));
    let input = pair(i, pair(acc, s));

    lemma_eval_br_acc(i, acc, s);
    let remaining_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(remaining, pair(valid, idx));

    let fst_remaining = cs_fst(remaining_expr);
    lemma_eval_fst(remaining_expr, input);

    //  IfZero(fst(remaining) == 0): then branch → acc
    lemma_eval_ifzero_then(fst_remaining, br_acc(),
        CompSpec::CantorPair {
            left: Box::new(cs_snd(remaining_expr)),
            right: Box::new(CompSpec::CantorPair {
                left: Box::new(cs_and(
                    cs_fst(cs_snd(br_acc())),
                    cs_comp(check_line(), CompSpec::CantorPair {
                        left: Box::new(cs_snd(cs_snd(CompSpec::Id))),
                        right: Box::new(cs_snd(cs_snd(br_acc()))),
                    }),
                )),
                right: Box::new(CompSpec::Add {
                    left: Box::new(cs_snd(cs_snd(br_acc()))),
                    right: Box::new(cs_const(1)),
                }),
            }),
        },
        input);
}

///  When remaining is non-empty, step advances: pops head, checks line, advances idx.
proof fn lemma_cal_step_advance(
    i: nat, head_plus_1: nat, rest_enc: nat, valid: nat, idx: nat, s: nat,
)
    requires
        head_plus_1 > 0,
    ensures ({
        let remaining = pair(head_plus_1, rest_enc);
        let acc = pair(remaining, pair(valid, idx));
        let input = pair(i, pair(acc, s));
        let cl = eval_comp(check_line(), pair(s, idx));
        eval_comp(cal_step(), input) == pair(rest_enc, pair(valid * cl, idx + 1))
    }),
{
    let remaining = pair(head_plus_1, rest_enc);
    let acc = pair(remaining, pair(valid, idx));
    let input = pair(i, pair(acc, s));

    //  Extract acc
    lemma_eval_br_acc(i, acc, s);
    let remaining_expr = cs_fst(br_acc());
    lemma_eval_fst(br_acc(), input);
    lemma_unpair1_pair(remaining, pair(valid, idx));

    //  fst(remaining) = head_plus_1 > 0 → else branch (non-empty)
    let fst_remaining = cs_fst(remaining_expr);
    lemma_eval_fst(remaining_expr, input);
    lemma_unpair1_pair(head_plus_1, rest_enc);
    assert(eval_comp(fst_remaining, input) == head_plus_1);
    assert(head_plus_1 != 0);

    //  snd(remaining) = rest_enc
    let snd_remaining = cs_snd(remaining_expr);
    lemma_eval_snd(remaining_expr, input);
    lemma_unpair2_pair(head_plus_1, rest_enc);

    //  valid and idx extraction
    let valid_expr = cs_fst(cs_snd(br_acc()));
    let idx_expr = cs_snd(cs_snd(br_acc()));
    lemma_eval_fst(cs_snd(br_acc()), input);
    lemma_eval_snd(cs_snd(br_acc()), input);
    lemma_eval_snd(br_acc(), input);
    lemma_unpair2_pair(remaining, pair(valid, idx));
    lemma_unpair1_pair(valid, idx);
    lemma_unpair2_pair(valid, idx);

    //  orig_seq = snd(snd(input)) = s
    let orig_expr = cs_snd(cs_snd(CompSpec::Id));
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(i, pair(acc, s));
    lemma_unpair2_pair(acc, s);

    //  check_line(pair(s, idx))
    let cl_input = CompSpec::CantorPair {
        left: Box::new(orig_expr),
        right: Box::new(idx_expr),
    };
    lemma_eval_pair(orig_expr, idx_expr, input);
    let cl_comp = cs_comp(check_line(), cl_input);
    lemma_eval_comp(check_line(), cl_input, input);

    //  valid * check_line_result
    lemma_eval_cs_and(valid_expr, cl_comp, input);

    //  idx + 1
    lemma_eval_add(idx_expr, cs_const(1), input);

    //  Build result pairs
    let new_valid_expr = cs_and(valid_expr, cl_comp);
    let new_idx_expr = CompSpec::Add { left: Box::new(idx_expr), right: Box::new(cs_const(1)) };
    lemma_eval_pair(new_valid_expr, new_idx_expr, input);
    lemma_eval_pair(snd_remaining, CompSpec::CantorPair {
        left: Box::new(new_valid_expr),
        right: Box::new(new_idx_expr),
    }, input);

    //  IfZero(fst(remaining) != 0): else branch
    lemma_eval_ifzero_else(fst_remaining, br_acc(),
        CompSpec::CantorPair {
            left: Box::new(snd_remaining),
            right: Box::new(CompSpec::CantorPair {
                left: Box::new(cs_and(valid_expr, cl_comp)),
                right: Box::new(new_idx_expr),
            }),
        },
        input);
}

///  Iteration on empty remaining stays stable.
proof fn lemma_cal_empty_stable(
    remaining: nat, valid: nat, idx: nat, s: nat, fuel: nat,
)
    requires
        unpair1(remaining) == 0,
    ensures ({
        let acc = pair(remaining, pair(valid, idx));
        compspec_iterate(cal_step(), fuel, acc, s) == acc
    }),
    decreases fuel,
{
    let acc = pair(remaining, pair(valid, idx));
    if fuel > 0 {
        lemma_cal_step_done((fuel - 1) as nat, remaining, valid, idx, s);
        lemma_compspec_iterate_unfold(cal_step(), fuel, acc, s);
        lemma_cal_empty_stable(remaining, valid, idx, s, (fuel - 1) as nat);
    }
}

///  Main iteration: for a valid proof, the BoundedRec iteration produces valid=nonzero.
///  Assumes: for each line i, check_line(pair(s, i)) != 0.
///  By induction on the number of remaining lines.
pub proof fn lemma_cal_iteration(
    s: nat, lines: Seq<nat>, start_idx: nat, valid: nat, fuel: nat,
)
    requires
        valid != 0,
        fuel >= lines.len(),
        //  Per-line: check_line returns nonzero for lines start_idx..start_idx+lines.len()
        forall|j: nat| #![trigger (start_idx + j)] j < lines.len() ==>
            eval_comp(check_line(), pair(s, (start_idx + j) as nat)) != 0,
    ensures ({
        let remaining = encode_nat_seq(lines);
        let acc = pair(remaining, pair(valid, start_idx));
        //  After iteration: valid_flag is nonzero
        unpair1(unpair2(compspec_iterate(cal_step(), fuel, acc, s))) != 0
    }),
    decreases lines.len(),
{
    let remaining = encode_nat_seq(lines);
    let acc = pair(remaining, pair(valid, start_idx));

    if lines.len() == 0 {
        //  Empty sequence: remaining = 0, unpair1(0) = 0 → done immediately
        assert(remaining == 0nat);
        assert(unpair1(0nat) == 0nat) by {
            assert(0nat * 1nat == 0nat) by(nonlinear_arith);
            lemma_unpair1_pair(0nat, 0nat);
        }
        lemma_cal_empty_stable(0nat, valid, start_idx, s, fuel);
        lemma_unpair2_pair(0nat, pair(valid, start_idx));
        lemma_unpair1_pair(valid, start_idx);
    } else {
        //  Non-empty: process one line, then recurse
        assert(fuel > 0);
        //  remaining = pair(lines[0]+1, encode_nat_seq(tail))
        let tail = lines.subrange(1, lines.len() as int);
        assert(remaining == pair(lines[0] + 1, encode_nat_seq(tail)));
        lemma_unpair1_pair(lines[0] + 1, encode_nat_seq(tail));
        assert(unpair1(remaining) == lines[0] + 1);
        assert(unpair1(remaining) != 0);

        //  One step: unfold and evaluate
        lemma_compspec_iterate_unfold(cal_step(), fuel, acc, s);
        lemma_cal_step_advance((fuel - 1) as nat, lines[0] + 1, encode_nat_seq(tail),
            valid, start_idx, s);
        //  step result = pair(encode_nat_seq(tail), pair(valid * cl, start_idx + 1))
        let cl = eval_comp(check_line(), pair(s, start_idx));
        //  cl != 0 from precondition with j=0
        assert(cl != 0) by {
            assert(0nat < lines.len());
            assert((start_idx + 0) == start_idx);
        }
        assert(valid >= 1nat);
        assert(cl >= 1nat);
        assert(valid * cl >= 1nat) by(nonlinear_arith)
            requires valid >= 1nat, cl >= 1nat;
        let new_valid = valid * cl;

        //  Recurse on tail with start_idx + 1
        //  Shift the forall: for j < tail.len(), check_line(pair(s, start_idx + 1 + j)) != 0
        assert forall|j: nat| #![trigger (start_idx + 1 + j)] j < tail.len() implies
            eval_comp(check_line(), pair(s, (start_idx + 1 + j) as nat)) != 0
        by {
            assert((j + 1) < lines.len());
            assert((start_idx + (j + 1)) == (start_idx + 1 + j));
        }
        lemma_cal_iteration(s, tail, (start_idx + 1) as nat, new_valid, (fuel - 1) as nat);
    }
}

///  Unfolding: eval_comp(check_all_lines(), s) == unpair1(unpair2(compspec_iterate(cal_step(), s, base, s))).
///  Bridges the BoundedRec to compspec_iterate via lemma_eval_bounded_rec.
pub proof fn lemma_cal_unfold(s: nat)
    ensures ({
        let base = pair(s, pair(1nat, 0nat));
        eval_comp(check_all_lines(), s)
            == unpair1(unpair2(compspec_iterate(cal_step(), s, base, s)))
    }),
{
    let base_expr = CompSpec::CantorPair {
        left: Box::new(CompSpec::Id),
        right: Box::new(CompSpec::CantorPair {
            left: Box::new(cs_const(1)),
            right: Box::new(cs_const(0)),
        }),
    };
    let step_expr = {
        let remaining = cs_fst(br_acc());
        let valid = cs_fst(cs_snd(br_acc()));
        let idx = cs_snd(cs_snd(br_acc()));
        let orig_seq = cs_snd(cs_snd(CompSpec::Id));
        CompSpec::IfZero {
            cond: Box::new(cs_fst(remaining)),
            then_br: Box::new(br_acc()),
            else_br: Box::new(CompSpec::CantorPair {
                left: Box::new(cs_snd(remaining)),
                right: Box::new(CompSpec::CantorPair {
                    left: Box::new(cs_and(
                        valid,
                        cs_comp(check_line(), CompSpec::CantorPair {
                            left: Box::new(orig_seq),
                            right: Box::new(idx),
                        }),
                    )),
                    right: Box::new(CompSpec::Add {
                        left: Box::new(idx),
                        right: Box::new(cs_const(1)),
                    }),
                }),
            }),
        }
    };

    //  check_all_lines() = cs_comp(cs_fst(cs_snd(Id)), BoundedRec{Id, base, step})
    lemma_eval_comp(cs_fst(cs_snd(CompSpec::Id)),
        CompSpec::BoundedRec {
            count_fn: Box::new(CompSpec::Id),
            base: Box::new(base_expr),
            step: Box::new(step_expr),
        }, s);

    //  Unfold BoundedRec
    lemma_eval_bounded_rec(CompSpec::Id, base_expr, step_expr, s);

    //  count = eval(Id, s) = s
    assert(eval_comp(CompSpec::Id, s) == s);

    //  base = eval(base_expr, s) = pair(s, pair(1, 0))
    lemma_eval_pair(CompSpec::Id, CompSpec::CantorPair {
        left: Box::new(cs_const(1)),
        right: Box::new(cs_const(0)),
    }, s);
    lemma_eval_pair(cs_const(1), cs_const(0), s);

    //  Extract valid_flag: cs_fst(cs_snd(Id)) applied to result
    let result = compspec_iterate(step_expr, s, pair(s, pair(1nat, 0nat)), s);
    lemma_eval_fst(cs_snd(CompSpec::Id), result);
    lemma_eval_snd(CompSpec::Id, result);
}

} //  verus!
