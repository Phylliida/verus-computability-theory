use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::*;
use crate::zfc::*;
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
pub proof fn lemma_cal_step_done(
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
pub proof fn lemma_cal_step_advance(
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
pub proof fn lemma_cal_empty_stable(
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

///  The advance step in seq_elem BoundedRec: cs_snd(br_acc()) takes unpair2 of current position.
proof fn lemma_seq_advance_step(iter: nat, acc: nat, orig: nat)
    ensures
        eval_comp(cs_snd(br_acc()), pair(iter, pair(acc, orig))) == unpair2(acc),
{
    let input = pair(iter, pair(acc, orig));
    lemma_eval_br_acc(iter, acc, orig);
    lemma_eval_snd(br_acc(), input);
}

///  After i advances through encoded sequence, we reach the i-th tail.
proof fn lemma_seq_advance_iter(s: Seq<nat>, i: nat, fuel: nat, orig: nat)
    requires
        i <= s.len(),
        fuel >= i,
    ensures
        compspec_iterate(cs_snd(br_acc()), fuel, encode_nat_seq(s), orig)
            == compspec_iterate(cs_snd(br_acc()), (fuel - i) as nat,
                encode_nat_seq(s.subrange(i as int, s.len() as int)), orig),
    decreases i,
{
    if i == 0 {
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        assert(fuel > 0);
        assert(s.len() > 0);
        //  One step: unfold
        lemma_compspec_iterate_unfold(cs_snd(br_acc()), fuel, encode_nat_seq(s), orig);
        //  step result = unpair2(encode_nat_seq(s)) = encode_nat_seq(tail)
        lemma_seq_advance_step((fuel - 1) as nat, encode_nat_seq(s), orig);
        lemma_encode_nat_seq_structure(s);
        let tail = s.subrange(1, s.len() as int);
        //  Recurse on tail with i-1
        lemma_seq_advance_iter(tail, (i - 1) as nat, (fuel - 1) as nat, orig);
        //  tail.subrange(i-1, tail.len()) =~= s.subrange(i, s.len())
        assert(tail.subrange((i - 1) as int, tail.len() as int)
            =~= s.subrange(i as int, s.len() as int));
    }
}

///  seq_elem_comp correctly extracts the i-th element of an encoded sequence.
pub proof fn lemma_seq_elem_correct(s: Seq<nat>, i: nat)
    requires
        i < s.len(),
    ensures
        eval_comp(seq_elem_comp(), pair(encode_nat_seq(s), i)) == s[i as int],
{
    let enc = encode_nat_seq(s);
    let input = pair(enc, i);

    //  seq_elem_comp = cs_comp(Pred, cs_fst(BoundedRec{count=i, base=enc, step=cs_snd(br_acc())}))
    //  Step 1: unfold BoundedRec to compspec_iterate
    lemma_eval_bounded_rec(cs_snd(CompSpec::Id), cs_fst(CompSpec::Id), cs_snd(br_acc()), input);
    //  count = eval(cs_snd(Id), input) = i
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(enc, i);
    //  base = eval(cs_fst(Id), input) = enc
    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(enc, i);

    //  Step 2: after i advances, we're at encode_nat_seq(s.subrange(i, s.len()))
    lemma_seq_advance_iter(s, i, i, input);
    //  compspec_iterate(step, i, enc, input) == compspec_iterate(step, 0, encode_nat_seq(s[i..]), input)
    //  = encode_nat_seq(s[i..])
    let tail_i = s.subrange(i as int, s.len() as int);
    assert(tail_i.len() > 0);
    assert(tail_i[0] == s[i as int]);

    //  Step 3: extract via cs_fst + Pred
    //  cs_fst of encode_nat_seq(tail_i) = unpair1(encode_nat_seq(tail_i)) = tail_i[0] + 1
    lemma_encode_nat_seq_structure(tail_i);
    let br_result = encode_nat_seq(tail_i);
    lemma_eval_fst(CompSpec::BoundedRec {
        count_fn: Box::new(cs_snd(CompSpec::Id)),
        base: Box::new(cs_fst(CompSpec::Id)),
        step: Box::new(cs_snd(br_acc())),
    }, input);
    //  Pred(tail_i[0] + 1) = tail_i[0] = s[i]
    lemma_eval_comp(CompSpec::Pred, cs_fst(CompSpec::BoundedRec {
        count_fn: Box::new(cs_snd(CompSpec::Id)),
        base: Box::new(cs_fst(CompSpec::Id)),
        step: Box::new(cs_snd(br_acc())),
    }), input);
    lemma_eval_pred(tail_i[0] + 1);
}

///  line_formula_comp correctly extracts the formula encoding from a proof line.
///  line_formula_comp() = cs_fst(seq_elem_comp())
pub proof fn lemma_line_formula_correct(s: Seq<nat>, i: nat)
    requires
        i < s.len(),
    ensures
        eval_comp(line_formula_comp(), pair(encode_nat_seq(s), i))
            == unpair1(s[i as int]),
{
    lemma_seq_elem_correct(s, i);
    //  seq_elem = s[i]
    //  line_formula_comp = cs_fst(seq_elem_comp()) = unpair1(seq_elem) = unpair1(s[i])
    lemma_eval_fst(seq_elem_comp(), pair(encode_nat_seq(s), i));
}

///  For encoded proof lines, line_formula extracts encode(formula).
pub proof fn lemma_proof_line_formula(p: Proof, i: nat)
    requires
        i < p.lines.len(),
    ensures ({
        let s = encode_proof(p);
        let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));
        eval_comp(line_formula_comp(), pair(s, i))
            == encode(p.lines[i as int].0)
    }),
{
    let lines = Seq::new(p.lines.len(), |j: int| encode_line(p.lines[j]));
    lemma_line_formula_correct(lines, i);
    //  unpair1(lines[i]) = unpair1(encode_line(p.lines[i]))
    //  = unpair1(pair(encode(formula), encode_justification))
    //  = encode(formula)
    lemma_unpair1_pair(encode(p.lines[i as int].0),
        encode_justification(p.lines[i as int].1));
}

///  lookup_formula_at correctly looks up a formula in the encoded proof.
pub proof fn lemma_lookup_formula_correct(p: Proof, seq_enc: nat, i: nat)
    requires
        seq_enc == encode_proof(p),
        i < p.lines.len(),
    ensures
        eval_comp(
            lookup_formula_at(
                CompSpec::Const { value: seq_enc },
                CompSpec::Const { value: i },
            ),
            0nat,  //  dummy input — lookup_formula_at captures seq and idx via const
        ) == encode(p.lines[i as int].0),
{
    //  lookup_formula_at(seq_expr, idx_expr) = cs_comp(line_formula_comp(), CantorPair{seq_expr, idx_expr})
    //  Applied to dummy input: eval(CantorPair{Const(seq_enc), Const(i)}, 0) = pair(seq_enc, i)
    //  Then: eval(line_formula_comp(), pair(seq_enc, i)) = encode(formula)
    lemma_eval_comp(line_formula_comp(), CompSpec::CantorPair {
        left: Box::new(CompSpec::Const { value: seq_enc }),
        right: Box::new(CompSpec::Const { value: i }),
    }, 0nat);
    lemma_eval_pair(
        CompSpec::Const { value: seq_enc },
        CompSpec::Const { value: i },
        0nat);
    lemma_proof_line_formula(p, i);
}

///  ci_formula correctly extracts formula_enc from check input.
///  Input format: pair(pair(formula_enc, just_content), pair(seq_enc, line_idx))
pub proof fn lemma_ci_formula_eval(
    formula_enc: nat, just_content: nat, seq_enc: nat, line_idx: nat,
)
    ensures
        eval_comp(ci_formula(),
            pair(pair(formula_enc, just_content), pair(seq_enc, line_idx)))
            == formula_enc,
{
    let input = pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_eval_fst(cs_fst(CompSpec::Id), input);
    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_unpair1_pair(formula_enc, just_content);
}

///  ci_just_content correctly extracts justification content.
pub proof fn lemma_ci_just_content_eval(
    formula_enc: nat, just_content: nat, seq_enc: nat, line_idx: nat,
)
    ensures
        eval_comp(ci_just_content(),
            pair(pair(formula_enc, just_content), pair(seq_enc, line_idx)))
            == just_content,
{
    let input = pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_eval_snd(cs_fst(CompSpec::Id), input);
    lemma_eval_fst(CompSpec::Id, input);
    lemma_unpair1_pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_unpair2_pair(formula_enc, just_content);
}

///  ci_seq correctly extracts seq_enc.
pub proof fn lemma_ci_seq_eval(
    formula_enc: nat, just_content: nat, seq_enc: nat, line_idx: nat,
)
    ensures
        eval_comp(ci_seq(),
            pair(pair(formula_enc, just_content), pair(seq_enc, line_idx)))
            == seq_enc,
{
    let input = pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_eval_fst(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_unpair1_pair(seq_enc, line_idx);
}

///  ci_idx correctly extracts line_idx.
pub proof fn lemma_ci_idx_eval(
    formula_enc: nat, just_content: nat, seq_enc: nat, line_idx: nat,
)
    ensures
        eval_comp(ci_idx(),
            pair(pair(formula_enc, just_content), pair(seq_enc, line_idx)))
            == line_idx,
{
    let input = pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_eval_snd(cs_snd(CompSpec::Id), input);
    lemma_eval_snd(CompSpec::Id, input);
    lemma_unpair2_pair(pair(formula_enc, just_content), pair(seq_enc, line_idx));
    lemma_unpair2_pair(seq_enc, line_idx);
}

///  check_modus_ponens returns nonzero for valid modus ponens steps.
///  Input: pair(pair(formula_enc, pair(premise_idx, impl_idx)), pair(seq_enc, line_idx))
pub proof fn lemma_check_mp_correct(
    p: Proof, i: nat, premise_line: nat, implication_line: nat,
)
    requires
        encode_proof(p) == encode_proof(p),  //  trivial, for trigger
        i < p.lines.len(),
        premise_line < i,
        implication_line < i,
        p.lines[implication_line as int].0 == mk_implies(
            p.lines[premise_line as int].0, p.lines[i as int].0),
    ensures ({
        let s = encode_proof(p);
        let formula_enc = encode(p.lines[i as int].0);
        let just_content = pair(premise_line, implication_line);
        let input = pair(pair(formula_enc, just_content), pair(s, i));
        eval_comp(check_modus_ponens(), input) != 0
    }),
{
    let s = encode_proof(p);
    let formula_enc = encode(p.lines[i as int].0);
    let just_content = pair(premise_line, implication_line);
    let input = pair(pair(formula_enc, just_content), pair(s, i));

    //  Extract components via ci_* helpers
    lemma_ci_formula_eval(formula_enc, just_content, s, i);
    lemma_ci_just_content_eval(formula_enc, just_content, s, i);
    lemma_ci_seq_eval(formula_enc, just_content, s, i);
    lemma_ci_idx_eval(formula_enc, just_content, s, i);

    //  Extract premise_idx and impl_idx from just_content
    lemma_eval_fst(ci_just_content(), input);
    lemma_eval_snd(ci_just_content(), input);
    lemma_unpair1_pair(premise_line, implication_line);
    lemma_unpair2_pair(premise_line, implication_line);

    //  check_premise_bound: premise_line < i → 1
    lemma_eval_lt(cs_fst(ci_just_content()), ci_idx(), input);
    //  check_impl_bound: implication_line < i → 1
    lemma_eval_lt(cs_snd(ci_just_content()), ci_idx(), input);

    //  lookup_formula_at inside check_modus_ponens:
    //  premise_formula = lookup_formula_at(ci_seq(), cs_fst(ci_just_content()))
    //  = cs_comp(line_formula_comp(), CantorPair{ci_seq(), cs_fst(ci_just_content())})
    let premise_idx_expr = cs_fst(ci_just_content());
    let impl_idx_expr = cs_snd(ci_just_content());
    let seq_expr = ci_seq();
    let idx_expr = ci_idx();

    //  Evaluate premise lookup
    let premise_pair = CompSpec::CantorPair {
        left: Box::new(seq_expr), right: Box::new(premise_idx_expr),
    };
    lemma_eval_pair(seq_expr, premise_idx_expr, input);
    lemma_eval_comp(line_formula_comp(), premise_pair, input);
    //  eval(lookup(premise)) = eval(line_formula, pair(s, premise_line))
    lemma_proof_line_formula(p, premise_line);

    //  Evaluate implication lookup
    let impl_pair = CompSpec::CantorPair {
        left: Box::new(seq_expr), right: Box::new(impl_idx_expr),
    };
    lemma_eval_pair(seq_expr, impl_idx_expr, input);
    lemma_eval_comp(line_formula_comp(), impl_pair, input);
    lemma_proof_line_formula(p, implication_line);

    //  Expected implication: pair(5, pair(premise_formula_enc, formula_enc))
    let premise = p.lines[premise_line as int].0;
    let impl_formula = p.lines[implication_line as int].0;
    assert(impl_formula == mk_implies(premise, p.lines[i as int].0));
    //  encode(Implies(premise, formula)) = pair(5, pair(encode(premise), encode(formula)))

    //  Evaluate expected_impl CompSpec
    let premise_formula_expr = lookup_formula_at(seq_expr, premise_idx_expr);
    let expected_inner = CompSpec::CantorPair {
        left: Box::new(premise_formula_expr),
        right: Box::new(ci_formula()),
    };
    let expected_impl = CompSpec::CantorPair {
        left: Box::new(cs_const(5)),
        right: Box::new(expected_inner),
    };
    lemma_eval_pair(premise_formula_expr, ci_formula(), input);
    lemma_eval_pair(cs_const(5), expected_inner, input);

    //  cs_eq: impl_formula_enc == expected_impl_enc
    let impl_formula_expr = lookup_formula_at(seq_expr, impl_idx_expr);
    lemma_eval_eq(impl_formula_expr, expected_impl, input);

    //  Compose: cs_and(bound1, cs_and(bound2, eq_check))
    let bound1 = cs_lt(premise_idx_expr, idx_expr);
    let bound2 = cs_lt(impl_idx_expr, idx_expr);
    let eq_check = cs_eq(impl_formula_expr, expected_impl);
    lemma_eval_cs_and(bound2, eq_check, input);
    lemma_eval_cs_and(bound1, cs_and(bound2, eq_check), input);
}

///  check_generalization returns nonzero for valid generalization steps.
pub proof fn lemma_check_gen_correct(
    p: Proof, i: nat, premise_line: nat, var: nat,
)
    requires
        i < p.lines.len(),
        premise_line < i,
        p.lines[i as int].0 == mk_forall(var, p.lines[premise_line as int].0),
    ensures ({
        let s = encode_proof(p);
        let formula_enc = encode(p.lines[i as int].0);
        let just_content = pair(premise_line, var);
        let input = pair(pair(formula_enc, just_content), pair(s, i));
        eval_comp(check_generalization(), input) != 0
    }),
{
    let s = encode_proof(p);
    let formula_enc = encode(p.lines[i as int].0);
    let just_content = pair(premise_line, var);
    let input = pair(pair(formula_enc, just_content), pair(s, i));

    lemma_ci_formula_eval(formula_enc, just_content, s, i);
    lemma_ci_just_content_eval(formula_enc, just_content, s, i);
    lemma_ci_seq_eval(formula_enc, just_content, s, i);
    lemma_ci_idx_eval(formula_enc, just_content, s, i);

    lemma_eval_fst(ci_just_content(), input);
    lemma_eval_snd(ci_just_content(), input);
    lemma_unpair1_pair(premise_line, var);
    lemma_unpair2_pair(premise_line, var);

    //  check_bound: premise_line < i → 1
    let premise_idx_expr = cs_fst(ci_just_content());
    let var_expr = cs_snd(ci_just_content());
    lemma_eval_lt(premise_idx_expr, ci_idx(), input);

    //  Lookup premise formula
    let seq_expr = ci_seq();
    let premise_pair = CompSpec::CantorPair {
        left: Box::new(seq_expr), right: Box::new(premise_idx_expr),
    };
    lemma_eval_pair(seq_expr, premise_idx_expr, input);
    lemma_eval_comp(line_formula_comp(), premise_pair, input);
    lemma_proof_line_formula(p, premise_line);

    //  Expected: pair(7, pair(var, premise_formula))
    //  encode(Forall(var, premise)) = pair(7, pair(var, encode(premise)))
    let premise_formula_expr = lookup_formula_at(seq_expr, premise_idx_expr);
    let expected_inner = CompSpec::CantorPair {
        left: Box::new(var_expr),
        right: Box::new(premise_formula_expr),
    };
    let expected = CompSpec::CantorPair {
        left: Box::new(cs_const(7)),
        right: Box::new(expected_inner),
    };
    lemma_eval_pair(var_expr, premise_formula_expr, input);
    lemma_eval_pair(cs_const(7), expected_inner, input);

    //  cs_eq: formula_enc == expected
    lemma_eval_eq(ci_formula(), expected, input);

    //  Compose: cs_and(bound, eq)
    let bound = cs_lt(premise_idx_expr, ci_idx());
    let eq_check = cs_eq(ci_formula(), expected);
    lemma_eval_cs_and(bound, eq_check, input);
}

//  TODO: check_zfc_axiom correctness — needs per-axiom eval helpers in separate file
//  TODO: check_logic_axiom correctness — needs per-schema eval helpers in separate file
//  Pattern: for each axiom X, prove eval_comp(enc_X(), input) == encode(X_axiom())
//  Then cs_or chain gives nonzero for the matching axiom.

} //  verus!
