use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_all_lines_helpers::*;
use crate::proof_encoding::*;

verus! {

//  ====================================================================
//  Forward iteration: check_all_lines nonzero → each check_line nonzero
//  ====================================================================

///  Product of check_line results for lines start..start+count.
pub open spec fn check_line_product(s: nat, start: nat, count: nat) -> nat
    decreases count,
{
    if count == 0 { 1 }
    else {
        eval_comp(check_line(), pair(s, start))
        * check_line_product(s, (start + 1) as nat, (count - 1) as nat)
    }
}

///  The iteration computes valid * product of check_lines.
proof fn lemma_cal_iteration_product(
    s: nat, lines: Seq<nat>, start_idx: nat, valid: nat, fuel: nat,
)
    requires
        fuel >= lines.len(),
    ensures ({
        let remaining = encode_nat_seq(lines);
        let acc = pair(remaining, pair(valid, start_idx));
        unpair1(unpair2(compspec_iterate(cal_step(), fuel, acc, s)))
            == valid * check_line_product(s, start_idx, lines.len())
    }),
    decreases lines.len(),
{
    let remaining = encode_nat_seq(lines);
    let acc = pair(remaining, pair(valid, start_idx));

    if lines.len() == 0 {
        //  Empty: iteration returns acc unchanged, product = 1
        assert(remaining == 0nat);
        assert(unpair1(0nat) == 0nat) by {
            assert(0nat * 1nat == 0nat) by (nonlinear_arith);
            lemma_unpair1_pair(0nat, 0nat);
        }
        lemma_cal_empty_stable(0nat, valid, start_idx, s, fuel);
        lemma_unpair2_pair(0nat, pair(valid, start_idx));
        lemma_unpair1_pair(valid, start_idx);
        assert(valid * 1 == valid) by (nonlinear_arith);
    } else {
        //  Non-empty: one step + recurse
        let tail = lines.subrange(1, lines.len() as int);
        lemma_unpair1_pair(lines[0] + 1, encode_nat_seq(tail));
        assert(unpair1(remaining) == lines[0] + 1);
        assert(unpair1(remaining) != 0);

        lemma_compspec_iterate_unfold(cal_step(), fuel, acc, s);
        lemma_cal_step_advance((fuel - 1) as nat, lines[0] + 1, encode_nat_seq(tail),
            valid, start_idx, s);

        let cl = eval_comp(check_line(), pair(s, start_idx));
        let new_valid = valid * cl;

        //  Recurse on tail
        lemma_cal_iteration_product(s, tail, (start_idx + 1) as nat, new_valid, (fuel - 1) as nat);

        //  Unfold product definition for lines.len() > 0
        assert(check_line_product(s, start_idx, lines.len())
            == cl * check_line_product(s, (start_idx + 1) as nat, (lines.len() - 1) as nat));

        //  Chain: result == new_valid * product(tail) == (valid * cl) * product(tail)
        //       == valid * (cl * product(tail)) == valid * product(full)
        assert(new_valid * check_line_product(s, (start_idx + 1) as nat, tail.len())
            == valid * check_line_product(s, start_idx, lines.len())) by (nonlinear_arith)
            requires
                new_valid == valid * cl,
                check_line_product(s, start_idx, lines.len())
                    == cl * check_line_product(s, (start_idx + 1) as nat, tail.len()),
                tail.len() == (lines.len() - 1) as nat;
    }
}

///  Nonzero product implies each factor nonzero.
proof fn lemma_product_nonzero_each(s: nat, start: nat, count: nat)
    requires check_line_product(s, start, count) != 0,
    ensures forall|j: nat| j < count ==>
        #[trigger] eval_comp(check_line(), pair(s, (start + j) as nat)) != 0,
    decreases count,
{
    if count > 0 {
        //  product = cl * rest_product. Nonzero → both nonzero.
        let cl = eval_comp(check_line(), pair(s, start));
        let rest = check_line_product(s, (start + 1) as nat, (count - 1) as nat);
        assert(cl * rest != 0);
        if cl == 0 {
            assert(cl * rest == 0) by (nonlinear_arith)
                requires cl == 0nat;
        }
        if rest == 0 {
            assert(cl * rest == 0) by (nonlinear_arith)
                requires rest == 0nat;
        }
        assert(cl != 0 && rest != 0);
        lemma_product_nonzero_each(s, (start + 1) as nat, (count - 1) as nat);
        //  From IH: for j < count-1, check_line(start+1+j) != 0
        //  For j == 0: cl = check_line(start) != 0
        //  For j > 0: check_line(start+j) = check_line(start+1+(j-1)) != 0
        assert forall|j: nat| j < count implies
            #[trigger] eval_comp(check_line(), pair(s, (start + j) as nat)) != 0
        by {
            if j == 0 {
            } else {
                assert((j - 1) < (count - 1));
                assert(((start + 1) + (j - 1)) == (start + j));
            }
        }
    }
}

///  Main forward iteration lemma: check_all_lines nonzero → each check_line nonzero.
pub proof fn lemma_check_all_lines_forward(s: nat, lines: Seq<nat>)
    requires
        s == encode_nat_seq(lines),
        eval_comp(check_all_lines(), s) != 0,
    ensures
        forall|i: nat| i < lines.len() ==>
            #[trigger] eval_comp(check_line(), pair(s, i)) != 0,
{
    //  Unfold check_all_lines to iteration
    lemma_cal_unfold(s);
    let base = pair(s, pair(1nat, 0nat));

    //  Iteration computes 1 * product
    lemma_encode_nat_seq_ge_len(lines);
    lemma_cal_iteration_product(s, lines, 0nat, 1nat, s);

    //  check_all_lines result == 1 * product == product
    //  product != 0 (since check_all_lines != 0)
    assert(check_line_product(s, 0nat, lines.len()) != 0) by (nonlinear_arith)
        requires
            unpair1(unpair2(compspec_iterate(cal_step(), s, base, s)))
                == 1 * check_line_product(s, 0nat, lines.len()),
            unpair1(unpair2(compspec_iterate(cal_step(), s, base, s))) != 0;

    //  Extract individual factors
    lemma_product_nonzero_each(s, 0nat, lines.len());
    //  Bridge: (0 + i) == i
    assert forall|i: nat| i < lines.len() implies
        #[trigger] eval_comp(check_line(), pair(s, i)) != 0
    by {
        assert((0nat + i) == i);
    }
}

} //  verus!
