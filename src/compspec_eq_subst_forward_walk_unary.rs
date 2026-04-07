use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_eq_subst_forward_step2::{lemma_eq_subst_forward_step_unary, lemma_esb_forward_unary_tags_match};
use crate::compspec_eq_subst_forward_walk::{lemma_esb_valid_zero_stable, lemma_eq_subst_forward_walk};

verus! {

///  Match-based requires: iterate inside match to reduce Z3 termination encoding.
#[verifier::rlimit(3000)]
pub proof fn lemma_eq_subst_forward_walk_unary(
    f1: Formula, f2: Formula, x_enc: nat, y_enc: nat,
    rest: nat, fuel: nat,
)
    requires
        f1 matches Formula::Not{..},
        ({
            match f1 {
                Formula::Not { sub } => {
                    fuel >= formula_size(f1) &&
                    unpair2(
                        compspec_iterate(check_eq_subst_step(), fuel,
                            pair(pair(pair(encode(f1), encode(f2)) + 1, rest), 1nat),
                            pair(encode(f1), pair(encode(f2), pair(x_enc, y_enc))))
                    ) != 0
                },
                _ => false,
            }
        }),
    ensures
        eq_subst_compatible(f1, f2, Term::Var { index: x_enc }, Term::Var { index: y_enc }),
    decreases f1, 0nat,
{
    hide(compspec_iterate);
    match f1 {
        Formula::Not { sub: s1 } => {
            let f1_enc = encode(f1);
            let f2_enc = encode(f2);
            let acc0 = pair(pair(pair(f1_enc, f2_enc) + 1, rest), 1nat);
            let s = pair(f1_enc, pair(f2_enc, pair(x_enc, y_enc)));
            lemma_formula_size_pos(f1);

            lemma_encode_is_pair(f1);
            lemma_unpair1_pair(2nat, encode(*s1));
            lemma_unpair2_pair(2nat, encode(*s1));

            //  Step valid != 0
            assert(unpair2(eval_comp(check_eq_subst_step(),
                pair((fuel - 1) as nat, pair(acc0, s)))) != 0) by {
                reveal(compspec_iterate);
                lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                let sr = eval_comp(check_eq_subst_step(), pair((fuel - 1) as nat, pair(acc0, s)));
                if unpair2(sr) == 0 {
                    lemma_pair_surjective(sr);
                    lemma_esb_valid_zero_stable((fuel - 1) as nat, unpair1(sr), s);
                    lemma_unpair2_pair(unpair1(sr), 0nat);
                }
            };

            //  Tags match → f2 is Not
            lemma_esb_forward_unary_tags_match(f1_enc, f2_enc,
                rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
            lemma_encode_is_pair(f2);
            lemma_unpair1_pair(formula_tag(f2), formula_content(f2));

            match f2 {
                Formula::Not { sub: s2 } => {
                    lemma_unpair1_pair(2nat, encode(*s2));
                    lemma_unpair2_pair(2nat, encode(*s2));
                    lemma_eq_subst_forward_step_unary(f1_enc, f2_enc,
                        rest, 1, (fuel - 1) as nat, f1_enc, f2_enc, x_enc, y_enc);
                    assert(unpair2(compspec_iterate(check_eq_subst_step(), (fuel - 1) as nat,
                        pair(pair(pair(encode(*s1), encode(*s2)) + 1, rest), 1nat), s)) != 0) by {
                        reveal(compspec_iterate);
                        lemma_compspec_iterate_unfold(check_eq_subst_step(), fuel, acc0, s);
                    };
                    lemma_eq_subst_forward_walk(*s1, *s2, x_enc, y_enc, rest, (fuel - 1) as nat);
                },
                _ => { /* formula_tag(f2) == 2 but not Not → impossible */ },
            }
        },
        _ => {},
    }
}

} // verus!
