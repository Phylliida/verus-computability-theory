use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

///  Structure extraction for eq_subst_left checker.
///  From check_axiom_eq_subst_left(enc) accepting, derive:
///  - enc has tag 5 (Implies)
///  - eq_part has tag 0 (Eq)
///  - impl_part has tag 5 (Implies)
///  - check_eq_subst_pair accepts the substitution components
#[verifier::rlimit(3000)]
pub proof fn eq_subst_left_structure(enc: nat)
    requires eval_comp(check_axiom_eq_subst_left(), enc) != 0,
    ensures
        unpair1(enc) == 5,                                        //  outer Implies
        unpair1(unpair1(unpair2(enc))) == 0,                      //  eq_part tag = 0 (Eq)
        unpair1(unpair2(unpair2(enc))) == 5,                      //  impl_part tag = 5 (Implies)
        eval_comp(check_eq_subst_pair(),
            pair(
                unpair1(unpair2(unpair2(unpair2(enc)))),          //  left_subst
                pair(
                    unpair2(unpair2(unpair2(unpair2(enc)))),      //  right_subst
                    pair(
                        unpair1(unpair2(unpair1(unpair2(enc)))),  //  x_enc
                        unpair2(unpair2(unpair1(unpair2(enc))))   //  y_enc
                    )
                )
            )) != 0,
{
    hide(eval_comp);

    let outer_content = cs_snd(CompSpec::Id);
    let eq_part = cs_fst(outer_content);
    let impl_part = cs_snd(outer_content);
    let x = cs_fst(cs_snd(eq_part));
    let y = cs_snd(cs_snd(eq_part));
    let left_subst = cs_fst(cs_snd(impl_part));
    let right_subst = cs_snd(cs_snd(impl_part));

    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(eq_part), cs_const(0));
    let c3 = cs_eq(cs_fst(impl_part), cs_const(5));
    let c4 = cs_comp(check_eq_subst_pair(),
        cs_pair(left_subst, cs_pair(right_subst, cs_pair(x, y))));

    //  Decompose nested cs_and: c1 ∧ (c2 ∧ (c3 ∧ c4))
    assert(eval_comp(c1, enc) != 0 && eval_comp(cs_and(c2, cs_and(c3, c4)), enc) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c4)), enc);
        if eval_comp(c1, enc) == 0 {
            assert(0nat * eval_comp(cs_and(c2, cs_and(c3, c4)), enc) == 0) by (nonlinear_arith);
        }
        if eval_comp(cs_and(c2, cs_and(c3, c4)), enc) == 0 {
            assert(eval_comp(c1, enc) * 0nat == 0) by (nonlinear_arith);
        }
    }
    assert(eval_comp(c2, enc) != 0 && eval_comp(cs_and(c3, c4), enc) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c2, cs_and(c3, c4), enc);
        if eval_comp(c2, enc) == 0 {
            assert(0nat * eval_comp(cs_and(c3, c4), enc) == 0) by (nonlinear_arith);
        }
        if eval_comp(cs_and(c3, c4), enc) == 0 {
            assert(eval_comp(c2, enc) * 0nat == 0) by (nonlinear_arith);
        }
    }
    assert(eval_comp(c3, enc) != 0 && eval_comp(c4, enc) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c3, c4, enc);
        if eval_comp(c3, enc) == 0 {
            assert(0nat * eval_comp(c4, enc) == 0) by (nonlinear_arith);
        }
        if eval_comp(c4, enc) == 0 {
            assert(eval_comp(c3, enc) * 0nat == 0) by (nonlinear_arith);
        }
    }

    //  c1: outer tag = 5
    assert(unpair1(enc) == 5) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_fst(CompSpec::Id, enc);
    }

    //  c2: eq_part tag = 0
    assert(unpair1(unpair1(unpair2(enc))) == 0) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(eq_part), cs_const(0), enc);
        lemma_eval_fst(eq_part, enc);
        lemma_eval_fst(outer_content, enc);
        lemma_eval_snd(CompSpec::Id, enc);
    }

    //  c3: impl_part tag = 5
    assert(unpair1(unpair2(unpair2(enc))) == 5) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(impl_part), cs_const(5), enc);
        lemma_eval_fst(impl_part, enc);
        lemma_eval_snd(outer_content, enc);
        lemma_eval_snd(CompSpec::Id, enc);
    }

    //  c4: check_eq_subst_pair acceptance
    assert(eval_comp(check_eq_subst_pair(),
        pair(
            unpair1(unpair2(unpair2(unpair2(enc)))),
            pair(
                unpair2(unpair2(unpair2(unpair2(enc)))),
                pair(
                    unpair1(unpair2(unpair1(unpair2(enc)))),
                    unpair2(unpair2(unpair1(unpair2(enc))))
                )
            )
        )) != 0) by {
        reveal(eval_comp);
        lemma_eval_comp(check_eq_subst_pair(),
            cs_pair(left_subst, cs_pair(right_subst, cs_pair(x, y))), enc);
        lemma_eval_pair(left_subst, cs_pair(right_subst, cs_pair(x, y)), enc);
        lemma_eval_pair(right_subst, cs_pair(x, y), enc);
        lemma_eval_pair(x, y, enc);
        //  left_subst = fst(snd(impl_part)) = fst(snd(snd(snd(Id))))
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_snd(outer_content, enc);
        lemma_eval_fst(cs_snd(impl_part), enc);
        lemma_eval_snd(impl_part, enc);
        //  right_subst = snd(snd(impl_part))
        lemma_eval_snd(cs_snd(impl_part), enc);
        //  x = fst(snd(eq_part)) = fst(snd(fst(snd(Id))))
        lemma_eval_fst(outer_content, enc);
        lemma_eval_fst(cs_snd(eq_part), enc);
        lemma_eval_snd(eq_part, enc);
        //  y = snd(snd(eq_part))
        lemma_eval_snd(cs_snd(eq_part), enc);
    }
}

} // verus!
