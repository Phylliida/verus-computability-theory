use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

//  Helper: extract individual factors from a cs_and chain
proof fn lemma_cs_and_nonzero_left(a: CompSpec, b: CompSpec, s: nat)
    requires eval_comp(cs_and(a, b), s) != 0,
    ensures eval_comp(a, s) != 0,
{
    lemma_eval_cs_and(a, b, s);
    //  eval_comp(cs_and(a,b), s) == eval_comp(a,s) * eval_comp(b,s)
    //  product != 0 → a != 0
    if eval_comp(a, s) == 0 {
        assert(eval_comp(a, s) * eval_comp(b, s) == 0) by (nonlinear_arith)
            requires eval_comp(a, s) == 0nat;
    }
}

proof fn lemma_cs_and_nonzero_right(a: CompSpec, b: CompSpec, s: nat)
    requires eval_comp(cs_and(a, b), s) != 0,
    ensures eval_comp(b, s) != 0,
{
    lemma_eval_cs_and(a, b, s);
    if eval_comp(b, s) == 0 {
        assert(eval_comp(a, s) * eval_comp(b, s) == 0) by (nonlinear_arith)
            requires eval_comp(b, s) == 0nat;
    }
}

//  iff_elim_right structure — isolated in own module to avoid sibling pollution

#[verifier::rlimit(1500)]
pub proof fn iff_elim_right_structure(enc: nat)
    requires eval_comp(check_axiom_iff_elim_right(), enc) != 0,
    ensures
        unpair1(enc) == 5,
        unpair1(unpair1(unpair2(enc))) == 6,
        unpair1(unpair2(unpair2(enc))) == 5,
        //  c4: fst(snd(iff)) == snd(snd(impl))
        unpair1(unpair2(unpair1(unpair2(enc)))) == unpair2(unpair2(unpair2(unpair2(enc)))),
        //  c5: snd(snd(iff)) == fst(snd(impl))
        unpair2(unpair2(unpair1(unpair2(enc)))) == unpair1(unpair2(unpair2(unpair2(enc)))),
{
    hide(eval_comp);
    let outer_content = cs_snd(CompSpec::Id);
    let iff_part = cs_fst(outer_content);
    let impl_part = cs_snd(outer_content);
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(iff_part), cs_const(6));
    let c3 = cs_eq(cs_fst(impl_part), cs_const(5));
    //  MUST match checker's argument order exactly!
    let c4 = cs_eq(cs_fst(cs_snd(iff_part)), cs_snd(cs_snd(impl_part)));
    let c5 = cs_eq(cs_snd(cs_snd(iff_part)), cs_fst(cs_snd(impl_part)));

    assert(unpair1(enc) == 5
        && unpair1(unpair1(unpair2(enc))) == 6
        && unpair1(unpair2(unpair2(enc))) == 5) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c4, c5, enc);
        lemma_eval_cs_and(c3, cs_and(c4, c5), enc);
        lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, c5)), enc);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(iff_part), cs_const(6), enc);
        lemma_eval_eq(cs_fst(impl_part), cs_const(5), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
        lemma_eval_fst(iff_part, enc);
        lemma_eval_fst(impl_part, enc);
    }

    //  Establish intermediate eval values for navigation
    assert(eval_comp(cs_snd(iff_part), enc) == unpair2(unpair1(unpair2(enc)))
        && eval_comp(cs_snd(impl_part), enc) == unpair2(unpair2(unpair2(enc)))) by {
        reveal(eval_comp);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(iff_part, enc);
        lemma_eval_snd(impl_part, enc);
    }

    //  Unpack cs_and chain → c4 and c5 nonzero (using helpers, no reveal needed)
    lemma_cs_and_nonzero_right(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), enc);
    lemma_cs_and_nonzero_right(c2, cs_and(c3, cs_and(c4, c5)), enc);
    lemma_cs_and_nonzero_right(c3, cs_and(c4, c5), enc);
    lemma_cs_and_nonzero_left(c4, c5, enc);
    lemma_cs_and_nonzero_right(c4, c5, enc);
    //  Now ambient has: eval_comp(c4, enc) != 0 AND eval_comp(c5, enc) != 0

    //  c4 equality: fst(snd(iff)) == snd(snd(impl))
    assert(unpair1(unpair2(unpair1(unpair2(enc)))) == unpair2(unpair2(unpair2(unpair2(enc))))) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(cs_snd(iff_part)), cs_snd(cs_snd(impl_part)), enc);
        lemma_eval_fst(cs_snd(iff_part), enc);
        lemma_eval_snd(cs_snd(impl_part), enc);
    }

    //  c5 equality: snd(snd(iff)) == fst(snd(impl))
    assert(unpair2(unpair2(unpair1(unpair2(enc)))) == unpair1(unpair2(unpair2(unpair2(enc))))) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_snd(cs_snd(iff_part)), cs_fst(cs_snd(impl_part)), enc);
        lemma_eval_snd(cs_snd(iff_part), enc);
        lemma_eval_fst(cs_snd(impl_part), enc);
    }
}

} //  verus!
