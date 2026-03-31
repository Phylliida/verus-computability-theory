use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;

verus! {

//  ====================================================================
//  Structural fact extraction from checker acceptance.
//  Each function takes a checker precondition and produces unpair facts.
//  ISOLATED from decode_formula to avoid context pollution.
//  ====================================================================

pub proof fn identity_structure(enc: nat)
    requires eval_comp(check_axiom_identity(), enc) != 0,
    ensures unpair1(enc) == 5, unpair1(unpair2(enc)) == unpair2(unpair2(enc)),
{
    hide(eval_comp);
    assert(unpair1(enc) == 5 && unpair1(unpair2(enc)) == unpair2(unpair2(enc))) by {
        reveal(eval_comp);
        lemma_eval_cs_and(
            cs_eq(cs_fst(CompSpec::Id), cs_const(5)),
            cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))),
            enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
    }
}

pub proof fn eq_refl_structure(enc: nat)
    requires eval_comp(check_axiom_eq_refl(), enc) != 0,
    ensures unpair1(enc) == 0, unpair1(unpair2(enc)) == unpair2(unpair2(enc)),
{
    hide(eval_comp);
    assert(unpair1(enc) == 0 && unpair1(unpair2(enc)) == unpair2(unpair2(enc))) by {
        reveal(eval_comp);
        lemma_eval_cs_and(
            cs_eq(cs_fst(CompSpec::Id), cs_const(0)),
            cs_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id))),
            enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(0), enc);
        lemma_eval_eq(cs_fst(cs_snd(CompSpec::Id)), cs_snd(cs_snd(CompSpec::Id)), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
    }
}

pub proof fn iff_elim_left_structure(enc: nat)
    requires eval_comp(check_axiom_iff_elim_left(), enc) != 0,
    ensures
        unpair1(enc) == 5,
        unpair1(unpair1(unpair2(enc))) == 6,
        unpair1(unpair2(unpair2(enc))) == 5,
        unpair2(unpair1(unpair2(enc))) == unpair2(unpair2(unpair2(enc))),
{
    hide(eval_comp);
    let outer_content = cs_snd(CompSpec::Id);
    let iff_part = cs_fst(outer_content);
    let impl_part = cs_snd(outer_content);
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(iff_part), cs_const(6));
    let c3 = cs_eq(cs_fst(impl_part), cs_const(5));
    let c4 = cs_eq(cs_snd(iff_part), cs_snd(impl_part));
    assert(unpair1(enc) == 5
        && unpair1(unpair1(unpair2(enc))) == 6
        && unpair1(unpair2(unpair2(enc))) == 5
        && unpair2(unpair1(unpair2(enc))) == unpair2(unpair2(unpair2(enc)))) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c3, c4, enc);
        lemma_eval_cs_and(c2, cs_and(c3, c4), enc);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c4)), enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(iff_part), cs_const(6), enc);
        lemma_eval_eq(cs_fst(impl_part), cs_const(5), enc);
        lemma_eval_eq(cs_snd(iff_part), cs_snd(impl_part), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(CompSpec::Id), enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
        lemma_eval_fst(iff_part, enc);
        lemma_eval_snd(iff_part, enc);
        lemma_eval_fst(impl_part, enc);
        lemma_eval_snd(impl_part, enc);
    }
}

pub proof fn iff_intro_structure(enc: nat)
    requires eval_comp(check_axiom_iff_intro(), enc) != 0,
    ensures
        unpair1(enc) == 5,
        unpair1(unpair1(unpair2(enc))) == 5,
        unpair1(unpair2(unpair2(enc))) == 5,
        ({
            let l_enc = unpair1(unpair2(enc));
            let r_enc = unpair2(unpair2(enc));
            let phi_v = unpair1(unpair2(l_enc));
            let psi_v = unpair2(unpair2(l_enc));
            unpair1(unpair2(r_enc)) == pair(5nat, pair(psi_v, phi_v))
            && unpair2(unpair2(r_enc)) == pair(6nat, unpair2(l_enc))
        }),
{
    hide(eval_comp);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    let phi_cs = cs_fst(cs_snd(l));
    let psi_cs = cs_snd(cs_snd(l));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(l), cs_const(5));
    let c3 = cs_eq(cs_fst(r), cs_const(5));
    let c4 = cs_eq(cs_fst(cs_snd(r)),
        CompSpec::CantorPair { left: Box::new(cs_const(5)),
            right: Box::new(CompSpec::CantorPair { left: Box::new(psi_cs), right: Box::new(phi_cs) }) });
    let c5 = cs_eq(cs_snd(cs_snd(r)),
        CompSpec::CantorPair { left: Box::new(cs_const(6)), right: Box::new(cs_snd(l)) });
    assert(unpair1(enc) == 5
        && unpair1(unpair1(unpair2(enc))) == 5
        && unpair1(unpair2(unpair2(enc))) == 5
        && ({
            let l_enc = unpair1(unpair2(enc));
            let r_enc = unpair2(unpair2(enc));
            let phi_v = unpair1(unpair2(l_enc));
            let psi_v = unpair2(unpair2(l_enc));
            unpair1(unpair2(r_enc)) == pair(5nat, pair(psi_v, phi_v))
            && unpair2(unpair2(r_enc)) == pair(6nat, unpair2(l_enc))
        })) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c4, c5, enc);
        lemma_eval_cs_and(c3, cs_and(c4, c5), enc);
        lemma_eval_cs_and(c2, cs_and(c3, cs_and(c4, c5)), enc);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, cs_and(c4, c5))), enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(l), cs_const(5), enc);
        lemma_eval_eq(cs_fst(r), cs_const(5), enc);
        lemma_eval_eq(cs_fst(cs_snd(r)), CompSpec::CantorPair { left: Box::new(cs_const(5)),
            right: Box::new(CompSpec::CantorPair { left: Box::new(psi_cs), right: Box::new(phi_cs) }) }, enc);
        lemma_eval_eq(cs_snd(cs_snd(r)), CompSpec::CantorPair { left: Box::new(cs_const(6)),
            right: Box::new(cs_snd(l)) }, enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(content, enc);
        lemma_eval_snd(content, enc);
        lemma_eval_fst(l, enc);
        lemma_eval_snd(l, enc);
        lemma_eval_fst(cs_snd(l), enc);
        lemma_eval_snd(cs_snd(l), enc);
        lemma_eval_fst(r, enc);
        lemma_eval_snd(r, enc);
        lemma_eval_fst(cs_snd(r), enc);
        lemma_eval_snd(cs_snd(r), enc);
        lemma_eval_pair(psi_cs, phi_cs, enc);
        lemma_eval_pair(cs_const(5), CompSpec::CantorPair { left: Box::new(psi_cs), right: Box::new(phi_cs) }, enc);
        lemma_eval_pair(cs_const(6), cs_snd(l), enc);
    }
}

} //  verus!
