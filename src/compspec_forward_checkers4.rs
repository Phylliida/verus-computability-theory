use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::proof_system::*;
use crate::compspec_free_var_detection::lemma_has_free_var_comp_sound;

verus! {

//  ====================================================================
//  Forward proof: vacuous_quant checker → is_axiom_vacuous_quant
//  ====================================================================

//  Decode bridge for Implies
proof fn decode_implies(enc: nat)
    requires unpair1(enc) == 5,
    ensures decode_formula(enc) == mk_implies(
        decode_formula(unpair1(unpair2(enc))), decode_formula(unpair2(unpair2(enc)))),
{
    reveal(decode_formula);
    lemma_pair_surjective(enc);
}

//  Decode bridge for Forall
proof fn decode_forall(enc: nat)
    requires unpair1(enc) == 7,
    ensures decode_formula(enc) == mk_forall(
        unpair1(unpair2(enc)), decode_formula(unpair2(unpair2(enc)))),
{
    reveal(decode_formula);
    lemma_pair_surjective(enc);
}

//  Structure extraction: from checker nonzero, extract tag and structural facts.
proof fn vacuous_quant_structure(enc: nat)
    requires eval_comp(check_axiom_vacuous_quant(), enc) != 0,
    ensures
        unpair1(enc) == 5,                               //  outer Implies
        unpair1(unpair2(unpair2(enc))) == 7,             //  right = Forall
        unpair1(unpair2(enc)) == unpair2(unpair2(unpair2(unpair2(enc)))),  //  phi == body
        eval_comp(has_free_var_comp(),
            pair(unpair1(unpair2(enc)),
                 unpair1(unpair2(unpair2(unpair2(enc)))))) == 0,  //  var not free
{
    hide(eval_comp);

    let outer_content = cs_snd(CompSpec::Id);
    let phi = cs_fst(outer_content);
    let right = cs_snd(outer_content);
    let var = cs_fst(cs_snd(right));
    let body = cs_snd(cs_snd(right));

    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(right), cs_const(7));
    let c3 = cs_eq(phi, body);
    let c4 = cs_not(cs_comp(has_free_var_comp(), cs_pair(phi, var)));

    //  Extract each check from the cs_and chain
    assert(eval_comp(c1, enc) != 0 && eval_comp(cs_and(c2, cs_and(c3, c4)), enc) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c1, cs_and(c2, cs_and(c3, c4)), enc);
        assert(eval_comp(c1, enc) * eval_comp(cs_and(c2, cs_and(c3, c4)), enc) != 0);
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

    //  Extract tag values
    assert(unpair1(enc) == 5) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_fst(CompSpec::Id, enc);
    }

    assert(unpair1(unpair2(unpair2(enc))) == 7) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(right), cs_const(7), enc);
        lemma_eval_fst(cs_snd(outer_content), enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
    }

    //  phi == body
    assert(unpair1(unpair2(enc)) == unpair2(unpair2(unpair2(unpair2(enc))))) by {
        reveal(eval_comp);
        lemma_eval_eq(phi, body, enc);
        lemma_eval_fst(outer_content, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_snd(cs_snd(right), enc);
        lemma_eval_snd(outer_content, enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
    }

    //  has_free_var_comp == 0
    assert(eval_comp(has_free_var_comp(),
        pair(unpair1(unpair2(enc)), unpair1(unpair2(unpair2(unpair2(enc)))))) == 0) by {
        reveal(eval_comp);
        lemma_eval_cs_not(cs_comp(has_free_var_comp(), cs_pair(phi, var)), enc);
        lemma_eval_comp(has_free_var_comp(), cs_pair(phi, var), enc);
        lemma_eval_pair(phi, var, enc);
        lemma_eval_fst(outer_content, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(cs_snd(right), enc);
        lemma_eval_snd(outer_content, enc);
        lemma_eval_snd(cs_snd(CompSpec::Id), enc);
    }
}

//  Main forward proof
pub proof fn lemma_check_vacuous_quant_forward(enc: nat)
    requires eval_comp(check_axiom_vacuous_quant(), enc) != 0,
    ensures is_axiom_vacuous_quant(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);

    vacuous_quant_structure(enc);

    let phi_enc = unpair1(unpair2(enc));
    let right_enc = unpair2(unpair2(enc));
    let var = unpair1(unpair2(right_enc));
    let body_enc = unpair2(unpair2(right_enc));

    //  Decode the formula via bridges
    decode_implies(enc);
    decode_forall(right_enc);

    //  phi_enc == body_enc → same decoded formula
    assert(phi_enc == body_enc);
    let phi = decode_formula(phi_enc);

    //  has_free_var_comp says var not free in phi
    assert(!has_free_var(phi, var)) by {
        reveal(eval_comp);
        lemma_decode_encode_formula(phi);
        lemma_has_free_var_comp_sound(phi, var);
    }

    //  Conclude
    assert(is_axiom_vacuous_quant(decode_formula(enc))) by {
        assert(decode_formula(enc) == mk_implies(phi, mk_forall(var, phi)));
    }
}

} // verus!
