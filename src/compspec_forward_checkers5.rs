use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::proof_system::*;
use crate::compspec_subst_forward::lemma_check_subst_comp_forward;

verus! {

//  ====================================================================
//  Forward proof: universal_inst checker → is_axiom_universal_inst
//  ====================================================================

proof fn decode_implies(enc: nat)
    requires unpair1(enc) == 5,
    ensures decode_formula(enc) == mk_implies(
        decode_formula(unpair1(unpair2(enc))), decode_formula(unpair2(unpair2(enc)))),
{
    reveal(decode_formula);
    lemma_pair_surjective(enc);
}

proof fn decode_forall(enc: nat)
    requires unpair1(enc) == 7,
    ensures decode_formula(enc) == mk_forall(
        unpair1(unpair2(enc)), decode_formula(unpair2(unpair2(enc)))),
{
    reveal(decode_formula);
    lemma_pair_surjective(enc);
}

//  Structure extraction
proof fn universal_inst_structure(enc: nat)
    requires eval_comp(check_axiom_universal_inst(), enc) != 0,
    ensures
        unpair1(enc) == 5,                                      //  outer Implies
        unpair1(unpair1(unpair2(enc))) == 7,                    //  left = Forall
        eval_comp(check_subst_comp(),                           //  substitution check passes
            pair(
                unpair2(unpair2(unpair1(unpair2(enc)))),         //  phi (body of Forall)
                pair(
                    unpair2(unpair2(enc)),                       //  result
                    unpair1(unpair2(unpair1(unpair2(enc))))      //  var
                )
            )) != 0,
{
    hide(eval_comp);

    let outer_content = cs_snd(CompSpec::Id);
    let left = cs_fst(outer_content);
    let result = cs_snd(outer_content);
    let var = cs_fst(cs_snd(left));
    let phi = cs_snd(cs_snd(left));

    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(left), cs_const(7));
    let c3 = cs_comp(check_subst_comp(), cs_pair(phi, cs_pair(result, var)));

    //  Extract c1 and c2 from cs_and chain
    assert(eval_comp(c1, enc) != 0 && eval_comp(cs_and(c2, c3), enc) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c1, cs_and(c2, c3), enc);
        if eval_comp(c1, enc) == 0 {
            assert(0nat * eval_comp(cs_and(c2, c3), enc) == 0) by (nonlinear_arith);
        }
        if eval_comp(cs_and(c2, c3), enc) == 0 {
            assert(eval_comp(c1, enc) * 0nat == 0) by (nonlinear_arith);
        }
    }
    assert(eval_comp(c2, enc) != 0 && eval_comp(c3, enc) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(c2, c3, enc);
        if eval_comp(c2, enc) == 0 {
            assert(0nat * eval_comp(c3, enc) == 0) by (nonlinear_arith);
        }
        if eval_comp(c3, enc) == 0 {
            assert(eval_comp(c2, enc) * 0nat == 0) by (nonlinear_arith);
        }
    }

    //  Outer tag
    assert(unpair1(enc) == 5) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_fst(CompSpec::Id, enc);
    }

    //  Left tag (Forall)
    assert(unpair1(unpair1(unpair2(enc))) == 7) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(left), cs_const(7), enc);
        lemma_eval_fst(cs_fst(outer_content), enc);
        lemma_eval_fst(outer_content, enc);
        lemma_eval_snd(CompSpec::Id, enc);
    }

    //  Subst comp
    assert(eval_comp(check_subst_comp(),
        pair(unpair2(unpair2(unpair1(unpair2(enc)))),
             pair(unpair2(unpair2(enc)),
                  unpair1(unpair2(unpair1(unpair2(enc))))))) != 0) by {
        reveal(eval_comp);
        lemma_eval_comp(check_subst_comp(), cs_pair(phi, cs_pair(result, var)), enc);
        lemma_eval_pair(phi, cs_pair(result, var), enc);
        lemma_eval_pair(result, var, enc);
        //  phi = snd(snd(left)) = snd(snd(fst(snd(Id))))
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(outer_content, enc);
        lemma_eval_snd(left, enc);
        lemma_eval_snd(cs_snd(left), enc);
        //  result = snd(snd(Id))
        lemma_eval_snd(outer_content, enc);
        //  var = fst(snd(left))
        lemma_eval_fst(cs_snd(left), enc);
    }
}

#[verifier::rlimit(3000)]
pub proof fn lemma_check_universal_inst_forward(enc: nat)
    requires
        eval_comp(check_axiom_universal_inst(), enc) != 0,
        exists|f: Formula| encode(f) == enc,
    ensures is_axiom_universal_inst(decode_formula(enc)),
{
    hide(eval_comp);
    hide(decode_formula);

    let outer_f: Formula = choose|f: Formula| encode(f) == enc;
    lemma_decode_encode_formula(outer_f);

    universal_inst_structure(enc);

    let left_enc = unpair1(unpair2(enc));
    let result_enc = unpair2(unpair2(enc));
    let var = unpair1(unpair2(left_enc));
    let phi_enc = unpair2(unpair2(left_enc));

    decode_implies(enc);
    decode_forall(left_enc);

    //  decode(enc) = Implies(Forall(var, decode(phi_enc)), decode(result_enc))
    let phi = decode_formula(phi_enc);
    let result = decode_formula(result_enc);

    //  From encode precondition: phi and result are valid formula encodings
    //  phi_enc = encode(actual_phi), result_enc = encode(actual_result)
    assert(exists|f: Formula| encode(f) == phi_enc) by {
        lemma_encode_is_pair(outer_f);
        match outer_f {
            Formula::Implies { left, right } => {
                lemma_unpair2_pair(5nat, pair(encode(*left), encode(*right)));
                lemma_unpair1_pair(encode(*left), encode(*right));
                match *left {
                    Formula::Forall { var: v, sub } => {
                        lemma_unpair2_pair(7nat, pair(v, encode(*sub)));
                        lemma_unpair2_pair(v, encode(*sub));
                        assert(phi_enc == encode(*sub));
                    },
                    _ => {
                        lemma_unpair1_pair(encode(*left), encode(*right));
                    },
                }
            },
            _ => {},
        }
    }
    assert(exists|f: Formula| encode(f) == result_enc) by {
        lemma_encode_is_pair(outer_f);
        match outer_f {
            Formula::Implies { left, right } => {
                lemma_unpair2_pair(5nat, pair(encode(*left), encode(*right)));
                lemma_unpair2_pair(encode(*left), encode(*right));
                assert(result_enc == encode(*right));
            },
            _ => {},
        }
    }

    lemma_encode_decode_formula(phi_enc);
    lemma_encode_decode_formula(result_enc);
    //  encode(phi) == phi_enc, encode(result) == result_enc

    //  Forward soundness: check_subst_comp accepts → result_enc == encode(subst(phi, var, t))
    let t = lemma_check_subst_comp_forward(phi, result_enc, var);

    //  decode(result_enc) == subst(phi, var, t) via encode injectivity
    lemma_decode_encode_formula(subst(phi, var, t));

    //  decode(enc) == Implies(Forall(var, phi), subst(phi, var, t))
    //  → is_axiom_universal_inst(decode(enc))
    assert(decode_formula(enc) == mk_implies(mk_forall(var, phi), subst(phi, var, t)));
}

} // verus!
