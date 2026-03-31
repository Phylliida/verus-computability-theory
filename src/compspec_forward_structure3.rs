use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_forward_structure2::*;

verus! {

//  Hyp syllogism structural extraction

pub proof fn hyp_syl_structure(enc: nat)
    requires eval_comp(check_axiom_hyp_syllogism(), enc) != 0,
    ensures
        unpair1(enc) == 5,
        unpair1(unpair1(unpair2(enc))) == 5,
        unpair1(unpair2(unpair2(enc))) == 5,
        unpair1(unpair1(unpair2(unpair2(unpair2(enc))))) == 5,
        unpair1(unpair2(unpair2(unpair2(unpair2(enc))))) == 5,
        unpair1(unpair2(unpair1(unpair2(unpair2(unpair2(enc)))))) == unpair2(unpair2(unpair1(unpair2(enc)))),
        unpair1(unpair2(unpair2(unpair2(unpair2(unpair2(enc)))))) == unpair1(unpair2(unpair1(unpair2(enc)))),
        unpair2(unpair2(unpair2(unpair2(unpair2(unpair2(enc)))))) == unpair2(unpair2(unpair1(unpair2(unpair2(unpair2(enc)))))),
{
    hide(eval_comp);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    let phi = cs_fst(cs_snd(l));
    let psi = cs_snd(cs_snd(l));
    let m = cs_fst(cs_snd(r));
    let n = cs_snd(cs_snd(r));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(l), cs_const(5));
    let c3 = cs_eq(cs_fst(r), cs_const(5));
    let c4 = cs_eq(cs_fst(m), cs_const(5));
    let c5 = cs_eq(cs_fst(n), cs_const(5));
    let c6 = cs_eq(cs_fst(cs_snd(m)), psi);
    let c7 = cs_eq(cs_fst(cs_snd(n)), phi);
    let c8 = cs_eq(cs_snd(cs_snd(n)), cs_snd(cs_snd(m)));
    let rest7 = c8;
    let rest6 = cs_and(c7, rest7);
    let rest5 = cs_and(c6, rest6);
    let rest4 = cs_and(c5, rest5);
    let rest3 = cs_and(c4, rest4);
    let rest2 = cs_and(c3, rest3);
    let rest1 = cs_and(c2, rest2);

    //  Tags: outer, L, R
    assert(unpair1(enc) == 5 && unpair1(unpair1(unpair2(enc))) == 5
        && unpair1(unpair2(unpair2(enc))) == 5) by {
        reveal(eval_comp);
        lemma_cs_and_nonzero_left(c1, rest1, enc);
        lemma_cs_and_nonzero_right(c1, rest1, enc);
        lemma_cs_and_nonzero_left(c2, rest2, enc);
        lemma_cs_and_nonzero_right(c2, rest2, enc);
        lemma_cs_and_nonzero_left(c3, rest3, enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(l), cs_const(5), enc);
        lemma_eval_eq(cs_fst(r), cs_const(5), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(content, enc);
        lemma_eval_snd(content, enc);
        lemma_eval_fst(l, enc);
        lemma_eval_fst(r, enc);
    }

    //  Tags: M, N
    assert(unpair1(unpair1(unpair2(unpair2(unpair2(enc))))) == 5
        && unpair1(unpair2(unpair2(unpair2(unpair2(enc))))) == 5) by {
        reveal(eval_comp);
        lemma_cs_and_nonzero_right(c1, rest1, enc);
        lemma_cs_and_nonzero_right(c2, rest2, enc);
        lemma_cs_and_nonzero_right(c3, rest3, enc);
        lemma_cs_and_nonzero_left(c4, rest4, enc);
        lemma_cs_and_nonzero_right(c4, rest4, enc);
        lemma_cs_and_nonzero_left(c5, rest5, enc);
        lemma_eval_eq(cs_fst(m), cs_const(5), enc);
        lemma_eval_eq(cs_fst(n), cs_const(5), enc);
        lemma_eval_fst(m, enc);
        lemma_eval_fst(n, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_snd(content, enc);
        lemma_eval_snd(r, enc);
        lemma_eval_fst(cs_snd(r), enc);
        lemma_eval_snd(cs_snd(r), enc);
    }

    //  Navigate deeper for content equalities
    assert(eval_comp(cs_snd(l), enc) == unpair2(unpair1(unpair2(enc)))
        && eval_comp(cs_snd(m), enc) == unpair2(unpair1(unpair2(unpair2(unpair2(enc)))))
        && eval_comp(cs_snd(n), enc) == unpair2(unpair2(unpair2(unpair2(unpair2(enc)))))) by {
        reveal(eval_comp);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(content, enc);
        lemma_eval_snd(content, enc);
        lemma_eval_snd(l, enc);
        lemma_eval_snd(r, enc);
        lemma_eval_fst(cs_snd(r), enc);
        lemma_eval_snd(cs_snd(r), enc);
        lemma_eval_snd(m, enc);
        lemma_eval_snd(n, enc);
    }

    //  ψ == ψ'
    lemma_cs_and_nonzero_right(c1, rest1, enc);
    lemma_cs_and_nonzero_right(c2, rest2, enc);
    lemma_cs_and_nonzero_right(c3, rest3, enc);
    lemma_cs_and_nonzero_right(c4, rest4, enc);
    lemma_cs_and_nonzero_right(c5, rest5, enc);
    lemma_cs_and_nonzero_left(c6, rest6, enc);
    assert(unpair1(unpair2(unpair1(unpair2(unpair2(unpair2(enc)))))) == unpair2(unpair2(unpair1(unpair2(enc))))) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(cs_snd(m)), psi, enc);
        lemma_eval_fst(cs_snd(m), enc);
        lemma_eval_snd(cs_snd(l), enc);
    }

    //  φ == φ'
    lemma_cs_and_nonzero_right(c6, rest6, enc);
    lemma_cs_and_nonzero_left(c7, rest7, enc);
    assert(unpair1(unpair2(unpair2(unpair2(unpair2(unpair2(enc)))))) == unpair1(unpair2(unpair1(unpair2(enc))))) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(cs_snd(n)), phi, enc);
        lemma_eval_fst(cs_snd(n), enc);
        lemma_eval_fst(cs_snd(l), enc);
    }

    //  χ == χ'
    lemma_cs_and_nonzero_right(c7, rest7, enc);
    assert(unpair2(unpair2(unpair2(unpair2(unpair2(unpair2(enc)))))) == unpair2(unpair2(unpair1(unpair2(unpair2(unpair2(enc))))))) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_snd(cs_snd(n)), cs_snd(cs_snd(m)), enc);
        lemma_eval_snd(cs_snd(n), enc);
        lemma_eval_snd(cs_snd(m), enc);
    }
}

//  Quantifier dist structural extraction
//  Checker has CantorPair constructions for the content equalities

pub proof fn quant_dist_structure(enc: nat)
    requires eval_comp(check_axiom_quantifier_dist(), enc) != 0,
    ensures
        unpair1(enc) == 5,
        unpair1(unpair1(unpair2(enc))) == 7,
        ({
            let l_enc = unpair1(unpair2(enc));
            let v_val = unpair1(unpair2(l_enc));
            let body_enc = unpair2(unpair2(l_enc));
            let r_enc = unpair2(unpair2(enc));
            unpair1(body_enc) == 5
            && unpair1(r_enc) == 5
            && unpair1(unpair2(r_enc)) == pair(7nat, pair(v_val, unpair1(unpair2(body_enc))))
            && unpair2(unpair2(r_enc)) == pair(7nat, pair(v_val, unpair2(unpair2(body_enc))))
        }),
{
    hide(eval_comp);
    let content = cs_snd(CompSpec::Id);
    let l = cs_fst(content);
    let r = cs_snd(content);
    let v = cs_fst(cs_snd(l));
    let body = cs_snd(cs_snd(l));
    let phi = cs_fst(cs_snd(body));
    let psi = cs_snd(cs_snd(body));
    let c1 = cs_eq(cs_fst(CompSpec::Id), cs_const(5));
    let c2 = cs_eq(cs_fst(l), cs_const(7));
    let c3 = cs_eq(cs_fst(body), cs_const(5));
    let c4 = cs_eq(cs_fst(r), cs_const(5));
    let r_left_expected = CompSpec::CantorPair {
        left: Box::new(cs_const(7)),
        right: Box::new(CompSpec::CantorPair { left: Box::new(v), right: Box::new(phi) })
    };
    let r_right_expected = CompSpec::CantorPair {
        left: Box::new(cs_const(7)),
        right: Box::new(CompSpec::CantorPair { left: Box::new(v), right: Box::new(psi) })
    };
    let c5 = cs_eq(cs_fst(cs_snd(r)), r_left_expected);
    let c6 = cs_eq(cs_snd(cs_snd(r)), r_right_expected);
    let rest5 = c6;
    let rest4 = cs_and(c5, rest5);
    let rest3 = cs_and(c4, rest4);
    let rest2 = cs_and(c3, rest3);
    let rest1 = cs_and(c2, rest2);

    //  Tags: outer, L
    assert(unpair1(enc) == 5 && unpair1(unpair1(unpair2(enc))) == 7) by {
        reveal(eval_comp);
        lemma_cs_and_nonzero_left(c1, rest1, enc);
        lemma_cs_and_nonzero_right(c1, rest1, enc);
        lemma_cs_and_nonzero_left(c2, rest2, enc);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(5), enc);
        lemma_eval_eq(cs_fst(l), cs_const(7), enc);
        lemma_eval_fst(CompSpec::Id, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(content, enc);
        lemma_eval_fst(l, enc);
    }

    //  Tags: body, R + content equalities
    assert(({
        let l_enc = unpair1(unpair2(enc));
        let v_val = unpair1(unpair2(l_enc));
        let body_enc = unpair2(unpair2(l_enc));
        let r_enc = unpair2(unpair2(enc));
        unpair1(body_enc) == 5
        && unpair1(r_enc) == 5
        && unpair1(unpair2(r_enc)) == pair(7nat, pair(v_val, unpair1(unpair2(body_enc))))
        && unpair2(unpair2(r_enc)) == pair(7nat, pair(v_val, unpair2(unpair2(body_enc))))
    })) by {
        reveal(eval_comp);
        lemma_cs_and_nonzero_right(c1, rest1, enc);
        lemma_cs_and_nonzero_right(c2, rest2, enc);
        lemma_cs_and_nonzero_left(c3, rest3, enc);
        lemma_cs_and_nonzero_right(c3, rest3, enc);
        lemma_cs_and_nonzero_left(c4, rest4, enc);
        lemma_cs_and_nonzero_right(c4, rest4, enc);
        lemma_cs_and_nonzero_left(c5, rest5, enc);
        lemma_cs_and_nonzero_right(c5, rest5, enc);
        lemma_eval_eq(cs_fst(body), cs_const(5), enc);
        lemma_eval_eq(cs_fst(r), cs_const(5), enc);
        lemma_eval_eq(cs_fst(cs_snd(r)), r_left_expected, enc);
        lemma_eval_eq(cs_snd(cs_snd(r)), r_right_expected, enc);
        lemma_eval_snd(CompSpec::Id, enc);
        lemma_eval_fst(content, enc);
        lemma_eval_snd(content, enc);
        lemma_eval_snd(l, enc);
        lemma_eval_fst(cs_snd(l), enc);
        lemma_eval_snd(cs_snd(l), enc);
        lemma_eval_fst(body, enc);
        lemma_eval_fst(r, enc);
        lemma_eval_snd(r, enc);
        lemma_eval_fst(cs_snd(r), enc);
        lemma_eval_snd(cs_snd(r), enc);
        lemma_eval_fst(cs_snd(body), enc);
        lemma_eval_snd(cs_snd(body), enc);
        lemma_eval_pair(v, phi, enc);
        lemma_eval_pair(cs_const(7), CompSpec::CantorPair { left: Box::new(v), right: Box::new(phi) }, enc);
        lemma_eval_pair(v, psi, enc);
        lemma_eval_pair(cs_const(7), CompSpec::CantorPair { left: Box::new(v), right: Box::new(psi) }, enc);
    }
}

} //  verus!
