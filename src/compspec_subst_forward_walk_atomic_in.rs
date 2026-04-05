use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_eq_iter_terms::*;
use crate::compspec_subst_forward_in_iter_valid::lemma_forward_in_valid_iter;

verus! {

///  Atomic In forward at iterate level (mirror of Eq, tag 1).
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_atomic_in_iter(
    left: Term, right: Term,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
) -> (t: Term)
    requires
        fuel >= 1,
        ({
            let phi_enc = encode(Formula::In { left, right });
            unpair1(unpair2(
                compspec_iterate(check_subst_step(), fuel,
                    pair(pair(pair(phi_enc, result_enc) + 1, rest),
                         pair(1nat, pair(te, ts))),
                    pair(pe, pair(re, var)))
            )) != 0
        }),
        unpair1(result_enc) == 1nat,
    ensures
        result_enc == encode(subst(Formula::In { left, right }, var, t)),
        ts != 0nat ==> encode_term(t) == te,
{
    let phi = Formula::In { left, right };
    let phi_enc = encode(phi);

    match left { Term::Var { index: a } => {
    match right { Term::Var { index: b } => {

    lemma_encode_is_pair(phi);
    lemma_unpair1_pair(1nat, pair(a, b));
    lemma_unpair2_pair(1nat, pair(a, b));
    lemma_unpair1_pair(a, b);
    lemma_unpair2_pair(a, b);

    let ra = unpair1(unpair2(result_enc));
    let rb = unpair2(unpair2(result_enc));
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));

    let entry = pair(phi_enc, result_enc);
    let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
    let si = pair((fuel - 1) as nat, pair(acc, pair(pe, pair(re, var))));

    extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts, pe, re, var);

    lemma_forward_term1_iter(si, a, ra, var, te, ts);
    let v1: nat = if a == var {
        if ts == 0 { 1nat } else { if ra == te { 1nat } else { 0nat } }
    } else { if a == ra { 1nat } else { 0nat } };
    let te1: nat = if a == var { if ts == 0 { ra } else { te } } else { te };
    let ts1: nat = if a == var { if ts == 0 { 1nat } else { ts } } else { ts };

    lemma_forward_term2_iter(si, b, rb, var, te1, ts1);
    let v2: nat = if b == var {
        if ts1 == 0 { 1nat } else { if rb == te1 { 1nat } else { 0nat } }
    } else { if b == rb { 1nat } else { 0nat } };

    lemma_forward_in_valid_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel, v1, v2);

    let t: Term = if ts != 0 {
        Term::Var { index: te }
    } else if a == var {
        Term::Var { index: ra }
    } else if b == var {
        Term::Var { index: rb }
    } else {
        Term::Var { index: 0 }
    };

    assert(result_enc == encode(subst(phi, var, t)));
    assert(ts != 0nat ==> encode_term(t) == te);
    t

    }}
    }}
}

} // verus!
