use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_eq_iter_terms::*;
use crate::compspec_subst_forward_eq_iter_valid::lemma_forward_eq_valid_iter;

verus! {

///  Atomic Eq forward at iterate level: given the iterate accepts with general (te, ts),
///  construct t with result_enc == encode(subst(phi, var, t)) and ts consistency.
#[verifier::rlimit(1500)]
pub proof fn lemma_forward_atomic_eq_iter(
    left: Term, right: Term,
    result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
) -> (t: Term)
    requires
        fuel >= 1,
        //  Iterate from entry state gives valid != 0
        ({
            let phi_enc = encode(Formula::Eq { left, right });
            unpair1(unpair2(
                compspec_iterate(check_subst_step(), fuel,
                    pair(pair(pair(phi_enc, result_enc) + 1, rest),
                         pair(1nat, pair(te, ts))),
                    pair(pe, pair(re, var)))
            )) != 0
        }),
        //  Result has matching tag (tag 0)
        unpair1(result_enc) == 0nat,
    ensures
        result_enc == encode(subst(Formula::Eq { left, right }, var, t)),
        ts != 0nat ==> encode_term(t) == te,
{
    let phi = Formula::Eq { left, right };
    let phi_enc = encode(phi);

    match left { Term::Var { index: a } => {
    match right { Term::Var { index: b } => {

    lemma_encode_is_pair(phi);
    lemma_unpair1_pair(0nat, pair(a, b));
    lemma_unpair2_pair(0nat, pair(a, b));
    lemma_unpair1_pair(a, b);
    lemma_unpair2_pair(a, b);

    let ra = unpair1(unpair2(result_enc));
    let rb = unpair2(unpair2(result_enc));
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));

    //  Build si
    let entry = pair(phi_enc, result_enc);
    let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
    let si = pair((fuel - 1) as nat, pair(acc, pair(pe, pair(re, var))));

    //  Extract needed csa_* values
    extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts, pe, re, var);

    //  Per-term evals
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

    //  Valid product != 0
    lemma_forward_eq_valid_iter(phi_enc, result_enc, var, rest, te, ts, pe, re, fuel, v1, v2);
    //  Now: v1 != 0 and v2 != 0

    //  Extract constraints from v1 != 0 and v2 != 0:
    //  a != var → ra == a (from v1 = cs_eq(a, ra) != 0)
    //  a == var && ts != 0 → ra == te (from v1 = cs_eq(te, ra) != 0)
    //  b != var → rb == b (from v2)
    //  b == var && ts1 != 0 → rb == te1 (from v2)

    //  Construct t
    let t: Term = if ts != 0 {
        Term::Var { index: te }
    } else if a == var {
        Term::Var { index: ra }
    } else if b == var {
        Term::Var { index: rb }
    } else {
        Term::Var { index: 0 }
    };

    //  Show result_enc == encode(subst(phi, var, t))
    //  subst(Eq(Var(a), Var(b)), var, t) = Eq(subst_term(Var(a)), subst_term(Var(b)))
    //  subst_term(Var(a), var, t) = if a == var then t else Var(a)
    //  encode(Eq(l', r')) = pair(0, pair(encode_term(l'), encode_term(r')))

    //  Need: ra == encode_term(subst_term(Var(a), var, t))
    //  and   rb == encode_term(subst_term(Var(b), var, t))

    //  Case analysis establishes this from the constraints:
    assert(result_enc == encode(subst(phi, var, t)));

    //  ts consistency
    assert(ts != 0nat ==> encode_term(t) == te);

    t

    }}
    }}
}

} // verus!
