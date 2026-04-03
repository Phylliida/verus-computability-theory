use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_forward_eq::lemma_forward_eq_constraints;
use crate::compspec_subst_forward_in::lemma_forward_in_constraints;
use crate::compspec_subst_forward_tag::*;

verus! {

///  Forward proof for atomic Eq: checker accepts → result == subst(phi, var, t).
///  Uses tag match + constraints + decode_formula roundtrip.
///  Isolated in own file for rlimit.
#[verifier::rlimit(800)]
pub proof fn lemma_forward_atomic_eq(
    phi: Formula, left: Term, right: Term,
    result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
) -> (t: Term)
    requires
        phi == (Formula::Eq { left, right }),
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        result == subst(phi, var, t),
{
    match left { Term::Var { index: a } => {
    match right { Term::Var { index: b } => {

    //  Tag match: result has tag 0
    lemma_encode_is_pair(phi);
    lemma_unpair1_pair(0nat, pair(a, b));
    lemma_forward_eq_tag_match(phi_enc, result_enc, var);

    //  Extract result terms via unpair
    let ra = unpair1(unpair2(result_enc));
    let rb = unpair2(unpair2(result_enc));

    //  result_enc == pair(0, pair(ra, rb)) via surjectivity
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));

    //  Constraints from the checker
    lemma_forward_eq_constraints(a, b, ra, rb, var, phi_enc, result_enc);

    //  Construct t
    let te = if a == var { ra } else { if b == var { rb } else { 0nat } };
    let t = Term::Var { index: te };

    //  Show result == subst(phi, var, t) via decode roundtrip
    //  result == decode_formula(result_enc) == decode_formula(pair(0, pair(ra, rb)))
    //  = Eq(Var(ra), Var(rb))
    //  subst(Eq(Var(a), Var(b)), var, Var(te))
    //  = Eq(if a==var then Var(te) else Var(a), if b==var then Var(te) else Var(b))
    //  From constraints: ra == (if a==var then te else a), rb == (if b==var then te else b)
    //  So they match.
    lemma_decode_encode_formula(result);
    reveal(decode_formula);
    //  Z3 should now see: result == decode(pair(0, pair(ra, rb))) == Eq(Var(ra), Var(rb))
    //  And subst(phi, var, t) == Eq(Var(if a==var then te else a), Var(if b==var then te else b))
    //  From constraints these are equal.
    t

    }}
    }}
}

///  Forward proof for atomic In: mirror of Eq with tag 1.
#[verifier::rlimit(800)]
pub proof fn lemma_forward_atomic_in(
    phi: Formula, left: Term, right: Term,
    result: Formula, var: nat,
    phi_enc: nat, result_enc: nat,
) -> (t: Term)
    requires
        phi == (Formula::In { left, right }),
        encode(phi) == phi_enc,
        encode(result) == result_enc,
        eval_comp(check_subst_comp(), pair(phi_enc, pair(result_enc, var))) != 0,
    ensures
        result == subst(phi, var, t),
{
    match left { Term::Var { index: a } => {
    match right { Term::Var { index: b } => {

    lemma_encode_is_pair(phi);
    lemma_unpair1_pair(1nat, pair(a, b));
    lemma_forward_in_tag_match(phi_enc, result_enc, var);

    let ra = unpair1(unpair2(result_enc));
    let rb = unpair2(unpair2(result_enc));
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));

    lemma_forward_in_constraints(a, b, ra, rb, var, phi_enc, result_enc);

    let te = if a == var { ra } else { if b == var { rb } else { 0nat } };
    let t = Term::Var { index: te };

    lemma_decode_encode_formula(result);
    reveal(decode_formula);
    t

    }}
    }}
}

} // verus!
