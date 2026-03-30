use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::zfc::*;

verus! {

///  Each enc_X() CompSpec evaluates to encode(X_axiom()).
///  Proved by `by(compute_only)` since both sides are constant expressions.

pub proof fn lemma_enc_extensionality_eval(x: nat)
    ensures eval_comp(enc_extensionality(), x) == encode(extensionality_axiom()),
{ assert(eval_comp(enc_extensionality(), x) == encode(extensionality_axiom())) by(compute_only); }

pub proof fn lemma_enc_pairing_eval(x: nat)
    ensures eval_comp(enc_pairing(), x) == encode(pairing_axiom()),
{ assert(eval_comp(enc_pairing(), x) == encode(pairing_axiom())) by(compute_only); }

pub proof fn lemma_enc_union_eval(x: nat)
    ensures eval_comp(enc_union(), x) == encode(union_axiom()),
{ assert(eval_comp(enc_union(), x) == encode(union_axiom())) by(compute_only); }

pub proof fn lemma_enc_powerset_eval(x: nat)
    ensures eval_comp(enc_powerset(), x) == encode(powerset_axiom()),
{ assert(eval_comp(enc_powerset(), x) == encode(powerset_axiom())) by(compute_only); }

pub proof fn lemma_enc_infinity_eval(x: nat)
    ensures eval_comp(enc_infinity(), x) == encode(infinity_axiom()),
{ assert(eval_comp(enc_infinity(), x) == encode(infinity_axiom())) by(compute_only); }

pub proof fn lemma_enc_foundation_eval(x: nat)
    ensures eval_comp(enc_foundation(), x) == encode(foundation_axiom()),
{ assert(eval_comp(enc_foundation(), x) == encode(foundation_axiom())) by(compute_only); }

pub proof fn lemma_enc_choice_eval(x: nat)
    ensures eval_comp(enc_choice(), x) == encode(choice_axiom()),
{ assert(eval_comp(enc_choice(), x) == encode(choice_axiom())) by(compute_only); }

///  For any fixed ZFC axiom (not replacement), check_zfc_axiom returns nonzero.
pub proof fn lemma_check_zfc_fixed_axiom(f: Formula)
    requires
        f == extensionality_axiom()
        || f == pairing_axiom()
        || f == union_axiom()
        || f == powerset_axiom()
        || f == infinity_axiom()
        || f == foundation_axiom()
        || f == choice_axiom(),
    ensures
        eval_comp(check_zfc_axiom(), encode(f)) != 0,
{
    let fe = encode(f);
    lemma_enc_extensionality_eval(fe);
    lemma_enc_pairing_eval(fe);
    lemma_enc_union_eval(fe);
    lemma_enc_powerset_eval(fe);
    lemma_enc_infinity_eval(fe);
    lemma_enc_foundation_eval(fe);
    lemma_enc_choice_eval(fe);
    //  For the matching axiom, cs_eq(Id, enc_X()) returns 1.
    //  cs_or chain: at least one 1 → sum >= 1 → nonzero.
}

} //  verus!
