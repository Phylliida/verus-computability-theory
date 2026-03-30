use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::zfc::*;

verus! {

///  Extensionality axiom encoding evaluates correctly.
///  Proved by compute_only — both sides are constant expressions.
pub proof fn lemma_enc_extensionality_eval(x: nat)
    ensures eval_comp(enc_extensionality(), x) == encode(extensionality_axiom()),
{ assert(eval_comp(enc_extensionality(), x) == encode(extensionality_axiom())) by(compute_only); }

//  TODO: remaining axiom eval lemmas need either:
//  1. by(compute_only) with longer timeout, OR
//  2. Manual bottom-up evaluation with lemma_eval_pair/cs_const helpers
//  The extensionality case proves the pattern works.

} //  verus!
