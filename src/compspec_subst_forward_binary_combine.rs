use vstd::prelude::*;
use crate::pairing::*;
use crate::formula::*;
use crate::compspec_subst_induction2::subst_state;
use crate::compspec_subst_forward_helpers::*;

verus! {

///  Binary t-consistency combine: given IH results for left and right,
///  derive the unified t for the binary formula.
///  No recursive calls — takes IH results as parameters.
pub proof fn lemma_binary_combine(
    phi: Formula, left: Formula, right: Formula, tag: nat,
    result_enc: nat, var: nat, te: nat, ts: nat,
    t_l: Term, t_r: Term,
    rl: nat, rr: nat,
    te_l: nat, ts_l: nat,
) -> (t: Term)
    requires
        tag >= 3, tag <= 6,
        encode(phi) == pair(tag, pair(encode(left), encode(right))),
        //  IH results
        rl == encode(subst(left, var, t_l)),
        ts != 0nat ==> encode_term(t_l) == te,
        rr == encode(subst(right, var, t_r)),
        ts_l != 0nat ==> encode_term(t_r) == te_l,
        //  State invariant from left processing
        ts_l == 0nat || te_l == encode_term(t_l),
        //  Subst structure for this binary variant (caller provides from match context)
        encode(subst(phi, var, t_l)) == pair(tag, pair(encode(subst(left, var, t_l)), encode(subst(right, var, t_l)))),
        encode(subst(phi, var, t_r)) == pair(tag, pair(encode(subst(left, var, t_r)), encode(subst(right, var, t_r)))),
        //  subst_state precondition (caller provides from binary step)
        ts_l == subst_state(left, var, encode_term(t_l), te, ts).1,
        //  Result structure (tags match)
        result_enc == pair(tag, pair(rl, rr)),
    ensures
        result_enc == encode(subst(phi, var, t)),
        ts != 0nat ==> encode_term(t) == te,
{
    if ts_l != 0nat {
        //  te_l == encode_term(t_l) (from invariant), encode_term(t_r) == te_l (from right IH)
        assert(encode_term(t_r) == encode_term(t_l));
        //  t_r and t_l are both Term::Var with the same index → subst gives same result
        match t_l { Term::Var { index: i_l } => {
        match t_r { Term::Var { index: i_r } => {
            assert(i_l == i_r);
            //  subst(right, var, t_r) == subst(right, var, t_l) since t_l == t_r
            assert(subst(right, var, t_r) == subst(right, var, t_l));
        }}
        }}
        //  result_enc = pair(tag, pair(rl, rr))
        //  = pair(tag, pair(encode(subst(left, var, t_l)), encode(subst(right, var, t_l))))
        //  = encode(subst(phi, var, t_l))
        assert(result_enc == encode(subst(phi, var, t_l)));
        t_l
    } else {
        //  If ts != 0: by ts_monotonic on left, ts_l != 0 → contradicts ts_l == 0
        //  So ts == 0 in this branch.
        if ts != 0nat {
            lemma_subst_state_ts_monotonic(left, var, encode_term(t_l), te, ts);
        }
        //  Now we know ts == 0
        assert(ts == 0nat);
        //  subst_state(left, var, encode_term(t_l), te, 0).1 == 0 (== ts_l)
        //  By generalized identity: subst(left, var, t) == left for any t
        lemma_subst_state_zero_identity_gen(left, var, encode_term(t_l), te, t_r);
        lemma_subst_state_zero_identity_gen(left, var, encode_term(t_l), te, t_l);
        //  rl = encode(subst(left, var, t_l)) = encode(left) = encode(subst(left, var, t_r))
        //  result_enc = pair(tag, pair(encode(left), rr))
        //  = pair(tag, pair(encode(subst(left, var, t_r)), encode(subst(right, var, t_r))))
        //  = encode(subst(phi, var, t_r))
        assert(result_enc == encode(subst(phi, var, t_r)));
        t_r
    }
}

} // verus!
