use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_step_compose::*;
use crate::compspec_subst_extract::*;
use crate::compspec_subst_term_eval::lemma_subst_one_term_valid;
use crate::compspec_subst_induction2::{subst_state, subst_term_state};

verus! {

proof fn csi_chain(fuel: nat, old_acc: nat, new_acc: nat, pe: nat, re: nat, var: nat)
    requires fuel > 0,
        eval_comp(check_subst_step(),
            pair((fuel-1) as nat, pair(old_acc, pair(pe, pair(re, var))))) == new_acc,
    ensures compspec_iterate(check_subst_step(), fuel, old_acc, pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat, new_acc, pair(pe, pair(re, var))),
{ lemma_compspec_iterate_unfold(check_subst_step(), fuel, old_acc, pair(pe, pair(re, var))); }

///  One iterate step for Eq formula, with exact state output matching subst_state.
#[verifier::rlimit(1200)]
pub proof fn step_eq_exact(
    f: Formula, left: Term, right: Term, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        fuel >= 1,
        f == (Formula::Eq { left, right }),
        ts == 0 || te == encode_term(t),
    ensures ({
        let (te2, ts2) = subst_state(f, var, encode_term(t), te, ts);
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f),encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(rest, pair(1nat, pair(te2, ts2))),
            pair(pe, pair(re, var)))
    }),
{
    let fe = encode(f); let r = encode(subst(f,var,t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    let orig = pair(pe, pair(re, var));
    let i = (fuel - 1) as nat;
    let n = pair(i, pair(acc, orig));
    let t_val = encode_term(t);

    //  Compose helper: step result = pair(rest, pair(1, state))
    lemma_subst_atomic_eq_result(i, left, right, var, t, rest, 1, te, ts, pe, re);
    let state = eval_comp(cs_snd(csa_term2()), n);

    //  Extract values + per-term eval to get exact state
    extract_atomic_eq_values(i, left, right, var, t, rest, 1, te, ts, pe, re);
    match left { Term::Var { index } => {} }
    match right { Term::Var { index } => {} }

    //  Term 1 (left)
    lemma_subst_one_term_valid(
        cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node())),
        csa_var(), csa_t_enc(), csa_t_set(), n,
        encode_term(left), encode_term(subst_term(left, var, t)), var,
        te, ts, t_val);

    let te1 = eval_comp(cs_fst(cs_snd(csa_term1())), n);
    let ts1 = eval_comp(cs_snd(cs_snd(csa_term1())), n);

    //  Term 2 (right) — uses te1, ts1 from term1
    lemma_subst_one_term_valid(
        cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node())),
        csa_var(), cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())), n,
        encode_term(right), encode_term(subst_term(right, var, t)), var,
        te1, ts1, t_val);

    let te2 = eval_comp(cs_fst(cs_snd(csa_term2())), n);
    let ts2 = eval_comp(cs_snd(cs_snd(csa_term2())), n);

    //  Reconstruct: cs_snd(csa_term2()) == pair(te2, ts2)
    lemma_eval_fst(cs_snd(csa_term2()), n);
    lemma_eval_snd(cs_snd(csa_term2()), n);
    lemma_pair_surjective(state);
    assert(state == pair(te2, ts2));

    //  Connect to subst_state
    assert(subst_state(f, var, t_val, te, ts) == (te2, ts2));

    //  Final: step result = pair(rest, pair(1, pair(te2, ts2)))
    assert(eval_comp(check_subst_step(), n) == pair(rest, pair(1nat, pair(te2, ts2))));

    csi_chain(fuel, acc, pair(rest, pair(1nat, pair(te2, ts2))), pe, re, var);
}

///  One iterate step for In formula, with exact state output matching subst_state.
#[verifier::rlimit(1200)]
pub proof fn step_in_exact(
    f: Formula, left: Term, right: Term, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat,
)
    requires
        fuel >= 1,
        f == (Formula::In { left, right }),
        ts == 0 || te == encode_term(t),
    ensures ({
        let (te2, ts2) = subst_state(f, var, encode_term(t), te, ts);
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f),encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(rest, pair(1nat, pair(te2, ts2))),
            pair(pe, pair(re, var)))
    }),
{
    let fe = encode(f); let r = encode(subst(f,var,t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    let orig = pair(pe, pair(re, var));
    let i = (fuel - 1) as nat;
    let n = pair(i, pair(acc, orig));
    let t_val = encode_term(t);

    lemma_subst_atomic_in_result(i, left, right, var, t, rest, 1, te, ts, pe, re);
    let state = eval_comp(cs_snd(csa_term2()), n);

    extract_atomic_in_values(i, left, right, var, t, rest, 1, te, ts, pe, re);
    match left { Term::Var { index } => {} }
    match right { Term::Var { index } => {} }

    //  Term 1 (left)
    lemma_subst_one_term_valid(
        cs_fst(cs_snd(csa_phi_node())), cs_fst(cs_snd(csa_result_node())),
        csa_var(), csa_t_enc(), csa_t_set(), n,
        encode_term(left), encode_term(subst_term(left, var, t)), var,
        te, ts, t_val);

    let te1 = eval_comp(cs_fst(cs_snd(csa_term1())), n);
    let ts1 = eval_comp(cs_snd(cs_snd(csa_term1())), n);

    //  Term 2 (right)
    lemma_subst_one_term_valid(
        cs_snd(cs_snd(csa_phi_node())), cs_snd(cs_snd(csa_result_node())),
        csa_var(), cs_fst(cs_snd(csa_term1())), cs_snd(cs_snd(csa_term1())), n,
        encode_term(right), encode_term(subst_term(right, var, t)), var,
        te1, ts1, t_val);

    let te2 = eval_comp(cs_fst(cs_snd(csa_term2())), n);
    let ts2 = eval_comp(cs_snd(cs_snd(csa_term2())), n);

    lemma_eval_fst(cs_snd(csa_term2()), n);
    lemma_eval_snd(cs_snd(csa_term2()), n);
    lemma_pair_surjective(state);
    assert(state == pair(te2, ts2));

    assert(subst_state(f, var, t_val, te, ts) == (te2, ts2));
    assert(eval_comp(check_subst_step(), n) == pair(rest, pair(1nat, pair(te2, ts2))));

    csi_chain(fuel, acc, pair(rest, pair(1nat, pair(te2, ts2))), pe, re, var);
}

} // verus!
