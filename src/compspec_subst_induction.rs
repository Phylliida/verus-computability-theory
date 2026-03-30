use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_step_helpers::*;

verus! {

proof fn csi_chain(fuel: nat, old_acc: nat, new_acc: nat, pe: nat, re: nat, var: nat)
    requires fuel > 0,
        eval_comp(check_subst_step(),
            pair((fuel-1) as nat, pair(old_acc, pair(pe, pair(re, var))))) == new_acc,
    ensures compspec_iterate(check_subst_step(), fuel, old_acc, pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat, new_acc, pair(pe, pair(re, var))),
{ lemma_compspec_iterate_unfold(check_subst_step(), fuel, old_acc, pair(pe, pair(re, var))); }

//  Non-recursive step helpers: show one step of the BoundedRec
//  for each formula constructor. Returns the new acc after processing the node.

proof fn step_eq(f: Formula, left: Term, right: Term, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, f == (Formula::Eq { left, right }),
    ensures
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var))),
{
    let fe = encode(f); let r = encode(subst(f,var,t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
    lemma_unpair1_pair(0nat, pair(encode_term(subst_term(left,var,t)), encode_term(subst_term(right,var,t))));
    lemma_subst_process_pair_atomic_eq((fuel-1) as nat, fe, r, rest, 1, te, ts, pe, re, var);
    csi_chain(fuel, acc, pair(rest, pair(1nat, pair(te,ts))), pe, re, var);
}

proof fn step_in(f: Formula, left: Term, right: Term, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, f == (Formula::In { left, right }),
    ensures
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var))),
{
    let fe = encode(f); let r = encode(subst(f,var,t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
    lemma_unpair1_pair(1nat, pair(encode_term(subst_term(left,var,t)), encode_term(subst_term(right,var,t))));
    lemma_subst_process_pair_atomic_in((fuel-1) as nat, fe, r, rest, 1, te, ts, pe, re, var);
    csi_chain(fuel, acc, pair(rest, pair(1nat, pair(te,ts))), pe, re, var);
}

proof fn step_not(f: Formula, sub: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, f == (Formula::Not { sub: Box::new(sub) }),
    ensures ({
        let sfe = encode(sub); let sre = encode(subst(sub,var,t));
        let target = pair(pair(pair(sfe,sre)+1, rest), pair(1nat, pair(te,ts)));
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat, target, pair(pe, pair(re, var))) }),
{
    let fe = encode(f); let r = encode(subst(f,var,t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_preserves_tag(f, var, t);
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    lemma_unpair1_pair(2nat, encode(sub));
    lemma_unpair1_pair(2nat, encode(subst(sub, var, t)));
    lemma_subst_process_pair_unary((fuel-1) as nat, fe, r, rest, 1, te, ts, pe, re, var);
    lemma_unpair2_pair(2nat, encode(sub));
    lemma_unpair2_pair(2nat, encode(subst(sub, var, t)));
    let sfe = encode(sub); let sre = encode(subst(sub, var, t));
    let na = pair(pair(pair(sfe,sre)+1, rest), pair(1nat, pair(te,ts)));
    csi_chain(fuel, acc, na, pe, re, var);
}

proof fn step_binary(f: Formula, left: Formula, right: Formula, tag: nat, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, tag >= 3, tag <= 6,
        encode(f) == pair(tag, pair(encode(left), encode(right))),
        encode(subst(f,var,t)) == pair(tag, pair(encode(subst(left,var,t)), encode(subst(right,var,t)))),
    ensures ({
        let lfe = encode(left); let rfe = encode(right);
        let lre = encode(subst(left,var,t)); let rre = encode(subst(right,var,t));
        let le = pair(lfe,lre); let ren = pair(rfe,rre);
        let target = pair(pair(le+1, pair(ren+1, rest)), pair(1nat, pair(te,ts)));
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f),encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat, target, pair(pe, pair(re, var))) }),
{
    let fe = encode(f);
    let r = encode(subst(f,var,t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    lemma_unpair1_pair(tag, pair(encode(left), encode(right)));
    lemma_unpair1_pair(tag, pair(encode(subst(left,var,t)), encode(subst(right,var,t))));
    lemma_subst_process_pair_binary((fuel-1) as nat, fe, r, rest, 1, te, ts, pe, re, var);
    lemma_unpair2_pair(tag, pair(encode(left), encode(right)));
    lemma_unpair2_pair(tag, pair(encode(subst(left,var,t)), encode(subst(right,var,t))));
    lemma_unpair1_pair(encode(left), encode(right));
    lemma_unpair2_pair(encode(left), encode(right));
    lemma_unpair1_pair(encode(subst(left,var,t)), encode(subst(right,var,t)));
    lemma_unpair2_pair(encode(subst(left,var,t)), encode(subst(right,var,t)));
    let lfe = encode(left); let rfe = encode(right);
    let lre = encode(subst(left,var,t)); let rre = encode(subst(right,var,t));
    let le = pair(lfe,lre); let ren = pair(rfe,rre);
    let na = pair(pair(le+1, pair(ren+1, rest)), pair(1nat, pair(te,ts)));
    csi_chain(fuel, acc, na, pe, re, var);
}

proof fn step_forall_bound(v: nat, sub: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, v == var,
    ensures ({ let f = Formula::Forall { var: v, sub: Box::new(sub) };
        let fe = encode(f); let r = encode(subst(f, var, t));
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var))) }),
{
    let f = Formula::Forall { var: v, sub: Box::new(sub) };
    let fe = encode(f); let r = encode(subst(f, var, t));
    //  v == var → subst returns f unchanged → r == fe
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    lemma_unpair1_pair(7nat, pair(v, encode(sub)));
    lemma_unpair2_pair(7nat, pair(v, encode(sub)));
    lemma_unpair1_pair(v, encode(sub));
    lemma_subst_process_pair_quantifier_bound((fuel-1) as nat, fe, rest,
        1, te, ts, pe, re, var);
    csi_chain(fuel, acc, pair(rest, pair(1nat, pair(te, ts))), pe, re, var);
}

proof fn quant_free_unpairs(tag: nat, v: nat, sub: Formula, var: nat, t: Term)
    requires tag >= 7, v != var,
    ensures
        unpair1(pair(tag, pair(v, encode(sub)))) == tag,
        unpair1(pair(tag, pair(v, encode(subst(sub,var,t))))) == tag,
        unpair1(unpair2(pair(tag, pair(v, encode(sub))))) == v,
        unpair1(unpair2(pair(tag, pair(v, encode(subst(sub,var,t)))))) == v,
        unpair2(unpair2(pair(tag, pair(v, encode(sub))))) == encode(sub),
        unpair2(unpair2(pair(tag, pair(v, encode(subst(sub,var,t)))))) == encode(subst(sub,var,t)),
{
    lemma_unpair1_pair(tag, pair(v, encode(sub)));
    lemma_unpair1_pair(tag, pair(v, encode(subst(sub,var,t))));
    lemma_unpair2_pair(tag, pair(v, encode(sub)));
    lemma_unpair2_pair(tag, pair(v, encode(subst(sub,var,t))));
    lemma_unpair1_pair(v, encode(sub));
    lemma_unpair1_pair(v, encode(subst(sub,var,t)));
    lemma_unpair2_pair(v, encode(sub));
    lemma_unpair2_pair(v, encode(subst(sub,var,t)));
}

proof fn step_forall_free(v: nat, sub: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, v != var,
    ensures ({ let f = Formula::Forall { var: v, sub: Box::new(sub) };
        let fe = encode(f); let r = encode(subst(f, var, t));
        let sfe = encode(sub); let sre = encode(subst(sub,var,t));
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(pair(pair(sfe,sre)+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var))) }),
{
    let f = Formula::Forall { var: v, sub: Box::new(sub) };
    let fe = encode(f); let r = encode(subst(f, var, t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_preserves_tag(f, var, t);
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    quant_free_unpairs(7, v, sub, var, t);
    lemma_subst_process_pair_quantifier((fuel-1) as nat, fe, r, rest, 1, te, ts, pe, re, var);
    let sfe = encode(sub); let sre = encode(subst(sub,var,t));
    let na = pair(pair(pair(sfe,sre)+1, rest), pair(1nat, pair(te,ts)));
    csi_chain(fuel, acc, na, pe, re, var);
}

proof fn step_exists_bound(v: nat, sub: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, v == var,
    ensures ({ let f = Formula::Exists { var: v, sub: Box::new(sub) };
        let fe = encode(f); let r = encode(subst(f, var, t));
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var))) }),
{
    let f = Formula::Exists { var: v, sub: Box::new(sub) };
    let fe = encode(f); let r = encode(subst(f, var, t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    lemma_unpair1_pair(8nat, pair(v, encode(sub)));
    lemma_unpair2_pair(8nat, pair(v, encode(sub)));
    lemma_unpair1_pair(v, encode(sub));
    lemma_subst_process_pair_quantifier_bound((fuel-1) as nat, fe, rest,
        1, te, ts, pe, re, var);
    csi_chain(fuel, acc, pair(rest, pair(1nat, pair(te, ts))), pe, re, var);
}

proof fn step_exists_free(v: nat, sub: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat)
    requires fuel >= 1, v != var,
    ensures ({ let f = Formula::Exists { var: v, sub: Box::new(sub) };
        let fe = encode(f); let r = encode(subst(f, var, t));
        let sfe = encode(sub); let sre = encode(subst(sub,var,t));
        compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel-1) as nat,
            pair(pair(pair(sfe,sre)+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var))) }),
{
    let f = Formula::Exists { var: v, sub: Box::new(sub) };
    let fe = encode(f); let r = encode(subst(f, var, t));
    let acc = pair(pair(pair(fe,r)+1, rest), pair(1nat, pair(te,ts)));
    lemma_subst_preserves_tag(f, var, t);
    lemma_subst_step_dispatch((fuel-1) as nat, pair(fe,r)+1, rest, 1, te, ts, pe, re, var);
    quant_free_unpairs(8, v, sub, var, t);
    lemma_subst_process_pair_quantifier((fuel-1) as nat, fe, r, rest, 1, te, ts, pe, re, var);
    let sfe = encode(sub); let sre = encode(subst(sub,var,t));
    let na = pair(pair(pair(sfe,sre)+1, rest), pair(1nat, pair(te,ts)));
    csi_chain(fuel, acc, na, pe, re, var);
}

///  Main structural induction.
#[verifier::rlimit(80)]
pub proof fn lemma_subst_traversal(
    f: Formula, var: nat, t: Term, rest: nat,
    te: nat, ts: nat, pe: nat, re: nat, fuel: nat,
)
    requires fuel >= formula_size(f),
    ensures compspec_iterate(check_subst_step(), fuel,
            pair(pair(pair(encode(f), encode(subst(f,var,t)))+1, rest), pair(1nat, pair(te,ts))),
            pair(pe, pair(re, var)))
        == compspec_iterate(check_subst_step(), (fuel - formula_size(f)) as nat,
            pair(rest, pair(1nat, pair(te,ts))), pair(pe, pair(re, var))),
    decreases f,
{
    assert(fuel > 0) by { lemma_formula_size_pos(f); }
    match f {
        Formula::Eq { left, right } => {
            step_eq(f, left, right, var, t, rest, te, ts, pe, re, fuel);
        },
        Formula::In { left, right } => {
            step_in(f, left, right, var, t, rest, te, ts, pe, re, fuel);
        },
        Formula::Not { sub } => {
            step_not(f, *sub, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
        },
        Formula::And { left, right } => {
            step_binary(f, *left, *right, 3, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Or { left, right } => {
            step_binary(f, *left, *right, 4, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Implies { left, right } => {
            step_binary(f, *left, *right, 5, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Iff { left, right } => {
            step_binary(f, *left, *right, 6, var, t, rest, te, ts, pe, re, fuel);
            lemma_subst_traversal(*left, var, t, pair(pair(encode(*right), encode(subst(*right,var,t)))+1, rest), te, ts, pe, re, (fuel-1) as nat);
            lemma_subst_traversal(*right, var, t, rest, te, ts, pe, re, (fuel-1-formula_size(*left)) as nat);
        },
        Formula::Forall { var: v, sub } => {
            if v == var {
                step_forall_bound(v, *sub, var, t, rest, te, ts, pe, re, fuel);
            } else {
                step_forall_free(v, *sub, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
            }
        },
        Formula::Exists { var: v, sub } => {
            if v == var {
                step_exists_bound(v, *sub, var, t, rest, te, ts, pe, re, fuel);
            } else {
                step_exists_free(v, *sub, var, t, rest, te, ts, pe, re, fuel);
                lemma_subst_traversal(*sub, var, t, rest, te, ts, pe, re, (fuel-1) as nat);
            }
        },
    }
}

} //  verus!
