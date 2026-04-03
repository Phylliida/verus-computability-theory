use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::compspec_subst_induction2::*;

verus! {

///  When valid == 0, the iterate preserves acc unchanged for ANY stack (not just empty).
///  Generalizes lemma_subst_empty_stable_general which only handles stack == 0.
pub proof fn lemma_subst_valid_zero_stable(
    fuel: nat, stack: nat, t_enc: nat, t_set: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    ensures ({
        let acc = pair(stack, pair(0nat, pair(t_enc, t_set)));
        let orig = pair(phi_enc, pair(result_enc, var));
        compspec_iterate(check_subst_step(), fuel, acc, orig) == acc
    }),
    decreases fuel,
{
    let acc = pair(stack, pair(0nat, pair(t_enc, t_set)));
    let orig = pair(phi_enc, pair(result_enc, var));
    if fuel > 0 {
        lemma_subst_step_valid_zero((fuel - 1) as nat, stack, t_enc, t_set,
            phi_enc, result_enc, var);
        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, orig);
        lemma_subst_valid_zero_stable((fuel - 1) as nat, stack, t_enc, t_set,
            phi_enc, result_enc, var);
    }
}

///  If subst_state starting from (te, 0) returns ts == 0, then state is completely unchanged.
///  (te only changes when ts changes, so if ts stayed 0, te stays at initial value.)
pub proof fn lemma_subst_state_unchanged(f: Formula, var: nat, t_enc: nat, te: nat)
    requires subst_state(f, var, t_enc, te, 0nat).1 == 0nat,
    ensures subst_state(f, var, t_enc, te, 0nat) == (te, 0nat),
    decreases f,
{
    match f {
        Formula::Eq { left, right } => {
            match left { Term::Var { index: a } => {
            match right { Term::Var { index: b } => {
                //  If a == var, subst_term_state returns (t_enc, 1) — ts becomes 1, contradiction
                //  So a != var, state stays (te, 0). Then b != var similarly.
            }}
            }}
        },
        Formula::In { left, right } => {
            match left { Term::Var { index: a } => {
            match right { Term::Var { index: b } => {
            }}
            }}
        },
        Formula::Not { sub } => {
            lemma_subst_state_unchanged(*sub, var, t_enc, te);
        },
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            let (te1, ts1) = subst_state(*left, var, t_enc, te, 0nat);
            if ts1 != 0nat {
                lemma_subst_state_ts_monotonic(*right, var, t_enc, te1, ts1);
            }
            //  ts1 == 0, so by IH on left: state unchanged → te1 == te
            lemma_subst_state_unchanged(*left, var, t_enc, te);
            //  Now (te1, ts1) == (te, 0), so right processes from (te, 0)
            lemma_subst_state_unchanged(*right, var, t_enc, te);
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
            if v == var {
                //  Returns (te, 0) unchanged
            } else {
                lemma_subst_state_unchanged(*sub, var, t_enc, te);
            }
        },
    }
}

///  If subst_state starting from (te, 0) returns ts_out == 0, then subst(f, var, t) == f.
///  (No term position in f's traversal matched var, so substitution is the identity.)
pub proof fn lemma_subst_state_zero_identity(f: Formula, var: nat, t_enc: nat, t: Term)
    requires subst_state(f, var, t_enc, 0nat, 0nat).1 == 0nat,
    ensures subst(f, var, t) == f,
    decreases f,
{
    match f {
        Formula::Eq { left, right } => {
            match left { Term::Var { index: a } => {
            match right { Term::Var { index: b } => {
                //  subst_state for Eq: process left term then right term
                //  subst_term_state(left, var, t_enc, 0, 0):
                //    if a == var → (t_enc, 1) — but ts_out would be 1, not 0
                //    else → (0, 0)
                //  Since final ts == 0, the first term didn't match var → a != var
                //  Then right processes with (0, 0):
                //    if b == var → ts_out = 1 — contradiction
                //    else → ts_out = 0
                //  So b != var too.
                //  subst_term(Var(a), var, t) = if a == var then t else Var(a) = Var(a)
                //  subst_term(Var(b), var, t) = Var(b)
                assert(a != var);
                assert(b != var);
            }}
            }}
        },
        Formula::In { left, right } => {
            match left { Term::Var { index: a } => {
            match right { Term::Var { index: b } => {
                assert(a != var);
                assert(b != var);
            }}
            }}
        },
        Formula::Not { sub } => {
            //  subst_state(Not(sub)) = subst_state(sub)
            lemma_subst_state_zero_identity(*sub, var, t_enc, t);
        },
        Formula::And { left, right } => {
            let (te1, ts1) = subst_state(*left, var, t_enc, 0nat, 0nat);
            if ts1 != 0nat {
                lemma_subst_state_ts_monotonic(*right, var, t_enc, te1, ts1);
            }
            //  ts1 == 0, and by unchanged lemma, te1 == 0
            lemma_subst_state_unchanged(*left, var, t_enc, 0nat);
            lemma_subst_state_zero_identity(*left, var, t_enc, t);
            lemma_subst_state_zero_identity(*right, var, t_enc, t);
        },
        Formula::Or { left, right } => {
            let (te1, ts1) = subst_state(*left, var, t_enc, 0nat, 0nat);
            if ts1 != 0nat {
                lemma_subst_state_ts_monotonic(*right, var, t_enc, te1, ts1);
            }
            lemma_subst_state_unchanged(*left, var, t_enc, 0nat);
            lemma_subst_state_zero_identity(*left, var, t_enc, t);
            lemma_subst_state_zero_identity(*right, var, t_enc, t);
        },
        Formula::Implies { left, right } => {
            let (te1, ts1) = subst_state(*left, var, t_enc, 0nat, 0nat);
            if ts1 != 0nat {
                lemma_subst_state_ts_monotonic(*right, var, t_enc, te1, ts1);
            }
            lemma_subst_state_unchanged(*left, var, t_enc, 0nat);
            lemma_subst_state_zero_identity(*left, var, t_enc, t);
            lemma_subst_state_zero_identity(*right, var, t_enc, t);
        },
        Formula::Iff { left, right } => {
            let (te1, ts1) = subst_state(*left, var, t_enc, 0nat, 0nat);
            if ts1 != 0nat {
                lemma_subst_state_ts_monotonic(*right, var, t_enc, te1, ts1);
            }
            lemma_subst_state_unchanged(*left, var, t_enc, 0nat);
            lemma_subst_state_zero_identity(*left, var, t_enc, t);
            lemma_subst_state_zero_identity(*right, var, t_enc, t);
        },
        Formula::Forall { var: v, sub } => {
            if v == var {
                //  subst(Forall(v, sub), var, t) = f when v == var
            } else {
                lemma_subst_state_zero_identity(*sub, var, t_enc, t);
            }
        },
        Formula::Exists { var: v, sub } => {
            if v == var {
                //  subst(Exists(v, sub), var, t) = f when v == var
            } else {
                lemma_subst_state_zero_identity(*sub, var, t_enc, t);
            }
        },
    }
}

///  ts monotonicity: if ts_in >= 1, ts_out >= 1 (ts never goes from 1 back to 0).
pub proof fn lemma_subst_state_ts_monotonic(f: Formula, var: nat, t_enc: nat, te: nat, ts: nat)
    requires ts != 0nat,
    ensures subst_state(f, var, t_enc, te, ts).1 != 0nat,
    decreases f,
{
    match f {
        Formula::Eq { left, right } => {
            //  subst_term_state with ts != 0: returns (te, ts) unchanged or same ts
        },
        Formula::In { left, right } => {},
        Formula::Not { sub } => {
            lemma_subst_state_ts_monotonic(*sub, var, t_enc, te, ts);
        },
        Formula::And { left, right } | Formula::Or { left, right }
        | Formula::Implies { left, right } | Formula::Iff { left, right } => {
            let (te1, ts1) = subst_state(*left, var, t_enc, te, ts);
            lemma_subst_state_ts_monotonic(*left, var, t_enc, te, ts);
            lemma_subst_state_ts_monotonic(*right, var, t_enc, te1, ts1);
        },
        Formula::Forall { var: v, sub } | Formula::Exists { var: v, sub } => {
            if v == var {
                //  returns (te, ts) unchanged
            } else {
                lemma_subst_state_ts_monotonic(*sub, var, t_enc, te, ts);
            }
        },
    }
}

} // verus!
