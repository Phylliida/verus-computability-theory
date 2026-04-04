use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_decode::*;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;
use crate::compspec_subst_step_helpers::lemma_subst_step_dispatch;
use crate::compspec_subst_forward_extract::extract_general;
use crate::compspec_subst_forward_term_eval::lemma_subst_one_term_eval_general;
use crate::compspec_subst_forward_helpers::lemma_subst_valid_zero_stable;

verus! {

///  Evaluate the Eq (tag 0) step at iterate level with general (te, ts).
///  Shows: step result has specific valid product and state.
///  Combined dispatch + term eval + valid structure in one file.
///  Isolated per rlimit tips.
#[verifier::rlimit(2000)]
pub proof fn lemma_forward_eq_step_iter(
    phi_enc: nat, result_enc: nat, var: nat,
    rest: nat, te: nat, ts: nat,
    pe: nat, re: nat, fuel: nat,
)
    requires
        unpair1(phi_enc) == 0nat,
        unpair1(result_enc) == 0nat,
        fuel >= 1,
        //  Iterate from entry state gives valid != 0
        unpair1(unpair2(
            compspec_iterate(check_subst_step(), fuel,
                pair(pair(pair(phi_enc, result_enc) + 1, rest),
                     pair(1nat, pair(te, ts))),
                pair(pe, pair(re, var)))
        )) != 0,
    ensures ({
        let a = unpair1(unpair2(phi_enc));
        let b = unpair2(unpair2(phi_enc));
        let ra = unpair1(unpair2(result_enc));
        let rb = unpair2(unpair2(result_enc));
        //  Constraints from the per-term checks:
        &&& (a != var ==> ra == a)
        &&& (b != var ==> rb == b)
        //  te consistency (when ts != 0, var positions must match te):
        &&& (a == var && ts != 0 ==> ra == te)
        //  After first term: te1 and ts1
        &&& ({
            let te1: nat = if a == var { if ts == 0 { ra } else { te } } else { te };
            let ts1: nat = if a == var { 1nat } else { ts };
            (b == var && ts1 != 0 ==> rb == te1)
        })
    }),
{
    hide(eval_comp);
    let entry = pair(phi_enc, result_enc);
    let acc = pair(pair(entry + 1, rest), pair(1nat, pair(te, ts)));
    let input = pair(pe, pair(re, var));
    let si = pair((fuel - 1) as nat, pair(acc, input));

    let a = unpair1(unpair2(phi_enc));
    let b = unpair2(unpair2(phi_enc));
    let ra = unpair1(unpair2(result_enc));
    let rb = unpair2(unpair2(result_enc));

    //  Phase 1: Dispatch step → process_pair → atomic_terms
    assert(eval_comp(check_subst_step(), si)
        == eval_comp(check_subst_atomic_terms(), si)) by {
        reveal(eval_comp);
        lemma_subst_step_dispatch((fuel - 1) as nat, entry + 1, rest, 1nat, te, ts,
            pe, re, var);
        //  process_pair dispatch: tag 0 → IfZero(0=0) → then → atomic_terms
        extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
            pe, re, var);
        let phi_tag_cs = cs_fst(csa_phi_node());
        lemma_eval_ifzero_then(phi_tag_cs,
            check_subst_atomic_terms(),
            CompSpec::IfZero {
                cond: Box::new(cs_comp(CompSpec::Pred, phi_tag_cs)),
                then_br: Box::new(check_subst_atomic_terms()),
                else_br: Box::new(CompSpec::IfZero {
                    cond: Box::new(cs_comp(CompSpec::Pred, cs_comp(CompSpec::Pred, phi_tag_cs))),
                    then_br: Box::new(check_subst_unary()),
                    else_br: Box::new(check_subst_compound()),
                }),
            }, si);
    }

    //  Phase 2: Extract csa_* values
    extract_general((fuel - 1) as nat, phi_enc, result_enc, rest, 1nat, te, ts,
        pe, re, var);
    lemma_pair_surjective(phi_enc);
    lemma_pair_surjective(unpair2(phi_enc));
    lemma_pair_surjective(result_enc);
    lemma_pair_surjective(unpair2(result_enc));

    //  Phase 3: Per-term evaluations
    let v1: nat = if a == var {
        if ts == 0 { 1nat } else { if ra == te { 1nat } else { 0nat } }
    } else { if a == ra { 1nat } else { 0nat } };
    let te1: nat = if a == var { if ts == 0 { ra } else { te } } else { te };
    let ts1: nat = if a == var { 1nat } else { ts };

    assert(eval_comp(cs_fst(csa_term1()), si) == v1) by {
        reveal(eval_comp);
        lemma_subst_one_term_eval_general(
            cs_fst(cs_snd(csa_phi_node())),
            cs_fst(cs_snd(csa_result_node())),
            csa_var(), csa_t_enc(), csa_t_set(),
            si, a, ra, var, te, ts);
    }

    let v2: nat = if b == var {
        if ts1 == 0 { 1nat } else { if rb == te1 { 1nat } else { 0nat } }
    } else { if b == rb { 1nat } else { 0nat } };

    assert(eval_comp(cs_fst(csa_term2()), si) == v2) by {
        reveal(eval_comp);
        lemma_subst_one_term_eval_general(
            cs_snd(cs_snd(csa_phi_node())),
            cs_snd(cs_snd(csa_result_node())),
            csa_var(),
            cs_fst(cs_snd(csa_term1())),
            cs_snd(cs_snd(csa_term1())),
            si, b, rb, var, te1, ts1);
    }

    //  Phase 4: Valid product = tag_eq * v1 * v2 and step output
    //  tag_eq = cs_eq(0, 0) = 1 (tags both 0)
    let valid_product = 1nat * (v1 * v2);
    assert(valid_product != 0nat) by {
        reveal(eval_comp);
        //  Evaluate the tag_eq
        lemma_eval_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node()), si);
        //  Evaluate valid = cs_and(tag_eq, cs_and(v1, v2))
        lemma_eval_cs_and(cs_fst(csa_term1()), cs_fst(csa_term2()), si);
        lemma_eval_cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
            cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())), si);
        //  Evaluate pair structure of atomic_terms output
        let valid_cs = cs_and(cs_eq(cs_fst(csa_phi_node()), cs_fst(csa_result_node())),
            cs_and(cs_fst(csa_term1()), cs_fst(csa_term2())));
        lemma_eval_pair(valid_cs, cs_snd(csa_term2()), si);
        lemma_eval_pair(csa_rest(), cs_pair(valid_cs, cs_snd(csa_term2())), si);
        //  step result
        let step_result = eval_comp(check_subst_step(), si);
        let state = eval_comp(cs_snd(csa_term2()), si);
        //  Connect iterate to step: if step valid = 0, remaining gives valid = 0
        lemma_compspec_iterate_unfold(check_subst_step(), fuel, acc, input);
        if valid_product == 0nat {
            //  step result has valid = 0 → remaining iterate preserves → final = 0
            lemma_pair_surjective(state);
            lemma_subst_valid_zero_stable((fuel - 1) as nat, rest,
                unpair1(state), unpair2(state), pe, re, var);
            lemma_unpair2_pair(rest, pair(0nat, state));
            lemma_unpair1_pair(0nat, state);
            //  contradiction with precondition
        }
    }

    //  Phase 5: Extract constraints from v1 != 0 and v2 != 0
    assert(v1 != 0nat && v2 != 0nat) by {
        if v1 == 0nat || v2 == 0nat {
            assert(v1 * v2 == 0nat) by (nonlinear_arith);
            assert(1nat * (v1 * v2) == 0nat) by (nonlinear_arith);
        }
    }

    //  From v1 != 0:
    //  If a != var: cs_eq(a, ra) != 0 → ra == a
    //  If a == var && ts != 0: cs_eq(te, ra) != 0 → ra == te
    //  From v2 != 0 (analogous with te1, ts1):
    //  If b != var: cs_eq(b, rb) != 0 → rb == b
    //  If b == var && ts1 != 0: cs_eq(te1, rb) != 0 → rb == te1
}

} // verus!
