use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::compspec_halts::*;
use crate::compspec_decode::br_acc;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;

verus! {

///  Extract sub-expression eval values for a GENERAL entry (phi_node, result_node).
///  Unlike the backward extract which takes Formula + Term, this takes raw nats.
///  Isolated in own file to avoid sibling body pollution (per rlimit tips).
#[verifier::rlimit(500)]
pub proof fn extract_general(
    i: nat, phi_node: nat, result_node: nat, rest: nat,
    valid: nat, te: nat, ts: nat,
    phi_enc: nat, result_enc: nat, var: nat,
)
    ensures ({
        let entry = pair(phi_node, result_node);
        let acc = pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
        let orig = pair(phi_enc, pair(result_enc, var));
        let n = pair(i, pair(acc, orig));
        eval_comp(csa_entry(), n) == entry &&
        eval_comp(csa_phi_node(), n) == phi_node &&
        eval_comp(csa_result_node(), n) == result_node &&
        eval_comp(cs_fst(csa_phi_node()), n) == unpair1(phi_node) &&
        eval_comp(cs_fst(cs_snd(csa_phi_node())), n) == unpair1(unpair2(phi_node)) &&
        eval_comp(cs_snd(cs_snd(csa_phi_node())), n) == unpair2(unpair2(phi_node)) &&
        eval_comp(cs_fst(csa_result_node()), n) == unpair1(result_node) &&
        eval_comp(cs_fst(cs_snd(csa_result_node())), n) == unpair1(unpair2(result_node)) &&
        eval_comp(cs_snd(cs_snd(csa_result_node())), n) == unpair2(unpair2(result_node)) &&
        eval_comp(csa_var(), n) == var &&
        eval_comp(csa_t_enc(), n) == te &&
        eval_comp(csa_t_set(), n) == ts &&
        eval_comp(csa_rest(), n) == rest
    }),
{
    let entry = pair(phi_node, result_node);
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
    let orig = pair(phi_enc, pair(result_enc, var));
    let n = pair(i, pair(acc, orig));

    lemma_eval_br_acc(i, acc, orig);
    lemma_eval_fst(br_acc(), n);
    lemma_unpair1_pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
    lemma_eval_fst(cs_fst(br_acc()), n);
    lemma_unpair1_pair(entry + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), n);
    lemma_unpair2_pair(entry + 1, rest);
    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
    lemma_eval_pred(entry + 1);
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    lemma_eval_fst(entry_cs, n);
    lemma_unpair1_pair(phi_node, result_node);
    lemma_eval_snd(entry_cs, n);
    lemma_unpair2_pair(phi_node, result_node);
    let pn = cs_fst(entry_cs);
    let rn = cs_snd(entry_cs);
    lemma_eval_fst(pn, n);
    lemma_eval_snd(pn, n);
    lemma_pair_surjective(phi_node);
    lemma_eval_fst(cs_snd(pn), n);
    lemma_eval_snd(cs_snd(pn), n);
    lemma_pair_surjective(unpair2(phi_node));
    lemma_eval_fst(rn, n);
    lemma_eval_snd(rn, n);
    lemma_pair_surjective(result_node);
    lemma_eval_fst(cs_snd(rn), n);
    lemma_eval_snd(cs_snd(rn), n);
    lemma_pair_surjective(unpair2(result_node));
    lemma_eval_snd(CompSpec::Id, n);
    lemma_unpair2_pair(i, pair(acc, orig));
    lemma_eval_snd(cs_snd(CompSpec::Id), n);
    lemma_unpair2_pair(acc, orig);
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), n);
    lemma_unpair2_pair(phi_enc, pair(result_enc, var));
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), n);
    lemma_unpair2_pair(result_enc, var);
    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(pair(entry + 1, rest), pair(valid, pair(te, ts)));
    lemma_eval_snd(cs_snd(br_acc()), n);
    lemma_unpair2_pair(valid, pair(te, ts));
    lemma_eval_fst(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair1_pair(te, ts);
    lemma_eval_snd(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair2_pair(te, ts);
}

} // verus!
