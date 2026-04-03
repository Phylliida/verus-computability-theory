use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_decode::br_acc;
use crate::compspec_free_var_helpers::lemma_eval_br_acc;

verus! {

///  Extract sub-expression eval values for atomic Eq step input.
pub proof fn extract_atomic_eq_values(
    i: nat, left: Term, right: Term, var: nat, t: Term,
    rest: nat, valid: nat, t_enc_val: nat, t_set_val: nat,
    phi_enc: nat, result_enc: nat,
)
    ensures ({
        let f = Formula::Eq { left, right };
        let entry = pair(encode(f), encode(subst(f, var, t)));
        let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
        let s = pair(phi_enc, pair(result_enc, var));
        let n = pair(i, pair(acc, s));
        let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
        let pn = cs_fst(entry_cs);
        let rn = cs_snd(entry_cs);
        let var_cs = cs_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))));
        let te_cs = cs_fst(cs_snd(cs_snd(br_acc())));
        let ts_cs = cs_snd(cs_snd(cs_snd(br_acc())));
        eval_comp(cs_fst(cs_snd(pn)), n) == encode_term(left) &&
        eval_comp(cs_snd(cs_snd(pn)), n) == encode_term(right) &&
        eval_comp(cs_fst(cs_snd(rn)), n) == encode_term(subst_term(left, var, t)) &&
        eval_comp(cs_snd(cs_snd(rn)), n) == encode_term(subst_term(right, var, t)) &&
        eval_comp(var_cs, n) == var &&
        eval_comp(te_cs, n) == t_enc_val &&
        eval_comp(ts_cs, n) == t_set_val &&
        eval_comp(cs_fst(pn), n) == 0nat &&
        eval_comp(cs_fst(rn), n) == 0nat &&
        eval_comp(cs_snd(cs_fst(br_acc())), n) == rest
    }),
{
    let f = Formula::Eq { left, right };
    let entry = pair(encode(f), encode(subst(f, var, t)));
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    let s = pair(phi_enc, pair(result_enc, var));
    let n = pair(i, pair(acc, s));

    lemma_encode_is_pair(f);
    lemma_encode_is_pair(subst(f, var, t));
    lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
    lemma_unpair1_pair(0nat, pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t))));

    lemma_eval_br_acc(i, acc, s);
    lemma_eval_fst(br_acc(), n);
    lemma_unpair1_pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    lemma_eval_fst(cs_fst(br_acc()), n);
    lemma_unpair1_pair(entry + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), n);
    lemma_unpair2_pair(entry + 1, rest);

    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
    lemma_eval_pred(entry + 1);
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    lemma_eval_fst(entry_cs, n);
    lemma_unpair1_pair(encode(f), encode(subst(f, var, t)));
    lemma_eval_snd(entry_cs, n);
    lemma_unpair2_pair(encode(f), encode(subst(f, var, t)));

    let pn = cs_fst(entry_cs);
    let rn = cs_snd(entry_cs);
    lemma_eval_fst(pn, n);
    lemma_eval_snd(pn, n);
    lemma_unpair2_pair(0nat, pair(encode_term(left), encode_term(right)));
    lemma_eval_fst(cs_snd(pn), n);
    lemma_unpair1_pair(encode_term(left), encode_term(right));
    lemma_eval_snd(cs_snd(pn), n);
    lemma_unpair2_pair(encode_term(left), encode_term(right));
    lemma_eval_fst(rn, n);
    lemma_eval_snd(rn, n);
    lemma_unpair2_pair(0nat, pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t))));
    lemma_eval_fst(cs_snd(rn), n);
    lemma_unpair1_pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t)));
    lemma_eval_snd(cs_snd(rn), n);
    lemma_unpair2_pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t)));

    lemma_eval_snd(CompSpec::Id, n);
    lemma_unpair2_pair(i, pair(acc, s));
    lemma_eval_snd(cs_snd(CompSpec::Id), n);
    lemma_unpair2_pair(acc, s);
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), n);
    lemma_unpair2_pair(phi_enc, pair(result_enc, var));
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), n);
    lemma_unpair2_pair(result_enc, var);

    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    lemma_eval_snd(cs_snd(br_acc()), n);
    lemma_unpair2_pair(valid, pair(t_enc_val, t_set_val));
    lemma_eval_fst(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair1_pair(t_enc_val, t_set_val);
    lemma_eval_snd(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair2_pair(t_enc_val, t_set_val);
}

///  Same as Eq but for In (tag 1).
pub proof fn extract_atomic_in_values(
    i: nat, left: Term, right: Term, var: nat, t: Term,
    rest: nat, valid: nat, t_enc_val: nat, t_set_val: nat,
    phi_enc: nat, result_enc: nat,
)
    ensures ({
        let f = Formula::In { left, right };
        let entry = pair(encode(f), encode(subst(f, var, t)));
        let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
        let s = pair(phi_enc, pair(result_enc, var));
        let n = pair(i, pair(acc, s));
        let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
        let pn = cs_fst(entry_cs);
        let rn = cs_snd(entry_cs);
        eval_comp(cs_fst(cs_snd(pn)), n) == encode_term(left) &&
        eval_comp(cs_snd(cs_snd(pn)), n) == encode_term(right) &&
        eval_comp(cs_fst(cs_snd(rn)), n) == encode_term(subst_term(left, var, t)) &&
        eval_comp(cs_snd(cs_snd(rn)), n) == encode_term(subst_term(right, var, t)) &&
        eval_comp(csa_var(), n) == var &&
        eval_comp(csa_t_enc(), n) == t_enc_val &&
        eval_comp(csa_t_set(), n) == t_set_val &&
        eval_comp(cs_fst(pn), n) == 1nat &&
        eval_comp(cs_fst(rn), n) == 1nat &&
        eval_comp(csa_rest(), n) == rest
    }),
{
    let f = Formula::In { left, right };
    let entry = pair(encode(f), encode(subst(f, var, t)));
    let acc = pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    let s = pair(phi_enc, pair(result_enc, var));
    let n = pair(i, pair(acc, s));

    lemma_encode_is_pair(f);
    lemma_encode_is_pair(subst(f, var, t));
    lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
    lemma_unpair1_pair(1nat, pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t))));

    lemma_eval_br_acc(i, acc, s);
    lemma_eval_fst(br_acc(), n);
    lemma_unpair1_pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    lemma_eval_fst(cs_fst(br_acc()), n);
    lemma_unpair1_pair(entry + 1, rest);
    lemma_eval_snd(cs_fst(br_acc()), n);
    lemma_unpair2_pair(entry + 1, rest);

    lemma_eval_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())), n);
    lemma_eval_pred(entry + 1);
    let entry_cs = cs_comp(CompSpec::Pred, cs_fst(cs_fst(br_acc())));
    lemma_eval_fst(entry_cs, n);
    lemma_unpair1_pair(encode(f), encode(subst(f, var, t)));
    lemma_eval_snd(entry_cs, n);
    lemma_unpair2_pair(encode(f), encode(subst(f, var, t)));

    let pn = cs_fst(entry_cs);
    let rn = cs_snd(entry_cs);
    lemma_eval_fst(pn, n);
    lemma_eval_snd(pn, n);
    lemma_unpair2_pair(1nat, pair(encode_term(left), encode_term(right)));
    lemma_eval_fst(cs_snd(pn), n);
    lemma_unpair1_pair(encode_term(left), encode_term(right));
    lemma_eval_snd(cs_snd(pn), n);
    lemma_unpair2_pair(encode_term(left), encode_term(right));
    lemma_eval_fst(rn, n);
    lemma_eval_snd(rn, n);
    lemma_unpair2_pair(1nat, pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t))));
    lemma_eval_fst(cs_snd(rn), n);
    lemma_unpair1_pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t)));
    lemma_eval_snd(cs_snd(rn), n);
    lemma_unpair2_pair(encode_term(subst_term(left, var, t)), encode_term(subst_term(right, var, t)));

    lemma_eval_snd(CompSpec::Id, n);
    lemma_unpair2_pair(i, pair(acc, s));
    lemma_eval_snd(cs_snd(CompSpec::Id), n);
    lemma_unpair2_pair(acc, s);
    lemma_eval_snd(cs_snd(cs_snd(CompSpec::Id)), n);
    lemma_unpair2_pair(phi_enc, pair(result_enc, var));
    lemma_eval_snd(cs_snd(cs_snd(cs_snd(CompSpec::Id))), n);
    lemma_unpair2_pair(result_enc, var);

    lemma_eval_snd(br_acc(), n);
    lemma_unpair2_pair(pair(entry + 1, rest), pair(valid, pair(t_enc_val, t_set_val)));
    lemma_eval_snd(cs_snd(br_acc()), n);
    lemma_unpair2_pair(valid, pair(t_enc_val, t_set_val));
    lemma_eval_fst(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair1_pair(t_enc_val, t_set_val);
    lemma_eval_snd(cs_snd(cs_snd(br_acc())), n);
    lemma_unpair2_pair(t_enc_val, t_set_val);
}

} // verus!
