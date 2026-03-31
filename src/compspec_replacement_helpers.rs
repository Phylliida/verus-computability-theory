use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::zfc::*;

verus! {

//  ====================================================================
//  Encoding helpers
//  ====================================================================

proof fn lemma_encode_forall(v: nat, sub: Formula)
    ensures encode(mk_forall(v, sub)) == pair(7nat, pair(v, encode(sub))),
{}

proof fn lemma_encode_exists(v: nat, sub: Formula)
    ensures encode(mk_exists(v, sub)) == pair(8nat, pair(v, encode(sub))),
{}

proof fn lemma_encode_implies(a: Formula, b: Formula)
    ensures encode(mk_implies(a, b)) == pair(5nat, pair(encode(a), encode(b))),
{}

proof fn lemma_encode_iff(a: Formula, b: Formula)
    ensures encode(mk_iff(a, b)) == pair(6nat, pair(encode(a), encode(b))),
{}

proof fn lemma_encode_and(a: Formula, b: Formula)
    ensures encode(mk_and(a, b)) == pair(3nat, pair(encode(a), encode(b))),
{}

proof fn lemma_encode_eq(a: Term, b: Term)
    ensures encode(mk_eq(a, b)) == pair(0nat, pair(encode_term(a), encode_term(b))),
{}

proof fn lemma_encode_in(a: Term, b: Term)
    ensures encode(mk_in(a, b)) == pair(1nat, pair(encode_term(a), encode_term(b))),
{}

//  ====================================================================
//  Tag + var + phi + subst checks
//  ====================================================================

#[verifier::rlimit(800)]
proof fn replacement_tags_vars_phi_subst(
    f: Formula, phi: Formula,
    x_var: nat, y_var: nat, z_var: nat, u_var: nat, v_var: nat,
)
    requires
        x_var != y_var, x_var != z_var, y_var != z_var,
        u_var != x_var, u_var != y_var, v_var != x_var, v_var != y_var, u_var != v_var,
        f == mk_forall(x_var, mk_implies(
            mk_forall(y_var, mk_forall(z_var, mk_implies(
                mk_and(phi, subst(phi, z_var, mk_var(y_var))),
                mk_eq(mk_var(y_var), mk_var(z_var))
            ))),
            mk_forall(u_var, mk_exists(v_var, mk_forall(y_var,
                mk_iff(
                    mk_in(mk_var(y_var), mk_var(v_var)),
                    mk_exists(x_var, mk_and(mk_in(mk_var(x_var), mk_var(u_var)), phi))
                )
            )))
        )),
    ensures ({
        let s = encode(f);
        let body = cs_snd(cs_snd(CompSpec::Id));
        let func = cs_fst(cs_snd(body));
        let range = cs_snd(cs_snd(body));
        let x = cs_fst(cs_snd(CompSpec::Id));
        let y = cs_fst(cs_snd(func));
        let func_inner = cs_snd(cs_snd(func));
        let z = cs_fst(cs_snd(func_inner));
        let func_implies = cs_snd(cs_snd(func_inner));
        let func_and = cs_fst(cs_snd(func_implies));
        let func_eq = cs_snd(cs_snd(func_implies));
        let phi_cs = cs_fst(cs_snd(func_and));
        let subst_phi_cs = cs_snd(cs_snd(func_and));
        let u = cs_fst(cs_snd(range));
        let range_exists = cs_snd(cs_snd(range));
        let v = cs_fst(cs_snd(range_exists));
        let range_forall_y = cs_snd(cs_snd(range_exists));
        let y_prime = cs_fst(cs_snd(range_forall_y));
        let range_iff = cs_snd(cs_snd(range_forall_y));
        let iff_left = cs_fst(cs_snd(range_iff));
        let iff_right = cs_snd(cs_snd(range_iff));
        let x_prime = cs_fst(cs_snd(iff_right));
        let range_and = cs_snd(cs_snd(iff_right));
        let phi_prime = cs_snd(cs_snd(range_and));

        //  Tag checks all evaluate to 1
        eval_comp(cs_eq(cs_fst(CompSpec::Id), cs_const(7)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(body), cs_const(5)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(func), cs_const(7)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(func_inner), cs_const(7)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(func_implies), cs_const(5)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(func_and), cs_const(3)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(func_eq), cs_const(0)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(range), cs_const(7)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(range_exists), cs_const(8)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(range_forall_y), cs_const(7)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(range_iff), cs_const(6)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(iff_left), cs_const(1)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(iff_right), cs_const(8)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(range_and), cs_const(3)), s) == 1 &&
        eval_comp(cs_eq(cs_fst(cs_fst(cs_snd(range_and))), cs_const(1)), s) == 1 &&
        //  Var checks all evaluate to 1
        eval_comp(cs_eq(y_prime, y), s) == 1 &&
        eval_comp(cs_eq(x_prime, x), s) == 1 &&
        eval_comp(cs_eq(cs_fst(cs_snd(func_eq)), y), s) == 1 &&
        eval_comp(cs_eq(cs_snd(cs_snd(func_eq)), z), s) == 1 &&
        eval_comp(cs_eq(cs_fst(cs_snd(iff_left)), y), s) == 1 &&
        eval_comp(cs_eq(cs_snd(cs_snd(iff_left)), v), s) == 1 &&
        eval_comp(cs_eq(cs_fst(cs_snd(cs_fst(cs_snd(range_and)))), x), s) == 1 &&
        eval_comp(cs_eq(cs_snd(cs_snd(cs_fst(cs_snd(range_and)))), u), s) == 1 &&
        //  Phi check
        eval_comp(cs_eq(phi_cs, phi_prime), s) == 1 &&
        //  Subst check
        eval_comp(cs_comp(check_subst_comp(), cs_pair(phi_cs, cs_pair(subst_phi_cs, z))), s) != 0 &&
        //  Variable evaluations (needed for distinct checks in compose)
        eval_comp(x, s) == x_var &&
        eval_comp(y, s) == y_var &&
        eval_comp(z, s) == z_var &&
        eval_comp(u, s) == u_var &&
        eval_comp(v, s) == v_var
    }),
{
    hide(eval_comp);
    let s = encode(f);
    let subst_phi_f = subst(phi, z_var, mk_var(y_var));

    //  ---- Sub-formula definitions ----
    let func_f = mk_forall(y_var, mk_forall(z_var, mk_implies(
        mk_and(phi, subst_phi_f), mk_eq(mk_var(y_var), mk_var(z_var))
    )));
    let range_f = mk_forall(u_var, mk_exists(v_var, mk_forall(y_var,
        mk_iff(
            mk_in(mk_var(y_var), mk_var(v_var)),
            mk_exists(x_var, mk_and(mk_in(mk_var(x_var), mk_var(u_var)), phi))
        )
    )));
    let fz_body_f = mk_implies(mk_and(phi, subst_phi_f), mk_eq(mk_var(y_var), mk_var(z_var)));
    let iff_left_f = mk_in(mk_var(y_var), mk_var(v_var));
    let iff_right_f = mk_exists(x_var, mk_and(mk_in(mk_var(x_var), mk_var(u_var)), phi));
    let iff_f = mk_iff(iff_left_f, iff_right_f);

    //  ---- Encoding structure (ambient) ----
    lemma_encode_forall(x_var, mk_implies(func_f, range_f));
    lemma_encode_implies(func_f, range_f);
    lemma_encode_forall(y_var, mk_forall(z_var, fz_body_f));
    lemma_encode_forall(z_var, fz_body_f);
    lemma_encode_implies(mk_and(phi, subst_phi_f), mk_eq(mk_var(y_var), mk_var(z_var)));
    lemma_encode_and(phi, subst_phi_f);
    lemma_encode_eq(mk_var(y_var), mk_var(z_var));
    lemma_encode_forall(u_var, mk_exists(v_var, mk_forall(y_var, iff_f)));
    lemma_encode_exists(v_var, mk_forall(y_var, iff_f));
    lemma_encode_forall(y_var, iff_f);
    lemma_encode_iff(iff_left_f, iff_right_f);
    lemma_encode_in(mk_var(y_var), mk_var(v_var));
    lemma_encode_exists(x_var, mk_and(mk_in(mk_var(x_var), mk_var(u_var)), phi));
    lemma_encode_and(mk_in(mk_var(x_var), mk_var(u_var)), phi);
    lemma_encode_in(mk_var(x_var), mk_var(u_var));

    //  ---- Computed encoding values ----
    let enc_and = pair(3nat, pair(encode(phi), encode(subst_phi_f)));
    let enc_eq = pair(0nat, pair(y_var, z_var));
    let enc_fz_body = pair(5nat, pair(enc_and, enc_eq));
    let enc_fz = pair(7nat, pair(z_var, enc_fz_body));
    let enc_func = pair(7nat, pair(y_var, enc_fz));
    let enc_in_yv = pair(1nat, pair(y_var, v_var));
    let enc_in_xu = pair(1nat, pair(x_var, u_var));
    let enc_range_and = pair(3nat, pair(enc_in_xu, encode(phi)));
    let enc_iff_right = pair(8nat, pair(x_var, enc_range_and));
    let enc_iff = pair(6nat, pair(enc_in_yv, enc_iff_right));
    let enc_ry = pair(7nat, pair(y_var, enc_iff));
    let enc_rv = pair(8nat, pair(v_var, enc_ry));
    let enc_range = pair(7nat, pair(u_var, enc_rv));
    let enc_impl = pair(5nat, pair(enc_func, enc_range));

    //  ---- CompSpec navigation (same as check_replacement_axiom) ----
    let body = cs_snd(cs_snd(CompSpec::Id));
    let func = cs_fst(cs_snd(body));
    let range = cs_snd(cs_snd(body));
    let x = cs_fst(cs_snd(CompSpec::Id));
    let y = cs_fst(cs_snd(func));
    let func_inner = cs_snd(cs_snd(func));
    let z = cs_fst(cs_snd(func_inner));
    let func_implies = cs_snd(cs_snd(func_inner));
    let func_and = cs_fst(cs_snd(func_implies));
    let func_eq = cs_snd(cs_snd(func_implies));
    let phi_cs = cs_fst(cs_snd(func_and));
    let subst_phi_cs = cs_snd(cs_snd(func_and));
    let u = cs_fst(cs_snd(range));
    let range_exists = cs_snd(cs_snd(range));
    let v = cs_fst(cs_snd(range_exists));
    let range_forall_y = cs_snd(cs_snd(range_exists));
    let y_prime = cs_fst(cs_snd(range_forall_y));
    let range_iff = cs_snd(cs_snd(range_forall_y));
    let iff_left = cs_fst(cs_snd(range_iff));
    let iff_right = cs_snd(cs_snd(range_iff));
    let x_prime = cs_fst(cs_snd(iff_right));
    let range_and = cs_snd(cs_snd(iff_right));
    let phi_prime = cs_snd(cs_snd(range_and));
    let in_xu = cs_fst(cs_snd(range_and));

    //  ====== NAVIGATION ======

    //  Top level: s = pair(7, pair(x_var, enc_impl))
    assert(eval_comp(cs_fst(CompSpec::Id), s) == 7 &&
           eval_comp(x, s) == x_var &&
           eval_comp(body, s) == enc_impl &&
           eval_comp(cs_fst(body), s) == 5) by {
        reveal(eval_comp);
        lemma_eval_fst(CompSpec::Id, s);
        lemma_unpair1_pair(7nat, pair(x_var, enc_impl));
        lemma_eval_snd(CompSpec::Id, s);
        lemma_unpair2_pair(7nat, pair(x_var, enc_impl));
        lemma_eval_fst(cs_snd(CompSpec::Id), s);
        lemma_unpair1_pair(x_var, enc_impl);
        lemma_eval_snd(cs_snd(CompSpec::Id), s);
        lemma_unpair2_pair(x_var, enc_impl);
        lemma_eval_fst(body, s);
        lemma_unpair1_pair(5nat, pair(enc_func, enc_range));
    }

    //  func, range
    assert(eval_comp(func, s) == enc_func &&
           eval_comp(range, s) == enc_range) by {
        reveal(eval_comp);
        lemma_eval_snd(body, s);
        lemma_unpair2_pair(5nat, pair(enc_func, enc_range));
        lemma_eval_fst(cs_snd(body), s);
        lemma_unpair1_pair(enc_func, enc_range);
        lemma_eval_snd(cs_snd(body), s);
        lemma_unpair2_pair(enc_func, enc_range);
    }

    //  FUNC: y, func_inner, tag
    assert(eval_comp(cs_fst(func), s) == 7 &&
           eval_comp(y, s) == y_var &&
           eval_comp(func_inner, s) == enc_fz) by {
        reveal(eval_comp);
        lemma_eval_fst(func, s);
        lemma_unpair1_pair(7nat, pair(y_var, enc_fz));
        lemma_eval_snd(func, s);
        lemma_unpair2_pair(7nat, pair(y_var, enc_fz));
        lemma_eval_fst(cs_snd(func), s);
        lemma_unpair1_pair(y_var, enc_fz);
        lemma_eval_snd(cs_snd(func), s);
        lemma_unpair2_pair(y_var, enc_fz);
    }

    //  func_inner: z, func_implies, tag
    assert(eval_comp(cs_fst(func_inner), s) == 7 &&
           eval_comp(z, s) == z_var &&
           eval_comp(func_implies, s) == enc_fz_body) by {
        reveal(eval_comp);
        lemma_eval_fst(func_inner, s);
        lemma_unpair1_pair(7nat, pair(z_var, enc_fz_body));
        lemma_eval_snd(func_inner, s);
        lemma_unpair2_pair(7nat, pair(z_var, enc_fz_body));
        lemma_eval_fst(cs_snd(func_inner), s);
        lemma_unpair1_pair(z_var, enc_fz_body);
        lemma_eval_snd(cs_snd(func_inner), s);
        lemma_unpair2_pair(z_var, enc_fz_body);
    }

    //  func_implies: and, eq, phi, subst_phi, tags
    assert(eval_comp(cs_fst(func_implies), s) == 5 &&
           eval_comp(func_and, s) == enc_and &&
           eval_comp(func_eq, s) == enc_eq &&
           eval_comp(cs_fst(func_and), s) == 3 &&
           eval_comp(cs_fst(func_eq), s) == 0 &&
           eval_comp(phi_cs, s) == encode(phi) &&
           eval_comp(subst_phi_cs, s) == encode(subst_phi_f)) by {
        reveal(eval_comp);
        lemma_eval_fst(func_implies, s);
        lemma_unpair1_pair(5nat, pair(enc_and, enc_eq));
        lemma_eval_snd(func_implies, s);
        lemma_unpair2_pair(5nat, pair(enc_and, enc_eq));
        lemma_eval_fst(cs_snd(func_implies), s);
        lemma_unpair1_pair(enc_and, enc_eq);
        lemma_eval_snd(cs_snd(func_implies), s);
        lemma_unpair2_pair(enc_and, enc_eq);
        lemma_eval_fst(func_and, s);
        lemma_unpair1_pair(3nat, pair(encode(phi), encode(subst_phi_f)));
        lemma_eval_fst(func_eq, s);
        lemma_unpair1_pair(0nat, pair(y_var, z_var));
        lemma_eval_snd(func_and, s);
        lemma_unpair2_pair(3nat, pair(encode(phi), encode(subst_phi_f)));
        lemma_eval_fst(cs_snd(func_and), s);
        lemma_unpair1_pair(encode(phi), encode(subst_phi_f));
        lemma_eval_snd(cs_snd(func_and), s);
        lemma_unpair2_pair(encode(phi), encode(subst_phi_f));
    }

    //  func_eq var contents
    assert(eval_comp(cs_fst(cs_snd(func_eq)), s) == y_var &&
           eval_comp(cs_snd(cs_snd(func_eq)), s) == z_var) by {
        reveal(eval_comp);
        lemma_eval_snd(func_eq, s);
        lemma_unpair2_pair(0nat, pair(y_var, z_var));
        lemma_eval_fst(cs_snd(func_eq), s);
        lemma_unpair1_pair(y_var, z_var);
        lemma_eval_snd(cs_snd(func_eq), s);
        lemma_unpair2_pair(y_var, z_var);
    }

    //  RANGE: u, range_exists, tag
    assert(eval_comp(cs_fst(range), s) == 7 &&
           eval_comp(u, s) == u_var &&
           eval_comp(range_exists, s) == enc_rv) by {
        reveal(eval_comp);
        lemma_eval_fst(range, s);
        lemma_unpair1_pair(7nat, pair(u_var, enc_rv));
        lemma_eval_snd(range, s);
        lemma_unpair2_pair(7nat, pair(u_var, enc_rv));
        lemma_eval_fst(cs_snd(range), s);
        lemma_unpair1_pair(u_var, enc_rv);
        lemma_eval_snd(cs_snd(range), s);
        lemma_unpair2_pair(u_var, enc_rv);
    }

    //  range_exists: v, range_forall_y, tag
    assert(eval_comp(cs_fst(range_exists), s) == 8 &&
           eval_comp(v, s) == v_var &&
           eval_comp(range_forall_y, s) == enc_ry) by {
        reveal(eval_comp);
        lemma_eval_fst(range_exists, s);
        lemma_unpair1_pair(8nat, pair(v_var, enc_ry));
        lemma_eval_snd(range_exists, s);
        lemma_unpair2_pair(8nat, pair(v_var, enc_ry));
        lemma_eval_fst(cs_snd(range_exists), s);
        lemma_unpair1_pair(v_var, enc_ry);
        lemma_eval_snd(cs_snd(range_exists), s);
        lemma_unpair2_pair(v_var, enc_ry);
    }

    //  range_forall_y: y_prime, range_iff, tag
    assert(eval_comp(cs_fst(range_forall_y), s) == 7 &&
           eval_comp(y_prime, s) == y_var &&
           eval_comp(range_iff, s) == enc_iff) by {
        reveal(eval_comp);
        lemma_eval_fst(range_forall_y, s);
        lemma_unpair1_pair(7nat, pair(y_var, enc_iff));
        lemma_eval_snd(range_forall_y, s);
        lemma_unpair2_pair(7nat, pair(y_var, enc_iff));
        lemma_eval_fst(cs_snd(range_forall_y), s);
        lemma_unpair1_pair(y_var, enc_iff);
        lemma_eval_snd(cs_snd(range_forall_y), s);
        lemma_unpair2_pair(y_var, enc_iff);
    }

    //  range_iff: iff_left, iff_right, tag
    assert(eval_comp(cs_fst(range_iff), s) == 6 &&
           eval_comp(iff_left, s) == enc_in_yv &&
           eval_comp(iff_right, s) == enc_iff_right) by {
        reveal(eval_comp);
        lemma_eval_fst(range_iff, s);
        lemma_unpair1_pair(6nat, pair(enc_in_yv, enc_iff_right));
        lemma_eval_snd(range_iff, s);
        lemma_unpair2_pair(6nat, pair(enc_in_yv, enc_iff_right));
        lemma_eval_fst(cs_snd(range_iff), s);
        lemma_unpair1_pair(enc_in_yv, enc_iff_right);
        lemma_eval_snd(cs_snd(range_iff), s);
        lemma_unpair2_pair(enc_in_yv, enc_iff_right);
    }

    //  iff_left details (In(y,v))
    assert(eval_comp(cs_fst(iff_left), s) == 1 &&
           eval_comp(cs_fst(cs_snd(iff_left)), s) == y_var &&
           eval_comp(cs_snd(cs_snd(iff_left)), s) == v_var) by {
        reveal(eval_comp);
        lemma_eval_fst(iff_left, s);
        lemma_unpair1_pair(1nat, pair(y_var, v_var));
        lemma_eval_snd(iff_left, s);
        lemma_unpair2_pair(1nat, pair(y_var, v_var));
        lemma_eval_fst(cs_snd(iff_left), s);
        lemma_unpair1_pair(y_var, v_var);
        lemma_eval_snd(cs_snd(iff_left), s);
        lemma_unpair2_pair(y_var, v_var);
    }

    //  iff_right: x_prime, range_and, tag
    assert(eval_comp(cs_fst(iff_right), s) == 8 &&
           eval_comp(x_prime, s) == x_var &&
           eval_comp(range_and, s) == enc_range_and) by {
        reveal(eval_comp);
        lemma_eval_fst(iff_right, s);
        lemma_unpair1_pair(8nat, pair(x_var, enc_range_and));
        lemma_eval_snd(iff_right, s);
        lemma_unpair2_pair(8nat, pair(x_var, enc_range_and));
        lemma_eval_fst(cs_snd(iff_right), s);
        lemma_unpair1_pair(x_var, enc_range_and);
        lemma_eval_snd(cs_snd(iff_right), s);
        lemma_unpair2_pair(x_var, enc_range_and);
    }

    //  range_and: in_xu, phi_prime, tag
    assert(eval_comp(cs_fst(range_and), s) == 3 &&
           eval_comp(in_xu, s) == enc_in_xu &&
           eval_comp(phi_prime, s) == encode(phi) &&
           eval_comp(cs_fst(in_xu), s) == 1) by {
        reveal(eval_comp);
        lemma_eval_fst(range_and, s);
        lemma_unpair1_pair(3nat, pair(enc_in_xu, encode(phi)));
        lemma_eval_snd(range_and, s);
        lemma_unpair2_pair(3nat, pair(enc_in_xu, encode(phi)));
        lemma_eval_fst(cs_snd(range_and), s);
        lemma_unpair1_pair(enc_in_xu, encode(phi));
        lemma_eval_snd(cs_snd(range_and), s);
        lemma_unpair2_pair(enc_in_xu, encode(phi));
        lemma_eval_fst(in_xu, s);
        lemma_unpair1_pair(1nat, pair(x_var, u_var));
    }

    //  in_xu var contents
    assert(eval_comp(cs_fst(cs_snd(in_xu)), s) == x_var &&
           eval_comp(cs_snd(cs_snd(in_xu)), s) == u_var) by {
        reveal(eval_comp);
        lemma_eval_snd(in_xu, s);
        lemma_unpair2_pair(1nat, pair(x_var, u_var));
        lemma_eval_fst(cs_snd(in_xu), s);
        lemma_unpair1_pair(x_var, u_var);
        lemma_eval_snd(cs_snd(in_xu), s);
        lemma_unpair2_pair(x_var, u_var);
    }

    //  ====== TAG CHECKS ======
    assert(eval_comp(cs_eq(cs_fst(CompSpec::Id), cs_const(7)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(body), cs_const(5)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(func), cs_const(7)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(func_inner), cs_const(7)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(func_implies), cs_const(5)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(func_and), cs_const(3)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(func_eq), cs_const(0)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(range), cs_const(7)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(range_exists), cs_const(8)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(range_forall_y), cs_const(7)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(range_iff), cs_const(6)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(iff_left), cs_const(1)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(iff_right), cs_const(8)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(range_and), cs_const(3)), s) == 1 &&
           eval_comp(cs_eq(cs_fst(in_xu), cs_const(1)), s) == 1
    ) by {
        reveal(eval_comp);
        lemma_eval_eq(cs_fst(CompSpec::Id), cs_const(7), s);
        lemma_eval_eq(cs_fst(body), cs_const(5), s);
        lemma_eval_eq(cs_fst(func), cs_const(7), s);
        lemma_eval_eq(cs_fst(func_inner), cs_const(7), s);
        lemma_eval_eq(cs_fst(func_implies), cs_const(5), s);
        lemma_eval_eq(cs_fst(func_and), cs_const(3), s);
        lemma_eval_eq(cs_fst(func_eq), cs_const(0), s);
        lemma_eval_eq(cs_fst(range), cs_const(7), s);
        lemma_eval_eq(cs_fst(range_exists), cs_const(8), s);
        lemma_eval_eq(cs_fst(range_forall_y), cs_const(7), s);
        lemma_eval_eq(cs_fst(range_iff), cs_const(6), s);
        lemma_eval_eq(cs_fst(iff_left), cs_const(1), s);
        lemma_eval_eq(cs_fst(iff_right), cs_const(8), s);
        lemma_eval_eq(cs_fst(range_and), cs_const(3), s);
        lemma_eval_eq(cs_fst(in_xu), cs_const(1), s);
    }

    //  ====== VAR CHECKS ======
    assert(eval_comp(cs_eq(y_prime, y), s) == 1 &&
           eval_comp(cs_eq(x_prime, x), s) == 1 &&
           eval_comp(cs_eq(cs_fst(cs_snd(func_eq)), y), s) == 1 &&
           eval_comp(cs_eq(cs_snd(cs_snd(func_eq)), z), s) == 1 &&
           eval_comp(cs_eq(cs_fst(cs_snd(iff_left)), y), s) == 1 &&
           eval_comp(cs_eq(cs_snd(cs_snd(iff_left)), v), s) == 1 &&
           eval_comp(cs_eq(cs_fst(cs_snd(in_xu)), x), s) == 1 &&
           eval_comp(cs_eq(cs_snd(cs_snd(in_xu)), u), s) == 1
    ) by {
        reveal(eval_comp);
        lemma_eval_eq(y_prime, y, s);
        lemma_eval_eq(x_prime, x, s);
        lemma_eval_eq(cs_fst(cs_snd(func_eq)), y, s);
        lemma_eval_eq(cs_snd(cs_snd(func_eq)), z, s);
        lemma_eval_eq(cs_fst(cs_snd(iff_left)), y, s);
        lemma_eval_eq(cs_snd(cs_snd(iff_left)), v, s);
        lemma_eval_eq(cs_fst(cs_snd(in_xu)), x, s);
        lemma_eval_eq(cs_snd(cs_snd(in_xu)), u, s);
    }

    //  ====== PHI CHECK ======
    assert(eval_comp(cs_eq(phi_cs, phi_prime), s) == 1) by {
        reveal(eval_comp);
        lemma_eval_eq(phi_cs, phi_prime, s);
    }

    //  ====== SUBST CHECK ======
    assert(eval_comp(cs_comp(check_subst_comp(), cs_pair(phi_cs, cs_pair(subst_phi_cs, z))), s) != 0) by {
        reveal(eval_comp);
        lemma_eval_pair(subst_phi_cs, z, s);
        lemma_eval_pair(phi_cs, cs_pair(subst_phi_cs, z), s);
        lemma_eval_comp(check_subst_comp(), cs_pair(phi_cs, cs_pair(subst_phi_cs, z)), s);
        lemma_check_subst_comp_backward(phi, z_var, mk_var(y_var));
    }
}

//  ====================================================================
//  Compose: distinct checks + chain composition + final composition
//  ====================================================================

#[verifier::rlimit(500)]
proof fn replacement_compose(
    f: Formula, phi: Formula,
    x_var: nat, y_var: nat, z_var: nat, u_var: nat, v_var: nat,
)
    requires
        x_var != y_var, x_var != z_var, y_var != z_var,
        u_var != x_var, u_var != y_var, v_var != x_var, v_var != y_var, u_var != v_var,
        f == mk_forall(x_var, mk_implies(
            mk_forall(y_var, mk_forall(z_var, mk_implies(
                mk_and(phi, subst(phi, z_var, mk_var(y_var))),
                mk_eq(mk_var(y_var), mk_var(z_var))
            ))),
            mk_forall(u_var, mk_exists(v_var, mk_forall(y_var,
                mk_iff(
                    mk_in(mk_var(y_var), mk_var(v_var)),
                    mk_exists(x_var, mk_and(mk_in(mk_var(x_var), mk_var(u_var)), phi))
                )
            )))
        )),
    ensures eval_comp(check_replacement_axiom(), encode(f)) != 0,
{
    hide(eval_comp);

    //  Get tag/var/phi/subst evaluations + variable values
    replacement_tags_vars_phi_subst(f, phi, x_var, y_var, z_var, u_var, v_var);

    let s = encode(f);

    //  CompSpec navigation (same as check_replacement_axiom)
    let body = cs_snd(cs_snd(CompSpec::Id));
    let func = cs_fst(cs_snd(body));
    let range = cs_snd(cs_snd(body));
    let x = cs_fst(cs_snd(CompSpec::Id));
    let y = cs_fst(cs_snd(func));
    let func_inner = cs_snd(cs_snd(func));
    let z = cs_fst(cs_snd(func_inner));
    let func_implies = cs_snd(cs_snd(func_inner));
    let func_and = cs_fst(cs_snd(func_implies));
    let func_eq = cs_snd(cs_snd(func_implies));
    let phi_cs = cs_fst(cs_snd(func_and));
    let subst_phi = cs_snd(cs_snd(func_and));
    let u = cs_fst(cs_snd(range));
    let range_exists = cs_snd(cs_snd(range));
    let v = cs_fst(cs_snd(range_exists));
    let range_forall_y = cs_snd(cs_snd(range_exists));
    let y_prime = cs_fst(cs_snd(range_forall_y));
    let range_iff = cs_snd(cs_snd(range_forall_y));
    let iff_left = cs_fst(cs_snd(range_iff));
    let iff_right = cs_snd(cs_snd(range_iff));
    let x_prime = cs_fst(cs_snd(iff_right));
    let range_and = cs_snd(cs_snd(iff_right));
    let phi_prime = cs_snd(cs_snd(range_and));

    //  ---- Prove distinct checks using variable values from helper ----
    //  Helper ensures: eval_comp(x, s) == x_var, eval_comp(y, s) == y_var, etc.
    assert(eval_comp(cs_not(cs_eq(x, y)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(x, y), s); lemma_eval_eq(x, y, s);
    }
    assert(eval_comp(cs_not(cs_eq(x, z)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(x, z), s); lemma_eval_eq(x, z, s);
    }
    assert(eval_comp(cs_not(cs_eq(y, z)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(y, z), s); lemma_eval_eq(y, z, s);
    }
    assert(eval_comp(cs_not(cs_eq(u, x)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(u, x), s); lemma_eval_eq(u, x, s);
    }
    assert(eval_comp(cs_not(cs_eq(u, y)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(u, y), s); lemma_eval_eq(u, y, s);
    }
    assert(eval_comp(cs_not(cs_eq(v, x)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(v, x), s); lemma_eval_eq(v, x, s);
    }
    assert(eval_comp(cs_not(cs_eq(v, y)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(v, y), s); lemma_eval_eq(v, y, s);
    }
    assert(eval_comp(cs_not(cs_eq(u, v)), s) == 1) by {
        reveal(eval_comp); lemma_eval_cs_not(cs_eq(u, v), s); lemma_eval_eq(u, v, s);
    }

    //  ---- Build check group expressions ----
    let tc15 = cs_and(cs_eq(cs_fst(cs_fst(cs_snd(range_and))), cs_const(1)), cs_const(1));
    let tc14 = cs_and(cs_eq(cs_fst(range_and), cs_const(3)), tc15);
    let tc13 = cs_and(cs_eq(cs_fst(iff_right), cs_const(8)), tc14);
    let tc12 = cs_and(cs_eq(cs_fst(iff_left), cs_const(1)), tc13);
    let tc11 = cs_and(cs_eq(cs_fst(range_iff), cs_const(6)), tc12);
    let tc10 = cs_and(cs_eq(cs_fst(range_forall_y), cs_const(7)), tc11);
    let tc9 = cs_and(cs_eq(cs_fst(range_exists), cs_const(8)), tc10);
    let tc8 = cs_and(cs_eq(cs_fst(range), cs_const(7)), tc9);
    let tc7 = cs_and(cs_eq(cs_fst(func_eq), cs_const(0)), tc8);
    let tc6 = cs_and(cs_eq(cs_fst(func_and), cs_const(3)), tc7);
    let tc5 = cs_and(cs_eq(cs_fst(func_implies), cs_const(5)), tc6);
    let tc4 = cs_and(cs_eq(cs_fst(func_inner), cs_const(7)), tc5);
    let tc3 = cs_and(cs_eq(cs_fst(func), cs_const(7)), tc4);
    let tc2 = cs_and(cs_eq(cs_fst(body), cs_const(5)), tc3);
    let tag_checks = cs_and(cs_eq(cs_fst(CompSpec::Id), cs_const(7)), tc2);

    let vc8 = cs_and(cs_eq(cs_snd(cs_snd(cs_fst(cs_snd(range_and)))), u), cs_const(1));
    let vc7 = cs_and(cs_eq(cs_fst(cs_snd(cs_fst(cs_snd(range_and)))), x), vc8);
    let vc6 = cs_and(cs_eq(cs_snd(cs_snd(iff_left)), v), vc7);
    let vc5 = cs_and(cs_eq(cs_fst(cs_snd(iff_left)), y), vc6);
    let vc4 = cs_and(cs_eq(cs_snd(cs_snd(func_eq)), z), vc5);
    let vc3 = cs_and(cs_eq(cs_fst(cs_snd(func_eq)), y), vc4);
    let vc2 = cs_and(cs_eq(x_prime, x), vc3);
    let var_checks = cs_and(cs_eq(y_prime, y), vc2);

    let phi_check = cs_eq(phi_cs, phi_prime);
    let subst_check = cs_comp(check_subst_comp(), cs_pair(phi_cs, cs_pair(subst_phi, z)));

    let dc8 = cs_not(cs_eq(u, v));
    let dc7 = cs_and(cs_not(cs_eq(v, y)), dc8);
    let dc6 = cs_and(cs_not(cs_eq(v, x)), dc7);
    let dc5 = cs_and(cs_not(cs_eq(u, y)), dc6);
    let dc4 = cs_and(cs_not(cs_eq(u, x)), dc5);
    let dc3 = cs_and(cs_not(cs_eq(y, z)), dc4);
    let dc2 = cs_and(cs_not(cs_eq(x, z)), dc3);
    let distinct_checks = cs_and(cs_not(cs_eq(x, y)), dc2);

    //  ---- Compose tag_checks chain ----
    assert(eval_comp(tag_checks, s) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(cs_eq(cs_fst(cs_fst(cs_snd(range_and))), cs_const(1)), cs_const(1), s);
        lemma_eval_cs_and(cs_eq(cs_fst(range_and), cs_const(3)), tc15, s);
        lemma_eval_cs_and(cs_eq(cs_fst(iff_right), cs_const(8)), tc14, s);
        lemma_eval_cs_and(cs_eq(cs_fst(iff_left), cs_const(1)), tc13, s);
        lemma_eval_cs_and(cs_eq(cs_fst(range_iff), cs_const(6)), tc12, s);
        lemma_eval_cs_and(cs_eq(cs_fst(range_forall_y), cs_const(7)), tc11, s);
        lemma_eval_cs_and(cs_eq(cs_fst(range_exists), cs_const(8)), tc10, s);
        lemma_eval_cs_and(cs_eq(cs_fst(range), cs_const(7)), tc9, s);
        lemma_eval_cs_and(cs_eq(cs_fst(func_eq), cs_const(0)), tc8, s);
        lemma_eval_cs_and(cs_eq(cs_fst(func_and), cs_const(3)), tc7, s);
        lemma_eval_cs_and(cs_eq(cs_fst(func_implies), cs_const(5)), tc6, s);
        lemma_eval_cs_and(cs_eq(cs_fst(func_inner), cs_const(7)), tc5, s);
        lemma_eval_cs_and(cs_eq(cs_fst(func), cs_const(7)), tc4, s);
        lemma_eval_cs_and(cs_eq(cs_fst(body), cs_const(5)), tc3, s);
        lemma_eval_cs_and(cs_eq(cs_fst(CompSpec::Id), cs_const(7)), tc2, s);
    }

    //  ---- Compose var_checks chain ----
    assert(eval_comp(var_checks, s) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(cs_eq(cs_snd(cs_snd(cs_fst(cs_snd(range_and)))), u), cs_const(1), s);
        lemma_eval_cs_and(cs_eq(cs_fst(cs_snd(cs_fst(cs_snd(range_and)))), x), vc8, s);
        lemma_eval_cs_and(cs_eq(cs_snd(cs_snd(iff_left)), v), vc7, s);
        lemma_eval_cs_and(cs_eq(cs_fst(cs_snd(iff_left)), y), vc6, s);
        lemma_eval_cs_and(cs_eq(cs_snd(cs_snd(func_eq)), z), vc5, s);
        lemma_eval_cs_and(cs_eq(cs_fst(cs_snd(func_eq)), y), vc4, s);
        lemma_eval_cs_and(cs_eq(x_prime, x), vc3, s);
        lemma_eval_cs_and(cs_eq(y_prime, y), vc2, s);
    }

    //  ---- Compose distinct_checks chain ----
    assert(eval_comp(distinct_checks, s) != 0) by {
        reveal(eval_comp);
        lemma_eval_cs_and(cs_not(cs_eq(v, y)), dc8, s);
        lemma_eval_cs_and(cs_not(cs_eq(v, x)), dc7, s);
        lemma_eval_cs_and(cs_not(cs_eq(u, y)), dc6, s);
        lemma_eval_cs_and(cs_not(cs_eq(u, x)), dc5, s);
        lemma_eval_cs_and(cs_not(cs_eq(y, z)), dc4, s);
        lemma_eval_cs_and(cs_not(cs_eq(x, z)), dc3, s);
        lemma_eval_cs_and(cs_not(cs_eq(x, y)), dc2, s);
    }

    //  ---- Final composition via nonlinear_arith ----
    assert(eval_comp(subst_check, s) != 0);
    assert(eval_comp(phi_check, s) != 0);

    lemma_eval_cs_and(subst_check, distinct_checks, s);
    assert(eval_comp(cs_and(subst_check, distinct_checks), s) != 0) by (nonlinear_arith)
        requires eval_comp(subst_check, s) > 0, eval_comp(distinct_checks, s) > 0,
            eval_comp(cs_and(subst_check, distinct_checks), s) == eval_comp(subst_check, s) * eval_comp(distinct_checks, s);

    lemma_eval_cs_and(phi_check, cs_and(subst_check, distinct_checks), s);
    assert(eval_comp(cs_and(phi_check, cs_and(subst_check, distinct_checks)), s) != 0) by (nonlinear_arith)
        requires eval_comp(phi_check, s) > 0, eval_comp(cs_and(subst_check, distinct_checks), s) > 0,
            eval_comp(cs_and(phi_check, cs_and(subst_check, distinct_checks)), s) == eval_comp(phi_check, s) * eval_comp(cs_and(subst_check, distinct_checks), s);

    lemma_eval_cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks)), s);
    assert(eval_comp(cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks))), s) != 0) by (nonlinear_arith)
        requires eval_comp(var_checks, s) > 0, eval_comp(cs_and(phi_check, cs_and(subst_check, distinct_checks)), s) > 0,
            eval_comp(cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks))), s) == eval_comp(var_checks, s) * eval_comp(cs_and(phi_check, cs_and(subst_check, distinct_checks)), s);

    lemma_eval_cs_and(tag_checks, cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks))), s);
    assert(eval_comp(cs_and(tag_checks, cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks)))), s) != 0) by (nonlinear_arith)
        requires eval_comp(tag_checks, s) > 0, eval_comp(cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks))), s) > 0,
            eval_comp(cs_and(tag_checks, cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks)))), s) == eval_comp(tag_checks, s) * eval_comp(cs_and(var_checks, cs_and(phi_check, cs_and(subst_check, distinct_checks))), s);
}

//  ====================================================================
//  Public wrapper: extract witnesses and call compose
//  ====================================================================

pub proof fn lemma_check_replacement_axiom_correct(f: Formula)
    requires is_replacement_axiom(f),
    ensures eval_comp(check_replacement_axiom(), encode(f)) != 0,
{
    match f {
        Formula::Forall { var: x_var, sub: s1 } => {
            match *s1 {
                Formula::Implies { left: func_b, right: range_b } => {
                    match *func_b {
                        Formula::Forall { var: y_var, sub: s2 } => {
                            match *s2 {
                                Formula::Forall { var: z_var, sub: s3 } => {
                                    match *s3 {
                                        Formula::Implies { left: and_b, right: _eq_b } => {
                                            match *and_b {
                                                Formula::And { left: phi_b, right: _sp_b } => {
                                                    let phi = *phi_b;
                                                    match *range_b {
                                                        Formula::Forall { var: u_var, sub: s4 } => {
                                                            match *s4 {
                                                                Formula::Exists { var: v_var, sub: _s5 } => {
                                                                    replacement_compose(
                                                                        f, phi, x_var, y_var, z_var, u_var, v_var,
                                                                    );
                                                                },
                                                                _ => {},
                                                            }
                                                        },
                                                        _ => {},
                                                    }
                                                },
                                                _ => {},
                                            }
                                        },
                                        _ => {},
                                    }
                                },
                                _ => {},
                            }
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

} //  verus!
