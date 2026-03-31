use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::compspec_halts::*;
use crate::compspec_subst_helpers::*;
use crate::zfc::*;

verus! {

///  For a replacement axiom, establish the encoding structure.
///  This navigates the encoding tree and shows what each CompSpec
///  sub-expression evaluates to.
///
///  The encoding is:
///  f = Forall(x, Implies(FUNC, RANGE))
///  encode(f) = pair(7, pair(x, pair(5, pair(FUNC_enc, RANGE_enc))))
///
///  where FUNC = Forall(y, Forall(z, Implies(And(phi, subst_phi), Eq(y,z))))
///  and RANGE = Forall(u, Exists(v, Forall(y, Iff(In(y,v), Exists(x, And(In(x,u), phi))))))
proof fn replacement_encoding_structure(
    phi: Formula, x_var: nat, y_var: nat, z_var: nat, u_var: nat, v_var: nat,
)
    ensures ({
        let f = mk_forall(x_var, mk_implies(
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
        ));
        let x = encode(f);
        //  Top level: pair(7, pair(x_var, body))
        unpair1(x) == 7 &&
        unpair1(unpair2(x)) == x_var
    }),
{
    let func = mk_forall(y_var, mk_forall(z_var, mk_implies(
        mk_and(phi, subst(phi, z_var, mk_var(y_var))),
        mk_eq(mk_var(y_var), mk_var(z_var))
    )));
    let range = mk_forall(u_var, mk_exists(v_var, mk_forall(y_var,
        mk_iff(
            mk_in(mk_var(y_var), mk_var(v_var)),
            mk_exists(x_var, mk_and(mk_in(mk_var(x_var), mk_var(u_var)), phi))
        )
    )));
    let f = mk_forall(x_var, mk_implies(func, range));
    let x = encode(f);
    //  encode(Forall(x_var, body)) = pair(7, pair(x_var, encode(body)))
    lemma_unpair1_pair(7nat, pair(x_var, encode(mk_implies(func, range))));
    lemma_unpair2_pair(7nat, pair(x_var, encode(mk_implies(func, range))));
    lemma_unpair1_pair(x_var, encode(mk_implies(func, range)));
}

///  check_replacement_axiom returns nonzero for valid replacement axiom instances.
///
///  Due to the extreme depth of the encoding (5-7 levels of nested pairs),
///  the full proof requires ~200 lines of eval_comp chain proofs.
///
///  The proof structure:
///  1. Extract existential witnesses from is_replacement_axiom
///  2. Navigate the encoding tree (20+ unpair calls)
///  3. Show all 15 tag checks, 8 var checks, 1 phi check, 1 subst check, 8 distinct checks pass
///  4. Compose via cs_and chain
///
///  TODO: Complete the full proof. The pattern is identical to the other axiom proofs
///  but with deeper nesting. No new proof techniques needed.
pub proof fn lemma_check_replacement_axiom_correct(f: Formula)
    requires is_replacement_axiom(f),
    ensures eval_comp(check_replacement_axiom(), encode(f)) != 0,
{
    //  Extract witnesses via match on formula structure
    //  f = Forall(x, Implies(FUNC, RANGE))
    match f {
        Formula::Forall { var: x_var, sub } => {
            match *sub {
                Formula::Implies { left: func_box, right: range_box } => {
                    //  FUNC and RANGE are the two main sub-formulas
                    //  Each is deeply nested.
                    //  The check_replacement_axiom evaluates all 33 checks.
                    //  For a valid replacement axiom, all return 1.

                    //  TODO: Navigate the encoding tree and show each check passes.
                    //  This is the most tedious part — ~200 lines of mechanical proof.
                    //  Pattern: same as eq_subst_left_inner but with 5-7 levels of nesting.

                    //  The substitution check is the most interesting part:
                    //  It requires check_subst_comp to accept the substitution
                    //  subst(phi, z_var, mk_var(y_var)).
                    //  We already have lemma_check_subst_comp_backward for this.
                },
                _ => {},
            }
        },
        _ => {},
    }
}

} //  verus!
