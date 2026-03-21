use vstd::prelude::*;
use crate::pairing::*;
use crate::machine::*;

verus! {

// ============================================================
// CompSpec: Primitive Recursive Computation Specifications
// ============================================================
//
// A CompSpec is a formal witness that a function nat → nat is
// primitive recursive (hence register-machine computable).
//
// All functions are nat → nat. Multiple arguments are encoded
// via Cantor pairing: f(x, y) becomes f(pair(x, y)).

/// A specification of a primitive recursive computation.
pub enum CompSpec {
    /// Constant: input → value
    Const { value: nat },
    /// Identity: input → input
    Id,
    /// Successor: input → input + 1
    Succ,
    /// Predecessor (saturating): input → max(input - 1, 0)
    Pred,
    /// Addition: input → eval(left) + eval(right)
    Add { left: Box<CompSpec>, right: Box<CompSpec> },
    /// Multiplication: input → eval(left) * eval(right)
    Mul { left: Box<CompSpec>, right: Box<CompSpec> },
    /// Composition: input → eval(outer, eval(inner, input))
    Comp { outer: Box<CompSpec>, inner: Box<CompSpec> },
    /// Cantor pairing: input → pair(eval(left), eval(right))
    CantorPair { left: Box<CompSpec>, right: Box<CompSpec> },
    /// First projection: input → unpair1(eval(inner))
    CantorFst { inner: Box<CompSpec> },
    /// Second projection: input → unpair2(eval(inner))
    CantorSnd { inner: Box<CompSpec> },
    /// Conditional: input → if eval(cond) == 0 then eval(then_br) else eval(else_br)
    IfZero { cond: Box<CompSpec>, then_br: Box<CompSpec>, else_br: Box<CompSpec> },
    /// Equality: input → if eval(left) == eval(right) then 1 else 0
    Eq { left: Box<CompSpec>, right: Box<CompSpec> },
    /// Less-than: input → if eval(left) < eval(right) then 1 else 0
    Lt { left: Box<CompSpec>, right: Box<CompSpec> },
    /// Bounded primitive recursion:
    ///   count = eval(count_fn, input)
    ///   acc_0 = eval(base, input)
    ///   acc_{i+1} = eval(step, pair(i, pair(acc_i, input)))
    ///   result = acc_count
    BoundedRec { count_fn: Box<CompSpec>, base: Box<CompSpec>, step: Box<CompSpec> },
}

/// Iterate a step function `count` times.
///   iterate(f, 0, acc, input) = acc
///   iterate(f, n+1, acc, input) = iterate(f, n, f(pair(n, pair(acc, input))), input)
pub open spec fn iterate(
    step_fn: spec_fn(nat) -> nat,
    count: nat,
    acc: nat,
    input: nat,
) -> nat
    decreases count,
{
    if count == 0 {
        acc
    } else {
        iterate(
            step_fn,
            (count - 1) as nat,
            step_fn(pair((count - 1) as nat, pair(acc, input))),
            input,
        )
    }
}

/// Evaluate a CompSpec on an input.
pub open spec fn eval_comp(c: CompSpec, input: nat) -> nat
    decreases c,
{
    match c {
        CompSpec::Const { value } => value,
        CompSpec::Id => input,
        CompSpec::Succ => input + 1,
        CompSpec::Pred => if input > 0 { (input - 1) as nat } else { 0 },
        CompSpec::Add { left, right } =>
            eval_comp(*left, input) + eval_comp(*right, input),
        CompSpec::Mul { left, right } =>
            eval_comp(*left, input) * eval_comp(*right, input),
        CompSpec::Comp { outer, inner } =>
            eval_comp(*outer, eval_comp(*inner, input)),
        CompSpec::CantorPair { left, right } =>
            pair(eval_comp(*left, input), eval_comp(*right, input)),
        CompSpec::CantorFst { inner } =>
            unpair1(eval_comp(*inner, input)),
        CompSpec::CantorSnd { inner } =>
            unpair2(eval_comp(*inner, input)),
        CompSpec::IfZero { cond, then_br, else_br } =>
            if eval_comp(*cond, input) == 0 {
                eval_comp(*then_br, input)
            } else {
                eval_comp(*else_br, input)
            },
        CompSpec::Eq { left, right } =>
            if eval_comp(*left, input) == eval_comp(*right, input) { 1nat } else { 0nat },
        CompSpec::Lt { left, right } =>
            if eval_comp(*left, input) < eval_comp(*right, input) { 1nat } else { 0nat },
        CompSpec::BoundedRec { count_fn, base, step } => {
            let n = eval_comp(*count_fn, input);
            let b = eval_comp(*base, input);
            let step_fn = |x: nat| eval_comp(*step, x);
            iterate(step_fn, n, b, input)
        },
    }
}

// ============================================================
// Reduced Church-Turing Axiom
// ============================================================

/// Reduced Church-Turing axiom: every CompSpec-definable partial function
/// has a register machine implementation.
///
/// A "partial function" is specified by:
///   - halts_check: CompSpec whose output is nonzero iff the machine should halt
///   - output1, output2: CompSpec giving the two output values when halting
///
/// Justification: each CompSpec operation is primitive recursive.
/// Composition, pairing, bounded recursion preserve primitive recursiveness.
/// Every primitive recursive function is register-machine computable
/// (standard computability theory, independent of any domain-specific logic).
#[verifier::external_body]
pub proof fn axiom_computable_partial_fn(
    halts_check: CompSpec,
    output1: CompSpec,
    output2: CompSpec,
)
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> eval_comp(halts_check, s) != 0) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[1] == eval_comp(output1, s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == eval_comp(output2, s)
                )),
{
}

} // verus!
