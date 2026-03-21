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
// Core Church-Turing Axioms
// ============================================================

/// Core axiom 1: Every CompSpec defines a total computable function.
///
/// There exists a register machine that always halts and whose output
/// (register 0) equals eval_comp(c, input) for every input.
///
/// Justification: each CompSpec operation (constant, successor, predecessor,
/// addition, multiplication, composition, pairing, projection, conditional,
/// comparison, bounded recursion) is primitive recursive. Every primitive
/// recursive function is register-machine computable — this is a standard
/// theorem in computability theory.
#[verifier::external_body]
pub proof fn axiom_comp_spec_total(c: CompSpec)
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) &&
            (forall|s: nat| halts(rm, s)) &&
            (forall|s: nat| output(rm, s) == eval_comp(c, s)),
{
}

/// Core axiom 2: Three total register machines can be composed into a
/// partial machine that conditionally halts.
///
/// Given machines computing halts_fn, out1_fn, out2_fn (all total),
/// there exists a machine that:
///   - halts on input s iff halts_fn(s) != 0
///   - when halting, register 1 = out1_fn(s), register 2 = out2_fn(s)
///
/// Justification: standard register machine composition. The combined
/// machine runs the halts_fn machine, tests its output, and either
/// loops forever (if 0) or runs the two output machines and stores
/// results in registers 1 and 2.
#[verifier::external_body]
pub proof fn axiom_compose_partial_machine(
    rm_halts: RegisterMachine,
    rm_out1: RegisterMachine,
    rm_out2: RegisterMachine,
    halts_fn: spec_fn(nat) -> nat,
    out1_fn: spec_fn(nat) -> nat,
    out2_fn: spec_fn(nat) -> nat,
)
    requires
        machine_wf(rm_halts) &&
        (forall|s: nat| halts(rm_halts, s)) &&
        (forall|s: nat| output(rm_halts, s) == halts_fn(s)),
        machine_wf(rm_out1) &&
        (forall|s: nat| halts(rm_out1, s)) &&
        (forall|s: nat| output(rm_out1, s) == out1_fn(s)),
        machine_wf(rm_out2) &&
        (forall|s: nat| halts(rm_out2, s)) &&
        (forall|s: nat| output(rm_out2, s) == out2_fn(s)),
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> halts_fn(s) != 0) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[1] == out1_fn(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == out2_fn(s)
                )),
{
}

// ============================================================
// Derived Church-Turing Theorem
// ============================================================

/// Every CompSpec-definable partial function has a register machine.
///
/// Previously an axiom (external_body). Now derived from:
///   1. axiom_comp_spec_total (CompSpec → total register machine)
///   2. axiom_compose_partial_machine (compose total machines into partial one)
///
/// A "partial function" is specified by:
///   - halts_check: CompSpec whose output is nonzero iff the machine should halt
///   - output1, output2: CompSpec giving the two output values when halting
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
    // Step 1: Get total machines for each CompSpec
    axiom_comp_spec_total(halts_check);
    axiom_comp_spec_total(output1);
    axiom_comp_spec_total(output2);

    // Step 2: Choose the witness machines
    let rm_h = choose|rm: RegisterMachine|
        machine_wf(rm) &&
        (forall|s: nat| halts(rm, s)) &&
        (forall|s: nat| output(rm, s) == eval_comp(halts_check, s));
    let rm_1 = choose|rm: RegisterMachine|
        machine_wf(rm) &&
        (forall|s: nat| halts(rm, s)) &&
        (forall|s: nat| output(rm, s) == eval_comp(output1, s));
    let rm_2 = choose|rm: RegisterMachine|
        machine_wf(rm) &&
        (forall|s: nat| halts(rm, s)) &&
        (forall|s: nat| output(rm, s) == eval_comp(output2, s));

    // Step 3: Compose into a partial machine
    axiom_compose_partial_machine(
        rm_h, rm_1, rm_2,
        |s: nat| eval_comp(halts_check, s),
        |s: nat| eval_comp(output1, s),
        |s: nat| eval_comp(output2, s),
    );
}

} // verus!
