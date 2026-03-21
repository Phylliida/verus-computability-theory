use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::*;

verus! {

// ============================================================
// Modular Machines (Aanderaa-Cohen)
// ============================================================
//
// A modular machine operates on a triple (state, alpha, beta) where
// alpha and beta are non-negative integers. Transitions are
// unconditional: given state q and alpha ≡ r (mod m), the machine
// applies a fixed operation to alpha and beta and moves to a new state.
//
// This contrasts with register machines where DecJump conditionally
// branches on zero — the conditional zero-test cannot be directly
// encoded as an HNN conjugation relation.
//
// Modular machines encode register values via prime powers:
//   registers (r0, ..., rk) → alpha = p0^r0 * p1^r1 * ... * pk^rk
//
// Inc(r_i) becomes: multiply alpha by p_i
// DecJump(r_i, target) becomes:
//   - if alpha ≡ 0 (mod p_i): divide alpha by p_i, advance
//   - if alpha ≢ 0 (mod p_i): identity, jump to target
//
// Each transition is unconditional (just check residue), enabling
// direct HNN conjugation encoding.

// ============================================================
// Types
// ============================================================

/// Operation on a register variable (alpha or beta).
pub enum ModOp {
    /// Multiply by a constant c > 0.
    Mul { c: nat },
    /// Divide by a constant c > 0 (assumes divisibility).
    Div { c: nat },
    /// Identity (leave unchanged).
    Id,
}

/// A modular machine quadruple: from (state, residue mod modulus)
/// apply operations to alpha/beta and transition to next_state.
pub struct ModularQuadruple {
    /// Current state.
    pub state: nat,
    /// Required residue of alpha modulo `modulus`.
    pub residue: nat,
    /// Modulus to check against (> 0).
    pub modulus: nat,
    /// State to transition to.
    pub next_state: nat,
    /// Operation on alpha.
    pub alpha_op: ModOp,
    /// Operation on beta (usually Id for our encoding).
    pub beta_op: ModOp,
}

/// A modular machine: finite set of quadruples with designated
/// halt state and state count.
pub struct ModularMachine {
    /// Total number of states (states are 0..num_states-1).
    pub num_states: nat,
    /// The halt state (no quadruple has this as source state).
    pub halt_state: nat,
    /// The quadruples (transition rules).
    pub quadruples: Seq<ModularQuadruple>,
}

/// A modular machine configuration.
pub struct ModularConfig {
    pub state: nat,
    pub alpha: nat,
    pub beta: nat,
}

// ============================================================
// Well-formedness
// ============================================================

/// A ModOp is well-formed: Mul/Div constants are positive.
pub open spec fn mod_op_wf(op: ModOp) -> bool {
    match op {
        ModOp::Mul { c } => c > 0,
        ModOp::Div { c } => c > 0,
        ModOp::Id => true,
    }
}

/// A quadruple is well-formed.
pub open spec fn quadruple_wf(mm: ModularMachine, q: ModularQuadruple) -> bool {
    q.state < mm.num_states &&
    q.next_state < mm.num_states &&
    q.modulus > 0 &&
    q.residue < q.modulus &&
    mod_op_wf(q.alpha_op) &&
    mod_op_wf(q.beta_op) &&
    // Source state is not the halt state
    q.state != mm.halt_state
}

/// A modular machine is well-formed: all quadruples are wf,
/// halt_state is a valid state, and quadruples are deterministic
/// (at most one matching quadruple for any (state, alpha) pair).
#[verifier::opaque]
pub open spec fn modular_machine_wf(mm: ModularMachine) -> bool {
    mm.halt_state < mm.num_states &&
    // All quadruples well-formed
    (forall|i: int| #![trigger mm.quadruples[i]]
        0 <= i < mm.quadruples.len() ==>
        quadruple_wf(mm, mm.quadruples[i])) &&
    // Deterministic: no two quadruples match the same (state, residue mod modulus)
    // We require: for same state, moduli are equal and residues are distinct
    // (stronger than needed but sufficient for our encoding)
    (forall|i: int, j: int|
        #![trigger mm.quadruples[i], mm.quadruples[j]]
        0 <= i < mm.quadruples.len() &&
        0 <= j < mm.quadruples.len() &&
        i != j &&
        mm.quadruples[i].state == mm.quadruples[j].state
        ==> mm.quadruples[i].modulus == mm.quadruples[j].modulus &&
            mm.quadruples[i].residue != mm.quadruples[j].residue)
}

// ============================================================
// Semantics
// ============================================================

/// Apply a ModOp to a value.
pub open spec fn apply_mod_op(op: ModOp, val: nat) -> nat {
    match op {
        ModOp::Mul { c } => val * c,
        ModOp::Div { c } => val / c,
        ModOp::Id => val,
    }
}

/// A quadruple matches a configuration: state matches and residue condition holds.
pub open spec fn quadruple_matches(q: ModularQuadruple, config: ModularConfig) -> bool {
    q.state == config.state &&
    config.alpha % q.modulus == q.residue
}

/// Find the matching quadruple index for a configuration, if any.
pub open spec fn find_matching_quadruple(
    mm: ModularMachine, config: ModularConfig,
) -> Option<nat> {
    if exists|i: nat| i < mm.quadruples.len() &&
        #[trigger] quadruple_matches(mm.quadruples[i as int], config)
    {
        Some(choose|i: nat| i < mm.quadruples.len() &&
            #[trigger] quadruple_matches(mm.quadruples[i as int], config))
    } else {
        None
    }
}

/// Execute a single step of the modular machine.
/// Returns None if halted (at halt state or no matching quadruple).
pub open spec fn modular_step(
    mm: ModularMachine, config: ModularConfig,
) -> Option<ModularConfig> {
    if config.state == mm.halt_state {
        None
    } else {
        match find_matching_quadruple(mm, config) {
            None => None,
            Some(i) => {
                let q = mm.quadruples[i as int];
                Some(ModularConfig {
                    state: q.next_state,
                    alpha: apply_mod_op(q.alpha_op, config.alpha),
                    beta: apply_mod_op(q.beta_op, config.beta),
                })
            }
        }
    }
}

/// The modular machine is halted.
pub open spec fn modular_is_halted(
    mm: ModularMachine, config: ModularConfig,
) -> bool {
    modular_step(mm, config) is None
}

/// Run the modular machine for `fuel` steps.
pub open spec fn modular_run(
    mm: ModularMachine, config: ModularConfig, fuel: nat,
) -> ModularConfig
    decreases fuel,
{
    if fuel == 0 {
        config
    } else {
        match modular_step(mm, config) {
            Some(next) => modular_run(mm, next, (fuel - 1) as nat),
            None => config,
        }
    }
}

/// The modular machine halts within `fuel` steps.
pub open spec fn modular_run_halts(
    mm: ModularMachine, config: ModularConfig, fuel: nat,
) -> bool
    decreases fuel,
{
    if fuel == 0 {
        modular_is_halted(mm, config)
    } else {
        modular_is_halted(mm, config) || match modular_step(mm, config) {
            Some(next) => modular_run_halts(mm, next, (fuel - 1) as nat),
            None => true,
        }
    }
}

/// The modular machine halts from the given configuration.
pub open spec fn modular_halts(
    mm: ModularMachine, config: ModularConfig,
) -> bool {
    exists|fuel: nat| modular_run_halts(mm, config, fuel)
}

// ============================================================
// Register-to-Modular Conversion
// ============================================================
//
// The conversion encodes register values as prime power products:
//   alpha = p_0^{r_0} * p_1^{r_1} * ... * p_{k-1}^{r_{k-1}}
// where p_i is the (i+1)-th prime (p_0=2, p_1=3, p_2=5, ...).
//
// Each Inc(r_i) becomes: Mul(p_i)
// Each DecJump(r_i, target) splits into:
//   - Quadruple with residue 0 mod p_i: Div(p_i), advance
//   - Quadruple with residue r mod p_i (for each r ≠ 0): Id, jump to target
//
// The initial configuration maps to:
//   state = 0, alpha = p_0^{input}, beta = 0

/// The initial modular config encoding register machine input.
pub open spec fn modular_initial_config(
    mm: ModularMachine, encoded_input: nat,
) -> ModularConfig {
    ModularConfig {
        state: 0,
        alpha: encoded_input,
        beta: 0,
    }
}

/// A register machine simulation by a modular machine:
/// the modular machine faithfully simulates the register machine's
/// halting behavior and output.
pub open spec fn modular_simulates_register(
    rm: RegisterMachine, mm: ModularMachine,
    encode_input: spec_fn(nat) -> nat,
    decode_output: spec_fn(ModularConfig) -> nat,
) -> bool {
    // For all inputs, halting is preserved
    (forall|input: nat|
        halts(rm, input) <==>
        modular_halts(mm, modular_initial_config(mm, encode_input(input)))) &&
    // For halting inputs, output is preserved
    (forall|input: nat|
        halts(rm, input) ==>
        decode_output(
            modular_run(
                mm,
                modular_initial_config(mm, encode_input(input)),
                choose|fuel: nat| #[trigger] modular_run_halts(
                    mm,
                    modular_initial_config(mm, encode_input(input)),
                    fuel,
                ),
            )
        ) == output(rm, input))
}

/// Axiom: any well-formed register machine can be converted to an
/// equivalent modular machine.
///
/// This requires number theory (prime factorization, CRT) not yet
/// in the codebase. The conversion is constructive (Aanderaa 1976)
/// and can be filled in once we have a prime number library.
#[verifier::external_body]
pub proof fn axiom_register_to_modular(rm: RegisterMachine)
    requires
        machine_wf(rm),
    ensures
        exists|mm: ModularMachine, encode_input: spec_fn(nat) -> nat,
               decode_output: spec_fn(ModularConfig) -> nat|
            modular_machine_wf(mm) &&
            modular_simulates_register(rm, mm, encode_input, decode_output),
{
}

// ============================================================
// Basic lemmas
// ============================================================

/// A halted modular machine stays halted.
pub proof fn lemma_modular_halted_run_identity(
    mm: ModularMachine, config: ModularConfig, fuel: nat,
)
    requires
        modular_is_halted(mm, config),
    ensures
        modular_run(mm, config, fuel) == config,
    decreases fuel,
{
    if fuel > 0 {
        assert(modular_step(mm, config) is None);
    }
}

/// If the machine halts at fuel f1, it also halts at any f2 >= f1.
pub proof fn lemma_modular_run_monotone(
    mm: ModularMachine, config: ModularConfig, f1: nat, f2: nat,
)
    requires
        modular_run_halts(mm, config, f1),
        f2 >= f1,
    ensures
        modular_run_halts(mm, config, f2),
        modular_run(mm, config, f1) == modular_run(mm, config, f2),
    decreases f1,
{
    if f1 == 0 {
        lemma_modular_halted_run_identity(mm, config, f2);
        lemma_modular_halted_run_halts(mm, config, f2);
    } else if modular_is_halted(mm, config) {
        lemma_modular_halted_run_identity(mm, config, f1);
        lemma_modular_halted_run_identity(mm, config, f2);
        lemma_modular_halted_run_halts(mm, config, f2);
    } else {
        let next = modular_step(mm, config).unwrap();
        if f2 == 0 {
            assert(false);
        } else {
            lemma_modular_run_monotone(mm, next, (f1 - 1) as nat, (f2 - 1) as nat);
        }
    }
}

/// A halted configuration halts within any fuel.
pub proof fn lemma_modular_halted_run_halts(
    mm: ModularMachine, config: ModularConfig, fuel: nat,
)
    requires
        modular_is_halted(mm, config),
    ensures
        modular_run_halts(mm, config, fuel),
{
}

/// If the machine halts at fuel f1 and f2, run gives the same result.
pub proof fn lemma_modular_run_deterministic(
    mm: ModularMachine, config: ModularConfig, f1: nat, f2: nat,
)
    requires
        modular_run_halts(mm, config, f1),
        modular_run_halts(mm, config, f2),
    ensures
        modular_run(mm, config, f1) == modular_run(mm, config, f2),
    decreases f1,
{
    if f1 == 0 {
        assert(modular_is_halted(mm, config));
        lemma_modular_halted_run_identity(mm, config, f2);
    } else if modular_is_halted(mm, config) {
        lemma_modular_halted_run_identity(mm, config, f1);
        lemma_modular_halted_run_identity(mm, config, f2);
    } else {
        let next = modular_step(mm, config).unwrap();
        if f2 == 0 {
            assert(false);
        } else {
            lemma_modular_run_deterministic(mm, next, (f1 - 1) as nat, (f2 - 1) as nat);
        }
    }
}

// ============================================================
// CEER-specific: modular machine for a CEER enumerator
// ============================================================
//
// Given a CEER e with enumerator machine M, we convert M to a
// modular machine MM. The CEER's declared pairs are preserved:
// if M halts on input s producing (a, b), then MM halts on
// encoded_input(s) producing a configuration that decodes to (a, b).

/// A modular machine simulates a CEER enumerator: halting and
/// declared pairs are preserved through the encoding.
pub open spec fn modular_simulates_ceer_enumerator(
    e: CEER, mm: ModularMachine,
    encode_input: spec_fn(nat) -> nat,
    decode_pair: spec_fn(ModularConfig) -> (nat, nat),
) -> bool {
    // Halting preserved
    (forall|s: nat|
        halts(e.enumerator, s) <==>
        modular_halts(mm, modular_initial_config(mm, encode_input(s)))) &&
    // Declared pairs preserved
    (forall|s: nat|
        halts(e.enumerator, s) ==> {
            let mm_config = modular_run(
                mm,
                modular_initial_config(mm, encode_input(s)),
                choose|fuel: nat| #[trigger] modular_run_halts(
                    mm,
                    modular_initial_config(mm, encode_input(s)),
                    fuel,
                ),
            );
            let (a, b) = decode_pair(mm_config);
            declared_pair(e, s) == Some((a, b))
        })
}

/// Axiom: a CEER's enumerator can be converted to a modular machine
/// that faithfully simulates its pair enumeration.
#[verifier::external_body]
pub proof fn axiom_ceer_to_modular(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|mm: ModularMachine,
               encode_input: spec_fn(nat) -> nat,
               decode_pair: spec_fn(ModularConfig) -> (nat, nat)|
            modular_machine_wf(mm) &&
            modular_simulates_ceer_enumerator(e, mm, encode_input, decode_pair),
{
}

} // verus!
