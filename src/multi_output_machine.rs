use vstd::prelude::*;
use crate::machine::*;

verus! {

// ============================================================
// Instruction constructors (avoids struct literal parsing issues in requires)
// ============================================================

pub open spec fn mk_inc(r: nat) -> Instruction {
    Instruction::Inc { register: r }
}

pub open spec fn mk_dj(r: nat, t: nat) -> Instruction {
    Instruction::DecJump { register: r, target: t }
}

// ============================================================
// Instruction primitives
// ============================================================

/// Shift register indices and PC offsets in an instruction sequence.
/// Halts are replaced with DecJump{scratch, halt_target} (unconditional jump).
pub open spec fn embed_instructions(
    instrs: Seq<Instruction>,
    reg_offset: nat,
    pc_offset: nat,
    halt_target: nat,
    scratch_reg: nat,
) -> Seq<Instruction> {
    Seq::new(instrs.len(), |i: int| match instrs[i] {
        Instruction::Inc { register } =>
            Instruction::Inc { register: register + reg_offset },
        Instruction::DecJump { register, target } =>
            Instruction::DecJump { register: register + reg_offset, target: target + pc_offset },
        Instruction::Halt =>
            Instruction::DecJump { register: scratch_reg, target: halt_target },
    })
}

/// Destructive copy: src → dst (dst must start at 0, src becomes 0).
/// 3 instructions starting at start_pc. Next instruction at start_pc + 3.
pub open spec fn copy_instrs(
    src: nat, dst: nat, scratch: nat, start_pc: nat,
) -> Seq<Instruction> {
    seq![
        Instruction::DecJump { register: src, target: start_pc + 3 },
        Instruction::Inc { register: dst },
        Instruction::DecJump { register: scratch, target: start_pc },
    ]
}

/// Triple distribute: src → (d1, d2, d3) simultaneously (src destroyed).
/// 5 instructions starting at start_pc. Next instruction at start_pc + 5.
pub open spec fn triple_dist_instrs(
    src: nat, d1: nat, d2: nat, d3: nat, scratch: nat, start_pc: nat,
) -> Seq<Instruction> {
    seq![
        Instruction::DecJump { register: src, target: start_pc + 5 },
        Instruction::Inc { register: d1 },
        Instruction::Inc { register: d2 },
        Instruction::Inc { register: d3 },
        Instruction::DecJump { register: scratch, target: start_pc },
    ]
}

// ============================================================
// Combined machine construction
// ============================================================

/// Register layout:
///   reg 0: output 0 (also initial input)
///   reg 1: output 1
///   reg 2: output 2
///   reg 3: scratch (always 0)
///   reg 4 .. 4+N_h-1: bank for rm_halts
///   reg 4+N_h .. 4+N_h+N_1-1: bank for rm_out1
///   reg 4+N_h+N_1 .. 4+N_h+N_1+N_2-1: bank for rm_out2

pub open spec fn build_multi_output(
    rm_h: RegisterMachine,
    rm_1: RegisterMachine,
    rm_2: RegisterMachine,
) -> RegisterMachine {
    let n_h = rm_h.instructions.len();
    let n_1 = rm_1.instructions.len();
    let n_2 = rm_2.instructions.len();
    let bh: nat = 4;
    let b1: nat = 4 + rm_h.num_regs;
    let b2: nat = 4 + rm_h.num_regs + rm_1.num_regs;
    let scratch: nat = 3;
    let nr = 4 + rm_h.num_regs + rm_1.num_regs + rm_2.num_regs;

    // PC layout: [dist(5)] [embed_h(n_h)] [copy_h(3)] [embed_1(n_1)]
    //            [copy_1(3)] [embed_2(n_2)] [copy_2(3)] [Halt(1)]
    let p0: nat = 0;                            // triple distribute
    let p1: nat = 5;                            // embedded rm_h
    let p2: nat = 5 + n_h;                      // copy bank_h[0] → reg 0
    let p3: nat = 8 + n_h;                      // embedded rm_1
    let p4: nat = 8 + n_h + n_1;                // copy bank_1[0] → reg 1
    let p5: nat = 11 + n_h + n_1;               // embedded rm_2
    let p6: nat = 11 + n_h + n_1 + n_2;         // copy bank_2[0] → reg 2
    let p7: nat = 14 + n_h + n_1 + n_2;         // Halt

    RegisterMachine {
        instructions:
            triple_dist_instrs(0, bh, b1, b2, scratch, p0)
            + embed_instructions(rm_h.instructions, bh, p1, p2, scratch)
            + copy_instrs(bh, 0, scratch, p2)
            + embed_instructions(rm_1.instructions, b1, p3, p4, scratch)
            + copy_instrs(b1, 1, scratch, p4)
            + embed_instructions(rm_2.instructions, b2, p5, p6, scratch)
            + copy_instrs(b2, 2, scratch, p6)
            + seq![Instruction::Halt],
        num_regs: nr,
    }
}

// ============================================================
// Triple distribute loop proof
// ============================================================

proof fn lemma_triple_dist_inner(
    m: RegisterMachine,
    c: Configuration,
    src: nat, d1: nat, d2: nat, d3: nat, scratch: nat,
    start_pc: nat,
    orig_val: nat, acc: nat, remaining: nat,
)
    requires
        start_pc + 5 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, start_pc + 5),
        m.instructions[(start_pc + 1) as int] == mk_inc(d1),
        m.instructions[(start_pc + 2) as int] == mk_inc(d2),
        m.instructions[(start_pc + 3) as int] == mk_inc(d3),
        m.instructions[(start_pc + 4) as int] == mk_dj(scratch, start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[d1 as int] == acc,
        c.registers[d2 as int] == acc,
        c.registers[d3 as int] == acc,
        c.registers[scratch as int] == 0,
        src < m.num_regs, d1 < m.num_regs, d2 < m.num_regs,
        d3 < m.num_regs, scratch < m.num_regs,
        src != d1, src != d2, src != d3, src != scratch,
        d1 != d2, d1 != d3, d1 != scratch,
        d2 != d3, d2 != scratch, d3 != scratch,
        acc + remaining == orig_val,
    ensures
        run(m, c, 5 * remaining + 1).pc == start_pc + 5,
        run(m, c, 5 * remaining + 1).registers[src as int] == 0,
        run(m, c, 5 * remaining + 1).registers[d1 as int] == orig_val,
        run(m, c, 5 * remaining + 1).registers[d2 as int] == orig_val,
        run(m, c, 5 * remaining + 1).registers[d3 as int] == orig_val,
        run(m, c, 5 * remaining + 1).registers[scratch as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int
            && r != src as int && r != d1 as int && r != d2 as int && r != d3 as int
            ==> run(m, c, 5 * remaining + 1).registers[r] == c.registers[r],
    decreases remaining,
{
    if remaining == 0 {
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 5);
        assert(c1.registers == c.registers);
    } else {
        let c1 = step(m, c).unwrap();   // DecJump: dec src, pc+1
        assert(c1.pc == start_pc + 1);
        let c2 = step(m, c1).unwrap();   // Inc d1
        assert(c2.pc == start_pc + 2);
        let c3 = step(m, c2).unwrap();   // Inc d2
        assert(c3.pc == start_pc + 3);
        let c4 = step(m, c3).unwrap();   // Inc d3
        assert(c4.pc == start_pc + 4);
        let c5 = step(m, c4).unwrap();   // DecJump scratch=0: jump to start
        assert(c5.pc == start_pc);
        assert(c5.registers[src as int] == (remaining - 1) as nat);
        assert(c5.registers[d1 as int] == acc + 1);
        assert(c5.registers[d2 as int] == acc + 1);
        assert(c5.registers[d3 as int] == acc + 1);
        assert(c5.registers[scratch as int] == 0);
        lemma_triple_dist_inner(m, c5, src, d1, d2, d3, scratch,
            start_pc, orig_val, acc + 1, (remaining - 1) as nat);
    }
}

// ============================================================
// Destructive copy loop proof
// ============================================================

proof fn lemma_copy_loop_inner(
    m: RegisterMachine,
    c: Configuration,
    src: nat, dst: nat, scratch: nat,
    start_pc: nat,
    orig_val: nat, acc: nat, remaining: nat,
)
    requires
        start_pc + 3 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(dst),
        m.instructions[(start_pc + 2) as int] == mk_dj(scratch, start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[dst as int] == acc,
        c.registers[scratch as int] == 0,
        src < m.num_regs, dst < m.num_regs, scratch < m.num_regs,
        src != dst, src != scratch, dst != scratch,
        acc + remaining == orig_val,
    ensures
        run(m, c, 3 * remaining + 1).pc == start_pc + 3,
        run(m, c, 3 * remaining + 1).registers[dst as int] == orig_val,
        run(m, c, 3 * remaining + 1).registers[src as int] == 0,
        run(m, c, 3 * remaining + 1).registers[scratch as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            ==> run(m, c, 3 * remaining + 1).registers[r] == c.registers[r],
    decreases remaining,
{
    if remaining == 0 {
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 3);
        assert(c1.registers == c.registers);
    } else {
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 1);
        let c2 = step(m, c1).unwrap();
        assert(c2.pc == start_pc + 2);
        let c3 = step(m, c2).unwrap();
        assert(c3.pc == start_pc);
        assert(c3.registers[src as int] == (remaining - 1) as nat);
        assert(c3.registers[dst as int] == acc + 1);
        assert(c3.registers[scratch as int] == 0);
        lemma_copy_loop_inner(m, c3, src, dst, scratch, start_pc,
            orig_val, acc + 1, (remaining - 1) as nat);
    }
}

// ============================================================
// Embedded machine simulation
// ============================================================

pub open spec fn embed_configs_agree(
    rm_sub: RegisterMachine,
    reg_offset: nat,
    pc_offset: nat,
    scratch: nat,
    c_sub: Configuration,
    c: Configuration,
) -> bool {
    c.pc == c_sub.pc + pc_offset &&
    c_sub.registers.len() == rm_sub.num_regs &&
    (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
        c.registers[(r + reg_offset) as int] == c_sub.registers[r]) &&
    c.registers[scratch as int] == 0
}

proof fn lemma_embed_step_sim(
    rm_sub: RegisterMachine,
    m: RegisterMachine,
    reg_offset: nat,
    pc_offset: nat,
    halt_target: nat,
    scratch: nat,
    c_sub: Configuration,
    c: Configuration,
)
    requires
        machine_wf(rm_sub),
        config_wf(rm_sub, c_sub),
        !is_halted(rm_sub, c_sub),
        embed_configs_agree(rm_sub, reg_offset, pc_offset, scratch, c_sub, c),
        c.registers.len() == m.num_regs,
        forall|i: int| 0 <= i < rm_sub.instructions.len() ==>
            m.instructions[(i + pc_offset) as int] ==
                embed_instructions(rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch)[i],
        reg_offset + rm_sub.num_regs <= m.num_regs,
        scratch < m.num_regs,
        scratch < reg_offset || scratch >= reg_offset + rm_sub.num_regs,
        pc_offset + rm_sub.instructions.len() <= m.instructions.len(),
    ensures
        step(rm_sub, c_sub) is Some,
        step(m, c) is Some,
        embed_configs_agree(
            rm_sub, reg_offset, pc_offset, scratch,
            step(rm_sub, c_sub).unwrap(),
            step(m, c).unwrap(),
        ),
        step(m, c).unwrap().registers.len() == m.num_regs,
        config_wf(rm_sub, step(rm_sub, c_sub).unwrap()),
{
    reveal(machine_wf);
    let pc = c_sub.pc;
    let instr = rm_sub.instructions[pc as int];
    let m_instr = m.instructions[c.pc as int];
    assert(m_instr == embed_instructions(
        rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch)[pc as int]);
    let s_sub = step(rm_sub, c_sub).unwrap();
    let s_m = step(m, c).unwrap();
    match instr {
        Instruction::Inc { register: r } => {
            assert(m_instr == mk_inc(r + reg_offset));
            assert forall|j: int| 0 <= j < rm_sub.num_regs as int implies
                s_m.registers[(j + reg_offset) as int] == s_sub.registers[j]
            by {
                if j == r as int {
                    assert(c.registers[(j + reg_offset) as int] == c_sub.registers[j]);
                }
            };
            assert(s_m.registers[scratch as int] == 0) by {
                assert((r + reg_offset) != scratch);
            };
        },
        Instruction::DecJump { register: r, target: t } => {
            assert(m_instr == mk_dj(r + reg_offset, t + pc_offset));
            assert(c.registers[(r + reg_offset) as int] == c_sub.registers[r as int]);
            assert forall|j: int| 0 <= j < rm_sub.num_regs as int implies
                s_m.registers[(j + reg_offset) as int] == s_sub.registers[j]
            by {
                if c_sub.registers[r as int] > 0 && j == r as int {
                    assert(c.registers[(j + reg_offset) as int] == c_sub.registers[j]);
                }
            };
            assert(s_m.registers[scratch as int] == 0) by {
                if c_sub.registers[r as int] > 0 { assert((r + reg_offset) != scratch); }
            };
        },
        Instruction::Halt => { assert(false); },
    }
}

proof fn lemma_embed_reaches_target(
    rm_sub: RegisterMachine,
    m: RegisterMachine,
    reg_offset: nat,
    pc_offset: nat,
    halt_target: nat,
    scratch: nat,
    c_sub: Configuration,
    c: Configuration,
    fuel: nat,
)
    requires
        machine_wf(rm_sub),
        config_wf(rm_sub, c_sub),
        embed_configs_agree(rm_sub, reg_offset, pc_offset, scratch, c_sub, c),
        c.registers.len() == m.num_regs,
        run_halts(rm_sub, c_sub, fuel),
        forall|i: int| 0 <= i < rm_sub.instructions.len() ==>
            m.instructions[(i + pc_offset) as int] ==
                embed_instructions(rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch)[i],
        reg_offset + rm_sub.num_regs <= m.num_regs,
        scratch < m.num_regs,
        scratch < reg_offset || scratch >= reg_offset + rm_sub.num_regs,
        pc_offset + rm_sub.instructions.len() <= m.instructions.len(),
        halt_target <= m.instructions.len(),
        halt_target == pc_offset + rm_sub.instructions.len(),
    ensures ({
        let c_sub_halt = run(rm_sub, c_sub, fuel);
        exists|g: nat| g <= fuel + 1 &&
            run(m, c, g).pc == halt_target &&
            (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, c, g).registers[(r + reg_offset) as int] == c_sub_halt.registers[r]) &&
            run(m, c, g).registers[scratch as int] == 0 &&
            run(m, c, g).registers.len() == m.num_regs
    }),
    decreases fuel,
{
    reveal(machine_wf);
    let n = rm_sub.instructions.len();
    if is_halted(rm_sub, c_sub) {
        lemma_halted_run_identity(rm_sub, c_sub, fuel);
        if c_sub.pc >= n {
            assert(c_sub.pc == n);
            assert(c.pc == halt_target);
        } else {
            assert(rm_sub.instructions[c_sub.pc as int] is Halt);
            let embedded = embed_instructions(
                rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch);
            assert(m.instructions[c.pc as int] == embedded[c_sub.pc as int]);
            assert(m.instructions[c.pc as int] == mk_dj(scratch, halt_target));
            let next = step(m, c).unwrap();
            assert(next.pc == halt_target);
            assert(next.registers == c.registers);
        }
    } else {
        assert(fuel > 0);
        lemma_embed_step_sim(rm_sub, m, reg_offset, pc_offset, halt_target, scratch, c_sub, c);
        let s_sub = step(rm_sub, c_sub).unwrap();
        let s_m = step(m, c).unwrap();
        lemma_embed_reaches_target(rm_sub, m, reg_offset, pc_offset, halt_target, scratch,
            s_sub, s_m, (fuel - 1) as nat);
        let c_sub_halt = run(rm_sub, s_sub, (fuel - 1) as nat);
        let g_inner: nat = choose|g: nat| g <= fuel &&
            run(m, s_m, g).pc == halt_target &&
            (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, s_m, g).registers[(r + reg_offset) as int] == c_sub_halt.registers[r]) &&
            run(m, s_m, g).registers[scratch as int] == 0 &&
            run(m, s_m, g).registers.len() == m.num_regs;
        assert(run(m, c, g_inner + 1) == run(m, s_m, g_inner));
        assert(run(rm_sub, c_sub, fuel) == c_sub_halt);
    }
}

// ============================================================
// Well-formedness of the combined machine
// ============================================================

proof fn lemma_build_multi_output_wf(
    rm_h: RegisterMachine,
    rm_1: RegisterMachine,
    rm_2: RegisterMachine,
)
    requires
        machine_wf(rm_h),
        machine_wf(rm_1),
        machine_wf(rm_2),
    ensures
        machine_wf(build_multi_output(rm_h, rm_1, rm_2)),
        build_multi_output(rm_h, rm_1, rm_2).num_regs >= 3,
{
    reveal(machine_wf);
    let m = build_multi_output(rm_h, rm_1, rm_2);
    let n_h = rm_h.instructions.len();
    let n_1 = rm_1.instructions.len();
    let n_2 = rm_2.instructions.len();
    let bh: nat = 4;
    let b1: nat = 4 + rm_h.num_regs;
    let b2: nat = 4 + rm_h.num_regs + rm_1.num_regs;
    let scratch: nat = 3;
    let nr = m.num_regs;
    let tl = m.instructions.len();
    let p1: nat = 5;
    let p2: nat = 5 + n_h;
    let p3: nat = 8 + n_h;
    let p4: nat = 8 + n_h + n_1;
    let p5: nat = 11 + n_h + n_1;
    let p6: nat = 11 + n_h + n_1 + n_2;
    let p7: nat = 14 + n_h + n_1 + n_2;
    assert(tl == p7 + 1);

    assert forall|i: int| #![trigger m.instructions[i]]
        0 <= i < tl as int
    implies match m.instructions[i] {
        Instruction::Inc { register } => register < nr,
        Instruction::DecJump { register, target } =>
            register < nr && target <= tl,
        Instruction::Halt => true,
    } by {
        // Each region: identify the instruction and check bounds
        if i < p1 as int {
        } else if i < p2 as int {
        } else if i < p3 as int {
        } else if i < p4 as int {
        } else if i < p5 as int {
        } else if i < p6 as int {
        } else if i < p7 as int {
        } else {
        }
    };
}

// ============================================================
// Main proof
// ============================================================

pub proof fn lemma_total_multi_output_machine(
    rm_halts: RegisterMachine,
    rm_out1: RegisterMachine,
    rm_out2: RegisterMachine,
    f_h: spec_fn(nat) -> nat,
    f_1: spec_fn(nat) -> nat,
    f_2: spec_fn(nat) -> nat,
)
    requires
        machine_wf(rm_halts) &&
        (forall|s: nat| halts(rm_halts, s)) &&
        (forall|s: nat| output(rm_halts, s) == f_h(s)),
        machine_wf(rm_out1) &&
        (forall|s: nat| halts(rm_out1, s)) &&
        (forall|s: nat| output(rm_out1, s) == f_1(s)),
        machine_wf(rm_out2) &&
        (forall|s: nat| halts(rm_out2, s)) &&
        (forall|s: nat| output(rm_out2, s) == f_2(s)),
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s)) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[0] == f_h(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[1] == f_1(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == f_2(s)
                )),
{
    lemma_build_multi_output_wf(rm_halts, rm_out1, rm_out2);
    // TODO: phase composition proof
    assume(false);
}

} // verus!
