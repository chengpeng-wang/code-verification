import QuickselectMachine
import CountedExecution
import ProofLib
import ProofLib.BV.WidthNorm

open Arm64 ProofLib

private def reciprocal : BitVec 64 := 0xe38e38e38e38e38f#64

private theorem reciprocal_nat (n : Nat) (hn : n < 2 ^ 64) :
    (n * 16397105843297379215) / 2 ^ 67 = n / 9 := by
  apply (Nat.div_eq_of_lt_le ?_ ?_)
  · omega
  · omega

theorem divideNine (n : BitVec 64) :
    mulHi64 n reciprocal >>> 3 = BitVec.ofNat 64 (n.toNat / 9) := by
  have hmul : n.toNat * reciprocal.toNat < 2 ^ 128 := by
    calc n.toNat * reciprocal.toNat < 2 ^ 64 * 2 ^ 64 :=
          Nat.mul_lt_mul'' n.isLt reciprocal.isLt
      _ = 2 ^ 128 := by decide
  have hhi : (n.toNat * reciprocal.toNat) / 2 ^ 64 < 2 ^ 64 := by omega
  have hq : n.toNat / 9 < 2 ^ 64 := by have := n.isLt; omega
  apply BitVec.eq_of_toNat_eq
  rw [mulHi64_eq_ofNat]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hq]
  rw [Nat.div_div_eq_div_mul]
  exact reciprocal_nat n.toNat n.isLt


namespace Example04Rust

set_option autoImplicit false

theorem fetch_off (base offset : BitVec 64) :
    (program base).fetch (base + offset) = (program 0).fetch offset := by
  unfold Program.fetch Program.externAt?
  simp only [show (program base).base = base from rfl, show (program 0).base = 0#64 from rfl,
    BitVec.add_comm base offset, BitVec.add_sub_cancel, BitVec.sub_zero]
  rfl

theorem execute_at (base offset : BitVec 64) (inst : Instr) (s : State)
    (hpc : s.pc = base + offset) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (fetch : (program 0).fetch offset = some inst) :
    Step (program base) s ((program base).evalInst inst s) := by
  apply Step.exec running
  apply Program.fetchMem_of_fetch loaded
  rwa [hpc, fetch_off]

/-- Extend an exact trace by a step whose PC points to a decoded instruction
in the linked image. This is used to rule out an early return to an outside PC. -/
theorem linked_step {base off : BitVec 64} {n : Nat} {s t final : State}
    (pc : s.pc = base + off) (decoded : ((program 0).fetch off).isSome = true)
    (step : Step (program base) s t) (rest : Example03C.CodeStepsN (program base) n t final) :
    Example03C.CodeStepsN (program base) (n + 1) s final := by
  obtain ⟨inst, fetch⟩ := Option.isSome_iff_exists.mp decoded
  exact .step (by rw [pc, fetch_off]; exact fetch) step rest

theorem steps_append {prog : Program} {a b : Nat} {s mid final : State}
    (first : StepsN prog a s mid) (last : StepsN prog b mid final) :
    StepsN prog (a + b) s final := by
  induction first with
  | refl => simpa using last
  | step h _ ih => simpa only [Nat.succ_add] using StepsN.step h (ih last)

private def multiplyHigh : Instr := .dataProc3 .W64 .UMULH (.gpr 8) (.gpr 21) (.gpr 22) .xzr
private def copyBase : Instr := .logicalShift .W64 .ORR .x0 .xzr (.gpr 20) .LSL 0
private def copyLength : Instr := .logicalShift .W64 .ORR .x1 .xzr (.gpr 21) .LSL 0
private def zeroStart : Instr := .logicalShift .W64 .ORR .x2 .xzr .xzr .LSL 0
private def shiftQuotient : Instr := .bitfield .W64 .UBFM (.gpr 5) (.gpr 8) 3 63
private def scaleFour : Instr := .bitfield .W64 .UBFM (.gpr 3) (.gpr 5) 62 61
private def scaleEight : Instr := .bitfield .W64 .UBFM (.gpr 4) (.gpr 5) 61 60
private def callHelper : Instr := .bl (-(0x21c#64))

/-- At the driver's pivot call site, the eight linked instructions construct
    the recursive helper arguments and transfer control to its entry. -/
theorem pivot_call_setup (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 0x200#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (constant : s.readReg64 (.gpr 22) = reciprocal) :
    ∃ next : State, Example03C.CodeStepsN (program base) 8 s next ∧
      next.pc = base ∧ next.status = .Running ∧ next.mem = s.mem ∧ next.sp = s.sp ∧
      CalleeSavedPreserved s next ∧
      next.readReg64 .lr = base + 0x220#64 ∧
      next.readReg64 .x0 = s.readReg64 (.gpr 20) ∧
      next.readReg64 .x1 = s.readReg64 (.gpr 21) ∧ next.readReg64 .x2 = 0#64 ∧
      let blockLength := BitVec.ofNat 64 ((s.readReg64 (.gpr 21)).toNat / 9)
      next.readReg64 (.gpr 5) = blockLength ∧
        next.readReg64 (.gpr 3) = blockLength <<< 2 ∧
        next.readReg64 (.gpr 4) = blockLength <<< 3 := by
  let p := program base
  let s1 := p.evalInst multiplyHigh s
  let s2 := p.evalInst copyBase s1
  let s3 := p.evalInst copyLength s2
  let s4 := p.evalInst zeroStart s3
  let s5 := p.evalInst shiftQuotient s4
  let s6 := p.evalInst scaleFour s5
  let s7 := p.evalInst scaleEight s6
  let s8 := p.evalInst callHelper s7
  have loaded1 : p.CodeLoaded s1.mem := loaded
  have loaded2 : p.CodeLoaded s2.mem := loaded
  have loaded3 : p.CodeLoaded s3.mem := loaded
  have loaded4 : p.CodeLoaded s4.mem := loaded
  have loaded5 : p.CodeLoaded s5.mem := loaded
  have loaded6 : p.CodeLoaded s6.mem := loaded
  have loaded7 : p.CodeLoaded s7.mem := loaded
  have pc1 : s1.pc = base + 0x204#64 := by change s.pc + 4#64 = _; rw [hpc, BitVec.add_assoc]; rfl
  have pc2 : s2.pc = base + 0x208#64 := by change s1.pc + 4#64 = _; rw [pc1, BitVec.add_assoc]; rfl
  have pc3 : s3.pc = base + 0x20c#64 := by change s2.pc + 4#64 = _; rw [pc2, BitVec.add_assoc]; rfl
  have pc4 : s4.pc = base + 0x210#64 := by change s3.pc + 4#64 = _; rw [pc3, BitVec.add_assoc]; rfl
  have pc5 : s5.pc = base + 0x214#64 := by change s4.pc + 4#64 = _; rw [pc4, BitVec.add_assoc]; rfl
  have pc6 : s6.pc = base + 0x218#64 := by change s5.pc + 4#64 = _; rw [pc5, BitVec.add_assoc]; rfl
  have pc7 : s7.pc = base + 0x21c#64 := by change s6.pc + 4#64 = _; rw [pc6, BitVec.add_assoc]; rfl
  refine ⟨s8, linked_step hpc (by decide +kernel) (execute_at base _ multiplyHigh s hpc running loaded (by decide +kernel))
    (linked_step pc1 (by decide +kernel) (execute_at base _ copyBase s1 pc1 running loaded1 (by decide +kernel))
    (linked_step pc2 (by decide +kernel) (execute_at base _ copyLength s2 pc2 running loaded2 (by decide +kernel))
    (linked_step pc3 (by decide +kernel) (execute_at base _ zeroStart s3 pc3 running loaded3 (by decide +kernel))
    (linked_step pc4 (by decide +kernel) (execute_at base _ shiftQuotient s4 pc4 running loaded4 (by decide +kernel))
    (linked_step pc5 (by decide +kernel) (execute_at base _ scaleFour s5 pc5 running loaded5 (by decide +kernel))
    (linked_step pc6 (by decide +kernel) (execute_at base _ scaleEight s6 pc6 running loaded6 (by decide +kernel))
    (linked_step pc7 (by decide +kernel) (execute_at base _ callHelper s7 pc7 running loaded7 (by decide +kernel))
      (.refl _)))))))), ?_⟩
  have pc8 : s8.pc = base := by
    change s7.pc + (-(0x21c#64)) = _
    rw [pc7, BitVec.add_assoc]
    have h : 0x21c#64 + (-(0x21c#64)) = 0#64 := by decide
    rw [h, BitVec.add_zero]
  have ret : s8.readReg64 .lr = base + 0x220#64 := by
    change s7.pc + 4#64 = _
    rw [pc7, BitVec.add_assoc]
    rfl
  refine ⟨pc8, running, rfl, rfl, ?_, ret, ?_⟩
  · simp [CalleeSavedPreserved, wp_norm, arm64_norm, s8, s7, s6, s5, s4, s3, s2, s1, p,
      multiplyHigh, copyBase, copyLength, zeroStart, shiftQuotient, scaleFour, scaleEight, callHelper]
  · simp [wp_norm, arm64_norm, fold_mulHi64, s8, s7, s6, s5, s4, s3, s2, s1, p, multiplyHigh, copyBase, copyLength, zeroStart,
      shiftQuotient, scaleFour, scaleEight, callHelper]
    simp only [show (BitfieldOp.UBFM == .UBFM) = true from rfl, ite_true]
    have quotient : mulHi64 (s.readReg64 (.gpr 21#5)) (s.readReg64 (.gpr 22#5)) >>> 3 =
        BitVec.ofNat 64 ((s.readReg64 (.gpr 21#5)).toNat / 9) := by
      rw [show s.readReg64 (.gpr 22#5) = reciprocal from constant]
      exact divideNine _
    rw [quotient]
    simp


/-- Saved registers and link register remain unchanged during partition. -/
def PartitionRegs (s t : State) : Prop :=
    CalleeSavedPreserved s t ∧ t.readReg64 .lr = s.readReg64 .lr

theorem PartitionRegs.trans {s t u : State} (st : PartitionRegs s t)
      (tu : PartitionRegs t u) : PartitionRegs s u :=
    ⟨st.1.trans tu.1, tu.2.trans st.2⟩

/-- Once the left scan has found a value below the pivot, the next three
    instructions advance its cursor. They return to the left-scan test only
    when the new cursor has not yet reached the right cursor. -/
theorem partition_left_advance (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 0x27c#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) :
    ∃ next : State, Example03C.CodeStepsN (program base) 3 s next ∧
      next.status = .Running ∧ next.mem = s.mem ∧ next.sp = s.sp ∧ PartitionRegs s next ∧
      next.readReg64 .x1 = s.readReg64 .x1 + 1#64 ∧
      next.readReg64 (.gpr 9) = s.readReg64 (.gpr 9) ∧
      next.readReg64 (.gpr 10) = s.readReg64 (.gpr 10) ∧
      next.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      next.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      next.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      next.pc = (if s.readReg64 (.gpr 9) = s.readReg64 .x1 + 1#64
        then base + 0x288#64 else base + 0x260#64) := by
  let inc : Instr := .addSubImm .W64 .ADD .x1 .x1 1#12 false
  let cmp : Instr := .addSubShift .W64 .SUBS .xzr (.gpr 9) .x1 .LSL 0
  let branch : Instr := .bCond .NE (-(0x24#64))
  let p := program base
  let s1 := p.evalInst inc s
  let s2 := p.evalInst cmp s1
  let s3 := p.evalInst branch s2
  have pc1 : s1.pc = base + 0x280#64 := by
    simp [s1, p, inc, hpc, wp_norm, arm64_norm, BitVec.add_assoc]
  have pc2 : s2.pc = base + 0x284#64 := by
    simp [s2, s1, p, inc, cmp, hpc, wp_norm, arm64_norm, BitVec.add_assoc]
  have run1 : s1.status = .Running := by
    simp [s1, p, inc, running, wp_norm, arm64_norm]
  have run2 : s2.status = .Running := by
    simp [s2, s1, p, inc, cmp, running, wp_norm, arm64_norm]
  have mem1 : s1.mem = s.mem := by simp [s1, p, inc, wp_norm, arm64_norm]
  have mem2 : s2.mem = s.mem := by simp [s2, s1, p, inc, cmp, wp_norm, arm64_norm]
  refine ⟨s3, linked_step hpc (by decide +kernel) (execute_at base _ inc s hpc running loaded (by decide +kernel))
    (linked_step pc1 (by decide +kernel) (execute_at base _ cmp s1 pc1 run1 (mem1.symm ▸ loaded) (by decide +kernel))
    (linked_step pc2 (by decide +kernel) (execute_at base _ branch s2 pc2 run2 (mem2.symm ▸ loaded) (by decide +kernel))
      (.refl _))), ?_⟩
  simp [s3, s2, s1, p, inc, cmp, branch, hpc, running, wp_norm, arm64_norm,
    BitVec.add_assoc, PartitionRegs, CalleeSavedPreserved]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1500000 in
/-- With the left cursor inside the active scan interval, the guard passes
    and the machine loads and compares the next element with the pivot. -/
theorem partition_left_probe (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 0x260#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (cursor : (s.readReg64 (.gpr 1#5)).toNat < (s.readReg64 (.gpr 10#5)).toNat)
    (pivotReadable : s.mem.canRead (s.readReg64 (.gpr 20#5)) 8 = true)
    (elemReadable : s.mem.canRead
      (s.readReg64 (.gpr 20#5) + ((s.readReg64 (.gpr 1#5) <<< 3) + 8#64)) 8 = true) :
    ∃ next : State, Example03C.CodeStepsN (program base) 7 s next ∧
      next.status = .Running ∧ next.mem = s.mem ∧ next.sp = s.sp ∧ PartitionRegs s next ∧
      next.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) ∧
      next.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      next.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) ∧
      next.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      next.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) ∧
      next.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      next.pc =
        if (s.mem.read64 (s.readReg64 (.gpr 20#5) + ((s.readReg64 (.gpr 1#5) <<< 3) + 8#64))).toInt <
            (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt
        then base + 0x27c#64 else base + 0x28c#64 := by
  let cmpCursor : Instr := .addSubShift .W64 .SUBS .xzr (.gpr 10#5) (.gpr 1#5) .LSL 0
  let branchInvalid : Instr := .bCond .EQ 172#64
  let calcAddr : Instr := .addSubShift .W64 .ADD (.gpr 11#5) (.gpr 20#5) (.gpr 1#5) .LSL 3
  let loadPivot : Instr := .ldr .W64 .X64 false (.gpr 12#5) (.Offset (.gpr 20#5) 0#64)
  let loadElem : Instr := .ldr .W64 .X64 false (.gpr 11#5) (.Offset (.gpr 11#5) 8#64)
  let cmpPivot : Instr := .addSubShift .W64 .SUBS .xzr (.gpr 11#5) (.gpr 12#5) .LSL 0
  let branchGE : Instr := .bCond .GE 20#64
  let p := program base
  let s3 := p.evalInst cmpCursor s
  let s4 := p.evalInst branchInvalid s3
  let s5 := p.evalInst calcAddr s4
  let s6 := p.evalInst loadPivot s5
  let s7 := p.evalInst loadElem s6
  let s8 := p.evalInst cmpPivot s7
  let s9 := p.evalInst branchGE s8
  have cmp2 : s.readReg64 (.gpr 10#5) ≠ s.readReg64 (.gpr 1#5) := by
    intro eq
    have := congrArg BitVec.toNat eq
    omega
  refine ⟨s9, linked_step hpc (by decide +kernel) (execute_at base _ cmpCursor s hpc running loaded (by decide +kernel))
    (linked_step (off := 0x264#64) ?_ (by decide +kernel) (execute_at base 0x264#64 branchInvalid s3 ?_ ?_ ?_ (by decide +kernel))
    (linked_step (off := 0x268#64) ?_ (by decide +kernel) (execute_at base 0x268#64 calcAddr s4 ?_ ?_ ?_ (by decide +kernel))
    (linked_step (off := 0x26c#64) ?_ (by decide +kernel) (execute_at base 0x26c#64 loadPivot s5 ?_ ?_ ?_ (by decide +kernel))
    (linked_step (off := 0x270#64) ?_ (by decide +kernel) (execute_at base 0x270#64 loadElem s6 ?_ ?_ ?_ (by decide +kernel))
    (linked_step (off := 0x274#64) ?_ (by decide +kernel) (execute_at base 0x274#64 cmpPivot s7 ?_ ?_ ?_ (by decide +kernel))
    (linked_step (off := 0x278#64) ?_ (by decide +kernel) (execute_at base 0x278#64 branchGE s8 ?_ ?_ ?_ (by decide +kernel))
      (.refl _))))))), ?_⟩
  all_goals simp [s9, s8, s7, s6, s5, s4, s3, p, cmpCursor,
    branchInvalid, calcAddr, loadPivot, loadElem, cmpPivot, branchGE, hpc, wp_norm, arm64_norm,
    BitVec.add_assoc, cmp2, pivotReadable, elemReadable, running, loaded, BitVec.slt_eq_decide,
    PartitionRegs, CalleeSavedPreserved]
  simp only [BitVec.sle_iff_toInt_le, ← Int.not_lt, ite_not]

end Example04Rust
