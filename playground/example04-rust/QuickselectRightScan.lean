import QuickselectBounds
import QuickselectArray

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false

/-- The right scan reads the array only while the unsigned left cursor is
    strictly below the right cursor. Otherwise it goes to the pivot exchange. -/
theorem partition_right_guard (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 0x28c#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) :
    ∃ next : State, CodeStepsN (program base) 2 s next ∧
      next.status = .Running ∧ next.mem = s.mem ∧ next.sp = s.sp ∧ PartitionRegs s next ∧
      next.readReg64 .x1 = s.readReg64 .x1 ∧
      next.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      next.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) ∧
      next.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      next.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      next.pc = base + (if (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 9#5)).toNat
        then 0x294#64 else 0x2d8#64) := by
  let compare : Instr := .addSubShift .W64 .SUBS .xzr .x1 (.gpr 9#5) .LSL 0
  let branch : Instr := .bCond .CS 0x48#64
  let s1 := (program base).evalInst compare s
  let s2 := (program base).evalInst branch s1
  have pc1 : s1.pc = base + 0x290#64 := by
    simp [s1, compare, hpc, wp_norm, arm64_norm, BitVec.add_assoc]
  have live1 : s1.status = .Running ∧ (program base).CodeLoaded s1.mem := by
    simpa [s1, compare, wp_norm, arm64_norm] using And.intro running loaded
  refine ⟨s2, linked_step hpc (by decide +kernel)
    (execute_at base _ compare s hpc running loaded (by decide +kernel))
    (linked_step pc1 (by decide +kernel)
      (execute_at base _ branch s1 pc1 live1.1 live1.2 (by decide +kernel))
      (.refl _)), ?_⟩
  simp [s2, s1, compare, branch, hpc, running, wp_norm, arm64_norm, BitVec.add_assoc,
    BitVec.ule_iff_toNat_le, PartitionRegs, CalleeSavedPreserved]
  split <;> simp_all

private def decrementRight : Instr := .addSubImm .W64 .SUB (.gpr 10#5) (.gpr 9#5) 1#12 false
private def checkRight : Instr := .addSubShift .W64 .SUBS .xzr (.gpr 10#5) (.gpr 8#5) .LSL 0
private def boundsBranch : Instr := .bCond .CS 0x74#64
private def loadPivot : Instr := .ldr .W64 .X64 false (.gpr 12#5) (.Offset (.gpr 20#5) 0#64)
private def loadRight : Instr := .ldr .W64 .X64 false (.gpr 11#5)
  (.RegOffset (.gpr 20#5) (.gpr 9#5) .UXTX 3)
private def moveRight : Instr := .logicalShift .W64 .ORR (.gpr 9#5) .xzr (.gpr 10#5) .LSL 0
private def compareRight : Instr := .addSubShift .W64 .SUBS .xzr (.gpr 12#5) (.gpr 11#5) .LSL 0
private def repeatScan : Instr := .bCond .LT (-(0x24#64))

/-- The guarded right scan decrements its cursor before the signed comparison.
    If the examined word exceeds the pivot, the loop tests the new cursor.
    Otherwise this path reaches the exchange block. -/
theorem partition_right_probe (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 0x294#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (inBounds : (s.readReg64 (.gpr 9#5) - 1#64).toNat < (s.readReg64 (.gpr 8#5)).toNat)
    (readablePivot : s.mem.canRead (s.readReg64 (.gpr 20#5)) 8 = true)
    (readableRight :
      s.mem.canRead (s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 9#5) <<< 3)) 8 = true) :
    ∃ next : State, CodeStepsN (program base) 8 s next ∧
      next.status = .Running ∧ next.mem = s.mem ∧ next.sp = s.sp ∧ PartitionRegs s next ∧
      next.readReg64 .x1 = s.readReg64 .x1 ∧
      next.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      next.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) - 1#64 ∧
      next.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 9#5) - 1#64 ∧
      next.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      next.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      let pivot := s.mem.read64 (s.readReg64 (.gpr 20#5))
      let right := s.mem.read64 (s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 9#5) <<< 3))
      next.readReg64 (.gpr 11#5) = right ∧
        next.pc = base + (if pivot.toInt < right.toInt then 0x28c#64 else 0x2b4#64) := by
  let p := program base
  let s1 := p.evalInst decrementRight s
  let s2 := p.evalInst checkRight s1
  let s3 := p.evalInst boundsBranch s2
  let s4 := p.evalInst loadPivot s3
  let s5 := p.evalInst loadRight s4
  let s6 := p.evalInst moveRight s5
  let s7 := p.evalInst compareRight s6
  let s8 := p.evalInst repeatScan s7
  have guardFalse : BitVec.ule (s.readReg64 (.gpr 8#5)) (s.readReg64 (.gpr 9#5) - 1#64) = false := by
    cases h : BitVec.ule (s.readReg64 (.gpr 8#5)) (s.readReg64 (.gpr 9#5) - 1#64)
    · rfl
    · have := BitVec.ule_iff_toNat_le.mp h
      omega
  have pc1 : s1.pc = base + 0x298#64 := by
    simp [s1, p, decrementRight, hpc, wp_norm, arm64_norm, BitVec.add_assoc]
  have pc2 : s2.pc = base + 0x29c#64 := by
    simp [s2, p, checkRight, pc1, wp_norm, arm64_norm, BitVec.add_assoc]
  have pc3 : s3.pc = base + 0x2a0#64 := by
    simp [s3, s2, s1, p, boundsBranch, checkRight, decrementRight, hpc, wp_norm, arm64_norm,
      guardFalse, BitVec.add_assoc]
  have step4 : s4 = (s3.writeReg64 (.gpr 12#5) (s.mem.read64 (s.readReg64 (.gpr 20#5)))).advancePC := by
    simp [s4, s3, s2, s1, p, loadPivot, boundsBranch, checkRight, decrementRight, hpc, wp_norm,
      arm64_norm, execLdr, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode,
      MemWidth.bytes, Memory.readSized, readablePivot, guardFalse]
  have step5 : s5 = (s4.writeReg64 (.gpr 11#5)
      (s.mem.read64 (s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 9#5) <<< 3)))).advancePC := by
    simp [s5, step4, s3, s2, s1, p, loadRight, boundsBranch, checkRight, decrementRight, hpc,
      wp_norm, arm64_norm, execLdr, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg,
      evalAddrMode, extendVal, MemWidth.bytes, Memory.readSized, readableRight, guardFalse]
  have pc4 : s4.pc = base + 0x2a4#64 := by
    simp [step4, pc3, arm64_norm, BitVec.add_assoc]
  have pc5 : s5.pc = base + 0x2a8#64 := by
    simp [step5, pc4, arm64_norm, BitVec.add_assoc]
  have pc6 : s6.pc = base + 0x2ac#64 := by
    simp [s6, p, moveRight, pc5, wp_norm, arm64_norm, BitVec.add_assoc]
  have pc7 : s7.pc = base + 0x2b0#64 := by
    simp [s7, p, compareRight, pc6, wp_norm, arm64_norm, BitVec.add_assoc]
  have live1 : s1.status = .Running ∧ p.CodeLoaded s1.mem := by
    simpa [s1, p, decrementRight, wp_norm, arm64_norm] using And.intro running loaded
  have live2 : s2.status = .Running ∧ p.CodeLoaded s2.mem := by
    simpa [s2, p, checkRight, wp_norm, arm64_norm] using live1
  have live3 : s3.status = .Running ∧ p.CodeLoaded s3.mem := by
    simpa [s3, s2, s1, p, boundsBranch, checkRight, decrementRight, wp_norm, arm64_norm,
      guardFalse] using And.intro running loaded
  have run4 : s4.status = .Running := by
    rw [step4]
    exact live3.1
  have run5 : s5.status = .Running := by
    rw [step5]
    exact run4
  have load4 : p.CodeLoaded s4.mem := by
    rw [step4]
    exact live3.2
  have load5 : p.CodeLoaded s5.mem := by
    rw [step5]
    exact load4
  have live6 : s6.status = .Running ∧ p.CodeLoaded s6.mem := by
    simpa [s6, p, moveRight, wp_norm, arm64_norm] using And.intro run5 load5
  have live7 : s7.status = .Running ∧ p.CodeLoaded s7.mem := by
    simpa [s7, p, compareRight, wp_norm, arm64_norm] using live6
  refine ⟨s8, linked_step hpc (by decide +kernel) (execute_at base _ decrementRight s hpc running loaded (by decide +kernel))
    (linked_step pc1 (by decide +kernel) (execute_at base _ checkRight s1 pc1 live1.1 live1.2 (by decide +kernel))
    (linked_step pc2 (by decide +kernel) (execute_at base _ boundsBranch s2 pc2 live2.1 live2.2 (by decide +kernel))
    (linked_step pc3 (by decide +kernel) (execute_at base _ loadPivot s3 pc3 live3.1 live3.2 (by decide +kernel))
    (linked_step pc4 (by decide +kernel) (execute_at base _ loadRight s4 pc4 run4 load4 (by decide +kernel))
    (linked_step pc5 (by decide +kernel) (execute_at base _ moveRight s5 pc5 run5 load5 (by decide +kernel))
    (linked_step pc6 (by decide +kernel) (execute_at base _ compareRight s6 pc6 live6.1 live6.2 (by decide +kernel))
    (linked_step pc7 (by decide +kernel) (execute_at base _ repeatScan s7 pc7 live7.1 live7.2 (by decide +kernel))
      (.refl _)))))))), ?_⟩
  simp [s8, s7, s6, step5, step4, s3, s2, s1, p, repeatScan, compareRight, moveRight,
    boundsBranch, checkRight, decrementRight, hpc, running, wp_norm, arm64_norm, guardFalse,
    BitVec.add_assoc, BitVec.slt_iff_toInt_lt, PartitionRegs, CalleeSavedPreserved]
  split <;> simp_all

/-- The exit at the pivot exchange costs one final guard. The exit at the
    partition exchange follows the last probe and carries the word it read. -/
structure RightScanResult (base : BitVec 64) (initial final : State) (count : Nat) : Prop where
  steps : CodeStepsN (program base) count initial final
  running : final.status = .Running
  memory : final.mem = initial.mem
  stackPointer : final.sp = initial.sp
  regs : PartitionRegs initial final
  left : final.readReg64 .x1 = initial.readReg64 .x1
  length : final.readReg64 (.gpr 8#5) = initial.readReg64 (.gpr 8#5)
  array : final.readReg64 (.gpr 20#5) = initial.readReg64 (.gpr 20#5)
  rest : final.readReg64 (.gpr 23#5) = initial.readReg64 (.gpr 23#5)
  lower : (initial.readReg64 .x1).toNat ≤ (final.readReg64 (.gpr 9#5)).toNat
  upper : (final.readReg64 (.gpr 9#5)).toNat ≤ (initial.readReg64 (.gpr 9#5)).toNat
  strict : ∀ k, (final.readReg64 (.gpr 9#5)).toNat ≤ k →
    k < (initial.readReg64 (.gpr 9#5)).toNat →
    (final.pc = base + 0x2d8#64 ∨ (final.readReg64 (.gpr 9#5)).toNat < k) →
    (initial.mem.read64 (initial.readReg64 (.gpr 20#5))).toInt <
      (initial.mem.read64 (wordAddr (initial.readReg64 (.gpr 20#5)) (k + 1))).toInt
  stopped :
    let j := final.readReg64 (.gpr 9#5)
    let probes := (initial.readReg64 (.gpr 9#5)).toNat - j.toNat
    (final.pc = base + 0x2d8#64 ∧ j = initial.readReg64 .x1 ∧ count = 10 * probes + 2) ∨
    (final.pc = base + 0x2b4#64 ∧ final.readReg64 (.gpr 10#5) = j ∧ count = 10 * probes ∧
      final.readReg64 (.gpr 11#5) =
        initial.mem.read64 (initial.readReg64 (.gpr 20#5) + ((j + 1#64) <<< 3)) ∧
      (final.readReg64 (.gpr 11#5)).toInt ≤
        (initial.mem.read64 (initial.readReg64 (.gpr 20#5))).toInt)

/-- Execute the right scan until its cursors meet or a probe finds the next
    word to exchange. Every probe costs ten instructions and moves the cursor
    once. A cursors-meet exit adds two instructions. -/
theorem partition_right_scan (base : BitVec 64) (s : State)
    (hpc : s.pc = base + 0x28c#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (ordered : (s.readReg64 .x1).toNat ≤ (s.readReg64 (.gpr 9#5)).toNat)
    (fits : (s.readReg64 (.gpr 9#5)).toNat ≤ (s.readReg64 (.gpr 8#5)).toNat)
    (readable : ∀ k : BitVec 64, k.toNat ≤ (s.readReg64 (.gpr 8#5)).toNat →
      s.mem.canRead (s.readReg64 (.gpr 20#5) + (k <<< 3)) 8 = true) :
    ∃ count final, RightScanResult base s final count := by
  generalize hj : (s.readReg64 (.gpr 9#5)).toNat = j at ordered fits ⊢
  induction j using Nat.strongRecOn generalizing s with
  | ind j ih =>
    obtain ⟨guardState, guardSteps, guardRun, guardMem, guardSP, guardRegs, guardLeft, guardLength,
      guardRight, guardBase, guardRest, guardPC⟩ := partition_right_guard base s hpc running loaded
    by_cases hasNext : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 9#5)).toNat
    · have decrement : (s.readReg64 (.gpr 9#5) - 1#64).toNat = j - 1 := by
        have one : 1#64 ≤ s.readReg64 (.gpr 9#5) := BitVec.le_def.mpr (by simp; omega)
        rw [BitVec.toNat_sub_of_le one, hj]
        rfl
      have inBounds : (guardState.readReg64 (.gpr 9#5) - 1#64).toNat <
          (guardState.readReg64 (.gpr 8#5)).toNat := by
        rw [guardRight, guardLength, decrement]
        omega
      have readPivot : guardState.mem.canRead (guardState.readReg64 (.gpr 20#5)) 8 = true := by
        rw [guardMem, guardBase]
        simpa using readable 0#64 (by simp)
      have readRight : guardState.mem.canRead
          (guardState.readReg64 (.gpr 20#5) + (guardState.readReg64 (.gpr 9#5) <<< 3)) 8 = true := by
        rw [guardMem, guardBase, guardRight]
        exact readable _ (by rwa [hj])
      obtain ⟨next, probeSteps, probeRun, probeMem, probeSP, probeRegs, probeLeft, probeLength, probeRight,
        probeX10, probeBase, probeRest, probeWord, probePC⟩ :=
        partition_right_probe base guardState (by simpa [hasNext] using guardPC) guardRun
          (guardMem.symm ▸ loaded) inBounds readPivot readRight
      rw [guardMem, guardBase, guardRight] at probeWord probePC
      have nextRight : (next.readReg64 (.gpr 9#5)).toNat = j - 1 := by
        rw [probeRight, guardRight, decrement]
      have nextMem := probeMem.trans guardMem
      have nextSP := probeSP.trans guardSP
      have nextLeft := probeLeft.trans guardLeft
      have nextLength := probeLength.trans guardLength
      have nextBase := probeBase.trans guardBase
      have nextRest := probeRest.trans guardRest
      have nextFits : j - 1 ≤ (next.readReg64 (.gpr 8#5)).toNat := by rw [nextLength]; omega
      have nextOrdered : (next.readReg64 .x1).toNat ≤ j - 1 := by rw [nextLeft]; omega
      have nextReadable : ∀ k : BitVec 64, k.toNat ≤ (next.readReg64 (.gpr 8#5)).toNat →
          next.mem.canRead (next.readReg64 (.gpr 20#5) + (k <<< 3)) 8 = true := by
        simpa only [nextLength, nextMem, nextBase] using readable
      have front : CodeStepsN (program base) 10 s next := guardSteps.append probeSteps
      by_cases above : (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt <
          (s.mem.read64 (s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 9#5) <<< 3))).toInt
      · obtain ⟨cost, final, tail⟩ := ih (j - 1) (by omega) next
          (by simpa [above] using probePC) probeRun (nextMem.symm ▸ loaded)
          nextReadable nextRight nextOrdered nextFits
        have finalUpper := tail.upper
        rw [nextRight] at finalUpper
        refine ⟨10 + cost, final, ⟨front.append tail.steps, tail.running,
          tail.memory.trans nextMem, tail.stackPointer.trans nextSP, (guardRegs.trans probeRegs).trans tail.regs, tail.left.trans nextLeft,
          tail.length.trans nextLength, tail.array.trans nextBase, tail.rest.trans nextRest,
          by simpa only [nextLeft] using tail.lower, by omega, ?_, ?_⟩⟩
        · intro k lo hi kind
          by_cases last : k + 1 = j
          · rw [last, ← hj, wordAddr_shift]
            exact above
          · rw [hj] at hi
            simpa only [nextMem, nextBase] using tail.strict k lo (by omega) kind
        · rcases tail.stopped with ⟨pc, eq, costEq⟩ | ⟨pc, eq, costEq, word, order⟩
          · rw [nextRight] at costEq
            exact Or.inl ⟨pc, eq.trans nextLeft, by omega⟩
          · rw [nextRight] at costEq
            exact Or.inr ⟨pc, eq, by omega,
              by simpa only [nextMem, nextBase] using word,
              by simpa only [nextMem, nextBase] using order⟩
      · refine ⟨10, next, ⟨front, probeRun, nextMem, nextSP, guardRegs.trans probeRegs, nextLeft, nextLength,
          nextBase, nextRest, by omega, by omega, ?_, Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩⟩
        · intro k lo hi kind
          rw [nextRight] at lo
          rcases kind with pc | strict
          · have actual : next.pc = base + 0x2b4#64 := by simpa [above] using probePC
            rw [actual, BitVec.add_right_inj] at pc
            exact False.elim ((by decide : (0x2b4#64 : BitVec 64) ≠ 0x2d8#64) pc)
          · rw [nextRight] at strict
            omega
        · simpa [above] using probePC
        · exact probeX10.trans probeRight.symm
        · omega
        · rw [probeRight, guardRight, BitVec.sub_add_cancel]
          exact probeWord
        · rw [probeWord]
          omega
    · have equal : guardState.readReg64 (.gpr 9#5) = s.readReg64 .x1 :=
        BitVec.eq_of_toNat_eq (by rw [guardRight]; omega)
      refine ⟨2, guardState, ⟨guardSteps, guardRun, guardMem, guardSP, guardRegs, guardLeft, guardLength,
        guardBase, guardRest, by rw [guardRight]; omega, by simp only [guardRight, Nat.le_refl],
        by intro k lo hi _; rw [guardRight] at lo; omega,
        Or.inl ⟨by simpa [hasNext] using guardPC, equal, by rw [guardRight]; simp⟩⟩⟩

end Example04Rust
