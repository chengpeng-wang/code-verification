import QuickselectBounds

open Arm64 ProofLib Example03C

namespace Example04Rust

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem tailStep {base off : BitVec 64} {s t : State} {inst : Instr}
    (pc : s.pc = base + off) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (fetch : (program 0).fetch off = some inst)
    (execution : (program base).evalInst inst s = t) : Step (program base) s t := by
  rw [← execution]
  exact execute_at base off inst s pc running loaded fetch

private def branchLeft : Instr := .bCond .CC (-(0x110#64))
private def branchDone : Instr := .bCond .EQ 0x18#64
private def skipPivot : Instr := .addSubImm .W64 .ADD (.gpr 8) .x1 1 false
private def advanceBase : Instr := .addSubShift .W64 .ADD (.gpr 20) (.gpr 20) (.gpr 8) .LSL 3
private def reduceLength : Instr := .addSubShift .W64 .SUB .x1 (.gpr 21) (.gpr 8) .LSL 0
private def reduceIndex : Instr := .addSubShift .W64 .SUB (.gpr 19) (.gpr 19) (.gpr 8) .LSL 0
private def loopBack : Instr := .b (-(0x12c#64))

private theorem advancePC_eq (s : State) : s.advancePC = s.setPC (s.pc + 4#64) := rfl

/-- The block after the final partition stores chooses the next slice or the epilogue.
The incoming flags are those produced by `CMP x19, x1`. X19 is the requested
index, X1 is the pivot index, X21 is the old length, and X20 is the array base.
The destinations and counts are for this linked `.text` image. -/
theorem quickselect_driver_tail (base : BitVec 64) (s : State) (n k pivot : Nat)
    (pc : s.pc = base + 0x2f4#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) (nFits : n < 2 ^ 64)
    (indexIn : k < n) (pivotIn : pivot < n)
    (lengthReg : s.readReg64 (.gpr 21) = BitVec.ofNat 64 n)
    (indexReg : s.readReg64 (.gpr 19) = BitVec.ofNat 64 k)
    (pivotReg : s.readReg64 .x1 = BitVec.ofNat 64 pivot)
    (flags : s.pstate = subsPState64 (s.readReg64 (.gpr 19)) (s.readReg64 .x1)) :
    ∃ count final, CodeStepsN (program base) count s final ∧
      final.mem = s.mem ∧ final.sp = s.sp ∧ final.status = .Running ∧
      final.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
      final.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      if k < pivot then
        count = 1 ∧ final.pc = base + 0x1e4#64 ∧
          final.readReg64 .x1 = BitVec.ofNat 64 pivot ∧
          final.readReg64 (.gpr 19) = BitVec.ofNat 64 k ∧
          final.readReg64 (.gpr 20) = s.readReg64 (.gpr 20)
      else if k = pivot then
        count = 2 ∧ final.pc = base + 0x310#64
      else
        count = 7 ∧ final.pc = base + 0x1e0#64 ∧
          final.readReg64 .x1 = BitVec.ofNat 64 (n - (pivot + 1)) ∧
          final.readReg64 (.gpr 19) = BitVec.ofNat 64 (k - (pivot + 1)) ∧
          final.readReg64 (.gpr 20) = s.readReg64 (.gpr 20) + (BitVec.ofNat 64 (pivot + 1) <<< 3) ∧
          (final.readReg64 (.gpr 19)).toNat < (final.readReg64 .x1).toNat := by
  have kValue : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
  have pivotValue : (BitVec.ofNat 64 pivot).toNat = pivot := Nat.mod_eq_of_lt (by omega)
  have lessFlag : ConditionHolds .CC s.pstate = decide (k < pivot) := by
    rw [flags, subsPState64, conditionHolds_cc_subs64, indexReg, pivotReg,
      BitVec.ult_eq_decide, kValue, pivotValue]
  have equalFlag : ConditionHolds .EQ s.pstate = decide (k = pivot) := by
    rw [flags, subsPState64, conditionHolds_eq_subs64, indexReg, pivotReg]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, kValue, pivotValue]
  by_cases left : k < pivot
  · let final := s.setPC (base + 0x1e4#64)
    have step : Step (program base) s final := by
      apply tailStep (inst := branchLeft) pc running loaded (by decide +kernel)
      simp [branchLeft, Program.evalInst, execInstWithSvc, lessFlag, left, pc,
        BitVec.add_assoc, final]
    refine ⟨1, final, linked_step pc (by decide +kernel) step (.refl _), rfl, rfl, running, rfl, rfl, ?_⟩
    rw [ite_eq_left left]
    exact ⟨rfl, rfl, pivotReg, indexReg, rfl⟩
  · let s1 := s.setPC (base + 0x2f8#64)
    have first : Step (program base) s s1 := by
      apply tailStep (inst := branchLeft) pc running loaded (by decide +kernel)
      simp [branchLeft, Program.evalInst, execInstWithSvc, lessFlag, left, pc, s1,
        State.advancePC, State.setPC, BitVec.add_assoc]
    by_cases done : k = pivot
    · let final := s1.setPC (base + 0x310#64)
      have second : Step (program base) s1 final := by
        apply tailStep (s := s1) (off := 0x2f8#64) (inst := branchDone) rfl running loaded (by decide +kernel)
        change (if ConditionHolds .EQ s.pstate then s1.setPC (s1.pc + 0x18#64)
          else s1.advancePC) = final
        simp [equalFlag, done, s1, final, BitVec.add_assoc]
      have steps : CodeStepsN (program base) 2 s final :=
        linked_step pc (by decide +kernel) first <|
          linked_step (off := 0x2f8#64) rfl (by decide +kernel) second (.refl _)
      refine ⟨2, final, steps, rfl, rfl, running, rfl, rfl, ?_⟩
      rw [ite_eq_right left, ite_eq_left done]
      exact ⟨rfl, rfl⟩
    · let s2 := s1.setPC (base + 0x2fc#64)
      have second : Step (program base) s1 s2 := by
        apply tailStep (s := s1) (off := 0x2f8#64) (inst := branchDone) rfl running loaded (by decide +kernel)
        change (if ConditionHolds .EQ s.pstate then s1.setPC (s1.pc + 0x18#64)
          else s1.advancePC) = s2
        simp [equalFlag, done, s2, s1, State.advancePC, State.setPC, BitVec.add_assoc]
      let skipped := BitVec.ofNat 64 (pivot + 1)
      let s3 := (s2.writeReg64 (.gpr 8) skipped).setPC (base + 0x300#64)
      have third : Step (program base) s2 s3 := by
        apply tailStep (s := s2) (off := 0x2fc#64) (inst := skipPivot) rfl running loaded (by decide +kernel)
        have add : BitVec.ofNat 64 pivot + 1#64 = skipped := by
          simp only [skipped, BitVec.ofNat_add]
        simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, skipPivot, s3, s2, s1,
          advancePC_eq, BitVec.add_assoc, pivotReg, add]
      let s4 := (s3.writeReg64 (.gpr 20) (s.readReg64 (.gpr 20) + (skipped <<< 3))).setPC (base + 0x304#64)
      have fourth : Step (program base) s3 s4 := by
        apply tailStep (s := s3) (off := 0x300#64) (inst := advanceBase) rfl running loaded (by decide +kernel)
        simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, advanceBase, s4, s3, s2, s1,
          advancePC_eq, BitVec.add_assoc]
      let s5 := (s4.writeReg64 .x1 (BitVec.ofNat 64 (n - (pivot + 1)))).setPC (base + 0x308#64)
      have fifth : Step (program base) s4 s5 := by
        apply tailStep (s := s4) (off := 0x304#64) (inst := reduceLength) rfl running loaded (by decide +kernel)
        have sub : BitVec.ofNat 64 n - skipped = BitVec.ofNat 64 (n - (pivot + 1)) :=
          BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
        have lengthValue : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n := lengthReg
        simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, reduceLength, s5, s4, s3, s2, s1,
          advancePC_eq, BitVec.add_assoc, lengthValue, sub]
      let s6 := (s5.writeReg64 (.gpr 19) (BitVec.ofNat 64 (k - (pivot + 1)))).setPC (base + 0x30c#64)
      have sixth : Step (program base) s5 s6 := by
        apply tailStep (s := s5) (off := 0x308#64) (inst := reduceIndex) rfl running loaded (by decide +kernel)
        have sub : BitVec.ofNat 64 k - skipped = BitVec.ofNat 64 (k - (pivot + 1)) :=
          BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
        have indexValue : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 k := indexReg
        simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, reduceIndex, s6, s5, s4, s3, s2, s1,
          advancePC_eq, BitVec.add_assoc, indexValue, sub]
      let final := s6.setPC (base + 0x1e0#64)
      have seventh : Step (program base) s6 final := by
        apply tailStep (s := s6) (off := 0x30c#64) (inst := loopBack) rfl running loaded (by decide +kernel)
        simp [Program.evalInst, execInstWithSvc, loopBack, final, s6, BitVec.add_assoc]
      have steps : CodeStepsN (program base) 7 s final :=
        linked_step pc (by decide +kernel) first <|
        linked_step (off := 0x2f8#64) rfl (by decide +kernel) second <|
        linked_step (off := 0x2fc#64) rfl (by decide +kernel) third <|
        linked_step (off := 0x300#64) rfl (by decide +kernel) fourth <|
        linked_step (off := 0x304#64) rfl (by decide +kernel) fifth <|
        linked_step (off := 0x308#64) rfl (by decide +kernel) sixth <|
        linked_step (off := 0x30c#64) rfl (by decide +kernel) seventh (.refl _)
      refine ⟨7, final, steps, rfl, rfl, running, ?_, ?_, ?_⟩
      · simp [final, s6, s5, s4, s3, s2, s1, wp_norm, arm64_norm]
      · simp [final, s6, s5, s4, s3, s2, s1, wp_norm, arm64_norm]
      rw [ite_eq_right left, ite_eq_right done]
      have nextLen : final.readReg64 .x1 = BitVec.ofNat 64 (n - (pivot + 1)) := by
        simp [wp_norm, arm64_norm, final, s6, s5]
      have nextRank : final.readReg64 (.gpr 19) = BitVec.ofNat 64 (k - (pivot + 1)) := by
        simp [wp_norm, arm64_norm, final, s6]
      refine ⟨rfl, rfl, nextLen, nextRank,
        by simp [wp_norm, arm64_norm, final, s6, s5, s4, skipped], ?_⟩
      rw [nextLen, nextRank, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : k - (pivot + 1) < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : n - (pivot + 1) < 2 ^ 64)]
      omega

private def compareRank : Instr := .addSubShift .W64 .SUBS .xzr (.gpr 19#5) .x1 .LSL 0
private def storePivot : Instr := .str .X64 (.gpr 8#5) (.Offset (.gpr 20#5) 0)
private def storeFirst : Instr := .str .X64 (.gpr 9#5) (.RegOffset (.gpr 20#5) .x1 .UXTX 3)

/-- The final comparison and stores leading into `quickselect_driver_tail`.
X8 and X9 already contain the two values loaded by the partition block. -/
theorem quickselect_partition_stores (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x2e8#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (writeStart : s.mem.canWrite (s.readReg64 (.gpr 20#5)) 8 = true)
    (writePivot : s.mem.canWrite (s.readReg64 (.gpr 20#5) + (s.readReg64 .x1 <<< 3)) 8 = true) :
    let start := s.readReg64 (.gpr 20#5)
    let pivot := start + (s.readReg64 .x1 <<< 3)
    let mem := (s.mem.write64 start (s.readReg64 (.gpr 8#5))).write64 pivot (s.readReg64 (.gpr 9#5))
    let flags := subsPState64 (s.readReg64 (.gpr 19#5)) (s.readReg64 .x1)
    let final := ((s.setPState flags).setMem mem).setPC (base + 0x2f4#64)
    CodeStepsN (program base) 3 s final ∧ (program base).CodeLoaded final.mem := by
  let start := s.readReg64 (.gpr 20#5)
  let pivot := start + (s.readReg64 .x1 <<< 3)
  let flags := subsPState64 (s.readReg64 (.gpr 19#5)) (s.readReg64 .x1)
  let m1 := s.mem.write64 start (s.readReg64 (.gpr 8#5))
  let m2 := m1.write64 pivot (s.readReg64 (.gpr 9#5))
  let s1 := (s.setPState flags).setPC (base + 0x2ec#64)
  let s2 := (s1.setMem m1).setPC (base + 0x2f0#64)
  let final := ((s.setPState flags).setMem m2).setPC (base + 0x2f4#64)
  have first : Step (program base) s s1 := by
    apply tailStep (inst := compareRank) pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, compareRank, s1, flags,
      advancePC_eq, pc, BitVec.add_assoc]
  have second : Step (program base) s1 s2 := by
    apply tailStep (s := s1) (off := 0x2ec#64) (inst := storePivot) rfl running loaded (by decide +kernel)
    have can : s1.mem.canWrite (s1.readReg64 (.gpr 20#5)) 8 = true := writeStart
    simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, storePivot, execStr, evalAddrMode,
      checkAddrSPAligned, Memory.writeSized, MemWidth.bytes, advancePC_eq, s2]
    rw [show s1.mem.canWrite (s1.readReg64 (.gpr 20#5)) 8 = true from can]
    simp only [Bool.true_eq_false, ite_false, s1, m1, start, State.pc_setPC,
      State.mem_setPC, State.mem_setPState, State.readReg64_setPC, State.readReg64_setPState,
      State.setPC_setPC, BitVec.add_assoc, BitVec.reduceAdd]
  have canPivot : m1.canWrite pivot 8 = true := by
    rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)]
    exact writePivot
  have third : Step (program base) s2 final := by
    apply tailStep (s := s2) (off := 0x2f0#64) (inst := storeFirst) rfl running
      (second.codeLoaded loaded) (by decide +kernel)
    have can : s2.mem.canWrite (s2.readReg64 (.gpr 20#5) + (s2.readReg64 .x1 <<< 3)) 8 = true := canPivot
    simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, storeFirst, execStr, evalAddrMode,
      checkAddrSPAligned, Memory.writeSized, MemWidth.bytes, extendVal, advancePC_eq]
    rw [show s2.mem.canWrite (s2.readReg64 (.gpr 20#5) + (s2.readReg64 (.gpr 1#5) <<< 3)) 8 = true from can]
    simp only [Bool.true_eq_false, ite_false, s2, s1, final, m2, pivot, start,
      State.pc_setMem, State.pc_setPC, State.mem_setMem, State.readReg64_setPC,
      State.readReg64_setMem, State.readReg64_setPState, State.setMem_setPC, State.setPC_setPC,
      State.setMem_setMem, Reg.x1, BitVec.add_assoc, BitVec.reduceAdd]
  refine ⟨?_, third.codeLoaded (second.codeLoaded loaded)⟩
  exact linked_step pc (by decide +kernel) first <|
    linked_step (off := 0x2ec#64) rfl (by decide +kernel) second <|
    linked_step (off := 0x2f0#64) rfl (by decide +kernel) third (.refl _)

private def compareLength : Instr := .addSubShift .W64 .SUBS .xzr .x1 (.gpr 21#5) .LSL 0
private def rejectPivot : Instr := .bCond .CS 0x34#64
private def loadPivot : Instr := .ldr .W64 .X64 false (.gpr 8#5) (.RegOffset (.gpr 20#5) .x1 .UXTX 3)
private def loadFirst : Instr := .ldr .W64 .X64 false (.gpr 9#5) (.Offset (.gpr 20#5) 0)

/-- For an in-range pivot index, the compiled bounds check falls through, and
two loads capture the original words before `quickselect_partition_stores`. -/
theorem quickselect_partition_loads (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x2d8#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (inRange : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 21#5)).toNat)
    (readStart : s.mem.canRead (s.readReg64 (.gpr 20#5)) 8 = true)
    (readPivot : s.mem.canRead (s.readReg64 (.gpr 20#5) + (s.readReg64 .x1 <<< 3)) 8 = true) :
    let start := s.readReg64 (.gpr 20#5)
    let pivot := start + (s.readReg64 .x1 <<< 3)
    let flags := subsPState64 (s.readReg64 .x1) (s.readReg64 (.gpr 21#5))
    let pivotLoaded := (s.setPState flags).writeReg64 (.gpr 8#5) (s.mem.read64 pivot)
    let final := (pivotLoaded.writeReg64 (.gpr 9#5) (s.mem.read64 start)).setPC (base + 0x2e8#64)
    CodeStepsN (program base) 4 s final := by
  let start := s.readReg64 (.gpr 20#5)
  let pivot := start + (s.readReg64 .x1 <<< 3)
  let flags := subsPState64 (s.readReg64 .x1) (s.readReg64 (.gpr 21#5))
  let s1 := (s.setPState flags).setPC (base + 0x2dc#64)
  let s2 := s1.setPC (base + 0x2e0#64)
  let s3 := (s2.writeReg64 (.gpr 8#5) (s.mem.read64 pivot)).setPC (base + 0x2e4#64)
  let pivotLoaded := (s.setPState flags).writeReg64 (.gpr 8#5) (s.mem.read64 pivot)
  let final := (pivotLoaded.writeReg64 (.gpr 9#5) (s.mem.read64 start)).setPC (base + 0x2e8#64)
  have first : Step (program base) s s1 := by
    apply tailStep (inst := compareLength) pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, compareLength, s1, flags,
      advancePC_eq, pc, BitVec.add_assoc]
  have second : Step (program base) s1 s2 := by
    apply tailStep (s := s1) (off := 0x2dc#64) (inst := rejectPivot) rfl running loaded (by decide +kernel)
    have keep : ConditionHolds .CS s1.pstate = false := by
      change ConditionHolds .CS (subsPState64 _ _) = false
      rw [conditionHolds_cs_subsPState64, BitVec.ule_eq_decide, decide_eq_false_iff_not]
      omega
    change (if ConditionHolds .CS s1.pstate then s1.setPC (s1.pc + 0x34#64)
      else s1.advancePC) = s2
    rw [keep]
    simp [s2, s1, advancePC_eq, BitVec.add_assoc]
  have third : Step (program base) s2 s3 := by
    apply tailStep (s := s2) (off := 0x2e0#64) (inst := loadPivot) rfl running loaded (by decide +kernel)
    have can : s2.mem.canRead (s2.readReg64 (.gpr 20#5) + (s2.readReg64 (.gpr 1#5) <<< 3)) 8 = true := readPivot
    simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, loadPivot, execLdr, evalAddrMode,
      checkAddrSPAligned, Memory.readSized, MemWidth.bytes, extendVal, advancePC_eq, can,
      show s2.pc = base + 0x2e0#64 from rfl, BitVec.add_assoc]
    simp only [s3, s2, s1, pivot, start, State.mem_setPC, State.mem_setPState,
      State.readReg64_setPC, State.readReg64_setPState, Reg.x1]
  have fourth : Step (program base) s3 final := by
    apply tailStep (s := s3) (off := 0x2e4#64) (inst := loadFirst) rfl running loaded (by decide +kernel)
    have sameBase : s3.readReg64 (.gpr 20#5) = start := by
      simp [wp_norm, arm64_norm, s3, s2, s1, start]
    have can : s3.mem.canRead (s3.readReg64 (.gpr 20#5)) 8 = true := by
      rw [sameBase]
      exact readStart
    simp [wp_norm, arm64_norm, Program.evalInst, execInstWithSvc, loadFirst, execLdr, evalAddrMode,
      checkAddrSPAligned, Memory.readSized, MemWidth.bytes, advancePC_eq, can,
      show s3.pc = base + 0x2e4#64 from rfl, BitVec.add_assoc]
    rw [sameBase]
    simp only [s3, s2, s1, final, pivotLoaded, State.mem_setPC, State.mem_writeReg64,
      State.mem_setPState, State.writeReg64_setPC, State.setPC_setPC]
  exact linked_step pc (by decide +kernel) first <|
    linked_step (off := 0x2dc#64) rfl (by decide +kernel) second <|
    linked_step (off := 0x2e0#64) rfl (by decide +kernel) third <|
    linked_step (off := 0x2e4#64) rfl (by decide +kernel) fourth (.refl _)

end Example04Rust
