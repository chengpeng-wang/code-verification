import QuickselectBounds

open Arm64 ProofLib Example03C

namespace Example04Rust

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

private theorem swapStep {base off : BitVec 64} {s t : State} {inst : Instr}
    (pc : s.pc = base + off) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (fetch : (program 0).fetch off = some inst)
    (effect : (program base).evalInst inst s = t) : Step (program base) s t := by
  rw [← effect]
  exact execute_at base off inst s pc running loaded fetch

private def rightBase : Instr := .addSubShift .W64 .ADD (.gpr 9) (.gpr 20) (.gpr 10) .LSL 3
private def leftSlot : AddrMode := .RegOffset (.gpr 23) .x1 .UXTX 3
private def loadLeft : Instr := .ldr .W64 .X64 false (.gpr 12) leftSlot
private def storeLeft : Instr := .str .X64 (.gpr 11) leftSlot
private def increment : Instr := .addSubImm .W64 .ADD .x1 .x1 1#12 false
private def storeRight : Instr := .str .X64 (.gpr 12) (.Offset (.gpr 9) 8#64)
private def copyRight : Instr := .logicalShift .W64 .ORR (.gpr 9) .xzr (.gpr 10) .LSL 0
private def compareCursors : Instr := .addSubShift .W64 .SUBS .xzr .x1 (.gpr 10) .LSL 0
private def crossedBranch : Instr := .bCond .CS (-(0x44#64))
private def continueBranch : Instr := .b (-(0x7c#64))

private theorem swapStores (base : BitVec 64) (s : State) (left right : BitVec 64)
    (pc : s.pc = base + 0x2b4#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (leftAddr : left = s.readReg64 (.gpr 23#5) + (s.readReg64 (.gpr 1#5) <<< (3 : Nat)))
    (rightAddr : right = s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 10#5) <<< (3 : Nat)) + 8#64)
    (readLeft : s.mem.canRead left 8 = true)
    (writeLeft : s.mem.canWrite left 8 = true) (writeRight : s.mem.canWrite right 8 = true)
    (rightValue : s.readReg64 (.gpr 11#5) = s.mem.read64 right) :
    ∃ mid, CodeStepsN (program base) 5 s mid ∧ mid.pc = base + 0x2c8#64 ∧
      mid.status = .Running ∧ mid.sp = s.sp ∧ PartitionRegs s mid ∧ (program base).CodeLoaded mid.mem ∧
      mid.mem = (s.mem.write64 left (s.mem.read64 right)).write64 right (s.mem.read64 left) ∧
      mid.readReg64 .x1 = s.readReg64 .x1 + 1#64 ∧
      mid.readReg64 (.gpr 10) = s.readReg64 (.gpr 10) ∧
      mid.readReg64 (.gpr 8) = s.readReg64 (.gpr 8) ∧
      mid.readReg64 (.gpr 20) = s.readReg64 (.gpr 20) ∧
      mid.readReg64 (.gpr 23) = s.readReg64 (.gpr 23) := by
  let rightBaseAddr := s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 10#5) <<< (3 : Nat))
  let nextLeft := s.readReg64 .x1 + 1#64
  let nextRight := s.readReg64 (.gpr 10)
  let m1 := s.mem.write64 left (s.mem.read64 right)
  let m2 := m1.write64 right (s.mem.read64 left)
  have loaded1 : (program base).CodeLoaded m1 := loaded.of_keepsFrozen (Memory.keepsFrozen_write64 writeLeft _)
  have writeRight1 : m1.canWrite right 8 = true := by
    simpa only [m1, Memory.canWrite_congr (Memory.perm_write64 _ _ _) right 8] using writeRight
  have loaded2 : (program base).CodeLoaded m2 := loaded1.of_keepsFrozen (Memory.keepsFrozen_write64 writeRight1 _)

  let s1 := (s.writeReg64 (.gpr 9) rightBaseAddr).setPC (base + 0x2b8#64)
  have first : Step (program base) s s1 := by
    apply swapStep (inst := rightBase) pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, rightBase, rightBaseAddr, s1, pc, BitVec.add_assoc]
  let s2 := (s1.writeReg64 (.gpr 12) (s.mem.read64 left)).setPC (base + 0x2bc#64)
  have second : Step (program base) s1 s2 := by
    apply swapStep (s := s1) (off := 0x2b8#64) (inst := loadLeft) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, loadLeft, leftSlot, s2, s1, BitVec.add_assoc]
    rw [← leftAddr, readLeft] <;> rfl
  let s3 := (s2.setMem m1).setPC (base + 0x2c0#64)
  have third : Step (program base) s2 s3 := by
    apply swapStep (s := s2) (off := 0x2bc#64) (inst := storeLeft) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, storeLeft, leftSlot, s3, s2, s1, m1, BitVec.add_assoc]
    rw [← leftAddr, writeLeft, rightValue] <;> rfl
  let s4 := (s3.writeReg64 .x1 nextLeft).setPC (base + 0x2c4#64)
  have fourth : Step (program base) s3 s4 := by
    apply swapStep (s := s3) (off := 0x2c0#64) (inst := increment) rfl running loaded1 (by decide +kernel)
    simp [wp_norm, arm64_norm, increment, s4, s3, s2, s1, nextLeft, BitVec.add_assoc]
  let s5 := (s4.setMem m2).setPC (base + 0x2c8#64)
  have fifth : Step (program base) s4 s5 := by
    apply swapStep (s := s4) (off := 0x2c4#64) (inst := storeRight) rfl running loaded1 (by decide +kernel)
    simp [wp_norm, arm64_norm, storeRight, s5, s4, s3, s2, s1, rightBaseAddr, m2, BitVec.add_assoc]
    rw [← BitVec.add_assoc, ← rightAddr, writeRight1] <;> rfl
  refine ⟨s5, ?_, rfl, running, rfl, ?_, loaded2, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact linked_step pc (by decide +kernel) first
      (linked_step (off := 0x2b8#64) rfl (by decide +kernel) second
      (linked_step (off := 0x2bc#64) rfl (by decide +kernel) third
      (linked_step (off := 0x2c0#64) rfl (by decide +kernel) fourth
      (linked_step (off := 0x2c4#64) rfl (by decide +kernel) fifth (.refl _)))))
  · simp [wp_norm, arm64_norm, s5, s4, s3, s2, s1, PartitionRegs, CalleeSavedPreserved]
  · simp [wp_norm, arm64_norm, s5, s4, nextLeft]
  all_goals simp [wp_norm, arm64_norm, s5, s4, s3, s2, s1]

private theorem resumeScan (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x2c8#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) :
    ∃ count final, CodeStepsN (program base) count s final ∧ final.status = .Running ∧
      final.sp = s.sp ∧ PartitionRegs s final ∧ final.mem = s.mem ∧ final.readReg64 .x1 = s.readReg64 .x1 ∧
      final.readReg64 (.gpr 9) = s.readReg64 (.gpr 10) ∧
      final.readReg64 (.gpr 10) = s.readReg64 (.gpr 10) ∧
      final.readReg64 (.gpr 8) = s.readReg64 (.gpr 8) ∧
      final.readReg64 (.gpr 20) = s.readReg64 (.gpr 20) ∧
      final.readReg64 (.gpr 23) = s.readReg64 (.gpr 23) ∧
      if BitVec.ule (s.readReg64 (.gpr 10)) (s.readReg64 .x1) then
        count = 3 ∧ final.pc = base + 0x28c#64
      else
        count = 4 ∧ final.pc = base + 0x258#64 := by
  let s1 := (s.writeReg64 (.gpr 9) (s.readReg64 (.gpr 10))).setPC (base + 0x2cc#64)
  have first : Step (program base) s s1 := by
    apply swapStep (inst := copyRight) pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, copyRight, s1, pc, BitVec.add_assoc]
  let s2 := (s1.setPState (subsPState64 (s.readReg64 .x1) (s.readReg64 (.gpr 10)))).setPC (base + 0x2d0#64)
  have second : Step (program base) s1 s2 := by
    apply swapStep (s := s1) (off := 0x2cc#64) (inst := compareCursors) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, compareCursors, s2, s1, BitVec.add_assoc]
  have leftReg : s2.readReg64 .x1 = s.readReg64 .x1 := by
    simp [wp_norm, arm64_norm, s2, s1]
  have rightReg : s2.readReg64 (.gpr 9) = s.readReg64 (.gpr 10) := by
    simp [wp_norm, arm64_norm, s2, s1]
  have rightSaved : s2.readReg64 (.gpr 10) = s.readReg64 (.gpr 10) := by
    simp [wp_norm, arm64_norm, s2, s1]
  have x8 : s2.readReg64 (.gpr 8) = s.readReg64 (.gpr 8) := by
    simp [wp_norm, arm64_norm, s2, s1]
  have x20 : s2.readReg64 (.gpr 20) = s.readReg64 (.gpr 20) := by
    simp [wp_norm, arm64_norm, s2, s1]
  have x23 : s2.readReg64 (.gpr 23) = s.readReg64 (.gpr 23) := by
    simp [wp_norm, arm64_norm, s2, s1]
  have flag : ConditionHolds .CS s2.pstate = BitVec.ule (s.readReg64 (.gpr 10)) (s.readReg64 .x1) :=
    conditionHolds_cs_subsPState64 _ _
  by_cases crossed : BitVec.ule (s.readReg64 (.gpr 10)) (s.readReg64 .x1)
  · let final := s2.setPC (base + 0x28c#64)
    have third : Step (program base) s2 final := by
      apply swapStep (s := s2) (off := 0x2d0#64) (inst := crossedBranch) rfl running loaded (by decide +kernel)
      change (if ConditionHolds .CS s2.pstate then s2.setPC (s2.pc + (-(0x44#64)))
        else s2.advancePC) = final
      rw [flag, ite_eq_left crossed]
      change s2.setPC (base + 0x2d0#64 + (-(0x44#64))) = _
      rw [BitVec.add_assoc]
      rfl
    have path : CodeStepsN (program base) 3 s final := linked_step pc (by decide +kernel) first
      (linked_step (off := 0x2cc#64) rfl (by decide +kernel) second
      (linked_step (off := 0x2d0#64) rfl (by decide +kernel) third (.refl _)))
    refine ⟨3, final, path, running, rfl, ?_, rfl,
      leftReg, rightReg, rightSaved, x8, x20, x23, ?_⟩
    · simp [final, s2, s1, wp_norm, arm64_norm, PartitionRegs, CalleeSavedPreserved]
    · rw [ite_eq_left crossed]
      exact ⟨rfl, rfl⟩
  · let s3 := s2.setPC (base + 0x2d4#64)
    have third : Step (program base) s2 s3 := by
      apply swapStep (s := s2) (off := 0x2d0#64) (inst := crossedBranch) rfl running loaded (by decide +kernel)
      change (if ConditionHolds .CS s2.pstate then s2.setPC (s2.pc + (-(0x44#64)))
        else s2.advancePC) = s3
      rw [flag, ite_eq_right crossed]
      change s2.setPC (base + 0x2d0#64 + 4#64) = _
      rw [BitVec.add_assoc]
      rfl
    let final := s3.setPC (base + 0x258#64)
    have fourth : Step (program base) s3 final := by
      apply swapStep (s := s3) (off := 0x2d4#64) (inst := continueBranch) rfl running loaded (by decide +kernel)
      change s3.setPC (base + 0x2d4#64 + (-(0x7c#64))) = _
      rw [BitVec.add_assoc]
      rfl
    have path : CodeStepsN (program base) 4 s final := linked_step pc (by decide +kernel) first
      (linked_step (off := 0x2cc#64) rfl (by decide +kernel) second
      (linked_step (off := 0x2d0#64) rfl (by decide +kernel) third
      (linked_step (off := 0x2d4#64) rfl (by decide +kernel) fourth (.refl _))))
    refine ⟨4, final, path, running, rfl, ?_, rfl, leftReg, rightReg, rightSaved, x8, x20, x23, ?_⟩
    · simp [final, s3, s2, s1, wp_norm, arm64_norm, PartitionRegs, CalleeSavedPreserved]
    · rw [ite_eq_right crossed]
      exact ⟨rfl, rfl⟩

/-- The machine block after the right scan stops. X11 holds the right value loaded by that
    scan, and X10 is the decremented right cursor. The two stores write the saved values to
    the opposite slots. The two addresses may coincide. The final comparison either
    returns to the cursor-crossing check in eight steps or to the left scan in nine. -/
theorem quickselect_swap (base : BitVec 64) (s : State) (left right : BitVec 64)
    (pc : s.pc = base + 0x2b4#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (leftAddr : left = s.readReg64 (.gpr 23#5) + (s.readReg64 (.gpr 1#5) <<< (3 : Nat)))
    (rightAddr : right = s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 10#5) <<< (3 : Nat)) + 8#64)
    (readLeft : s.mem.canRead left 8 = true)
    (writeLeft : s.mem.canWrite left 8 = true) (writeRight : s.mem.canWrite right 8 = true)
    (rightValue : s.readReg64 (.gpr 11#5) = s.mem.read64 right) :
    ∃ count final, CodeStepsN (program base) count s final ∧ final.status = .Running ∧
      final.sp = s.sp ∧ PartitionRegs s final ∧ (program base).CodeLoaded final.mem ∧
      final.mem = (s.mem.write64 left (s.mem.read64 right)).write64 right (s.mem.read64 left) ∧
      final.readReg64 .x1 = s.readReg64 .x1 + 1#64 ∧
      final.readReg64 (.gpr 9) = s.readReg64 (.gpr 10) ∧
      final.readReg64 (.gpr 10) = s.readReg64 (.gpr 10) ∧
      final.readReg64 (.gpr 8) = s.readReg64 (.gpr 8) ∧
      final.readReg64 (.gpr 20) = s.readReg64 (.gpr 20) ∧
      final.readReg64 (.gpr 23) = s.readReg64 (.gpr 23) ∧
      if BitVec.ule (s.readReg64 (.gpr 10)) (s.readReg64 .x1 + 1#64) then
        count = 8 ∧ final.pc = base + 0x28c#64
      else
        count = 9 ∧ final.pc = base + 0x258#64 := by
  obtain ⟨mid, first, midPC, midRunning, midSP, midRegs, midLoaded, midMem, midLeft, midRight,
    mid8, mid20, mid23⟩ :=
    swapStores base s left right pc running loaded leftAddr rightAddr readLeft writeLeft writeRight rightValue
  obtain ⟨count, final, last, finalRunning, finalSP, finalRegs, finalMem, finalLeft, finalRight, savedRight,
    final8, final20, final23, path⟩ := resumeScan base mid midPC midRunning midLoaded
  rw [midLeft, midRight] at path
  refine ⟨count + 5, final, by simpa only [Nat.add_comm] using first.append last, finalRunning, finalSP.trans midSP, midRegs.trans finalRegs,
    finalMem.symm ▸ midLoaded, finalMem.trans midMem, finalLeft.trans midLeft, finalRight.trans midRight,
    savedRight.trans midRight, final8.trans mid8, final20.trans mid20, final23.trans mid23, ?_⟩
  by_cases crossed : BitVec.ule (s.readReg64 (.gpr 10)) (s.readReg64 .x1 + 1#64)
  · rw [ite_eq_left crossed] at path ⊢
    exact ⟨by omega, path.2⟩
  · rw [ite_eq_right crossed] at path ⊢
    exact ⟨by omega, path.2⟩

end Example04Rust
