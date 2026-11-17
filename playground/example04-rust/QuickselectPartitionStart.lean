import QuickselectArray
import QuickselectDriverControl

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private def startLoadPivot : Instr := .ldr .W64 .X64 false (.gpr 9#5)
  (.RegOffset (.gpr 20#5) (.gpr 8#5) .UXTX 3)
private def startLoadFirst : Instr := .ldr .W64 .X64 false (.gpr 10#5) (.Offset (.gpr 20#5) 0#64)
private def startStorePivot : Instr := .str .X64 (.gpr 9#5) (.Offset (.gpr 20#5) 0#64)
private def startStoreFirst : Instr := .str .X64 (.gpr 10#5)
  (.RegOffset (.gpr 20#5) (.gpr 8#5) .UXTX 3)

/-- The compiled partition starts by moving the selected pivot to array slot
zero, sets the cursors to zero and n−1, and goes to the left scan when the
interval is nonempty. The two stores preserve any disjoint frame. -/
theorem partition_start (base : BitVec 64) (s : State) (xs : List (BitVec 64)) (p : Nat) (frame : SepProp)
    (pc : s.pc = base + 0x234#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (index : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 p)
    (length : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 xs.length)
    (size : xs.length < 2 ^ 64) (fits : p < xs.length)
    (owned : s.mem ⊨ (s.readReg64 (.gpr 20#5) ↦₆₄* xs) ∗ frame) :
    ∃ t, CodeStepsN (program base) 9 s t ∧ t.status = .Running ∧
      t.sp = s.sp ∧ (program base).CodeLoaded t.mem ∧
      CalleeSavedPreserved s t ∧ t.readReg64 .lr = s.readReg64 .lr ∧
      t.readReg64 .x1 = 0#64 ∧
      t.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (xs.length - 1) ∧
      t.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (xs.length - 1) ∧
      t.pc = base + (if xs.length = 1 then 0x28c#64 else 0x258#64) ∧
      t.mem ⊨ (s.readReg64 (.gpr 20#5) ↦₆₄* swapWords xs 0 p) ∗ frame := by
  let data := s.readReg64 (.gpr 20#5)
  let pivotAddr := wordAddr data p
  let oldPivot := s.mem.read64 pivotAddr
  let oldFirst := s.mem.read64 data
  let m1 := s.mem.write64 data oldPivot
  let m2 := m1.write64 pivotAddr oldFirst
  let limit := BitVec.ofNat 64 (xs.length - 1)
  have atFirst := word_at owned (i := 0) (by omega)
  rw [wordAddr_zero] at atFirst
  have atPivot := word_at owned fits
  have physical : data + (s.readReg64 (.gpr 8#5) <<< 3) = pivotAddr := by
    rw [← wordAddr_shift, index, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]
  have can1 : m1.canWrite pivotAddr 8 = true := by
    rw [Memory.canWrite_congr (Memory.perm_write64 ..)]
    exact atPivot.2.2
  have loaded1 := loaded.of_keepsFrozen (Memory.keepsFrozen_write64 atFirst.2.2 oldPivot)
  have loaded2 := loaded1.of_keepsFrozen (Memory.keepsFrozen_write64 can1 oldFirst)
  let s1 := (s.writeReg64 (.gpr 9#5) oldPivot).setPC (base + 0x238#64)
  let s2 := (s1.writeReg64 (.gpr 10#5) oldFirst).setPC (base + 0x23c#64)
  let s3 := (s2.writeReg64 .x1 0#64).setPC (base + 0x240#64)
  let s4 := (s3.setMem m1).setPC (base + 0x244#64)
  let s5 := (s4.writeReg64 (.gpr 9#5) limit).setPC (base + 0x248#64)
  let s6 := (s5.setMem m2).setPC (base + 0x24c#64)
  let s7 := (s6.writeReg64 (.gpr 8#5) limit).setPC (base + 0x250#64)
  let s8 := (s7.setPState (subsPState64 0#64 limit)).setPC (base + 0x254#64)
  have first : Step (program base) s s1 := by
    apply driver_step (inst := startLoadPivot) pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, startLoadPivot, pc, s1, oldPivot, BitVec.add_assoc]
    rw [show s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 8#5) <<< 3) = pivotAddr from physical,
      atPivot.2.1]
    rfl
  have second : Step (program base) s1 s2 := by
    apply driver_step (inst := startLoadFirst) (s := s1) (off := 0x238#64)
      rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, startLoadFirst, s1, s2, oldFirst, data, atFirst.2.1, BitVec.add_assoc]
  have third : Step (program base) s2 s3 := by
    apply driver_step (inst := .logicalShift .W64 .ORR .x1 .xzr .xzr .LSL 0) (s := s2)
      (off := 0x23c#64) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, s2, s3, BitVec.add_assoc]
  have fourth : Step (program base) s3 s4 := by
    apply driver_step (inst := startStorePivot) (s := s3) (off := 0x240#64)
      rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, startStorePivot, s1, s2, s3, s4, m1, data, atFirst.2.2, BitVec.add_assoc]
  have subtract : BitVec.ofNat 64 xs.length - 1#64 = limit := by
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  have fifth : Step (program base) s4 s5 := by
    apply driver_step (inst := .addSubImm .W64 .SUB (.gpr 9#5) (.gpr 21#5) 1#12 false)
      (s := s4) (off := 0x244#64) rfl running loaded1 (by decide +kernel)
    simp [wp_norm, arm64_norm, s1, s2, s3, s4, s5, length, subtract, BitVec.add_assoc]
  have sixth : Step (program base) s5 s6 := by
    apply driver_step (inst := startStoreFirst) (s := s5) (off := 0x248#64)
      rfl running loaded1 (by decide +kernel)
    simp [wp_norm, arm64_norm, startStoreFirst, s1, s2, s3, s4, s5, s6, m2, BitVec.add_assoc]
    rw [show s.readReg64 (.gpr 20#5) + (s.readReg64 (.gpr 8#5) <<< 3) = pivotAddr from physical, can1]
    rfl
  have seventh : Step (program base) s6 s7 := by
    apply driver_step (inst := .addSubImm .W64 .SUB (.gpr 8#5) (.gpr 21#5) 1#12 false)
      (s := s6) (off := 0x24c#64) rfl running loaded2 (by decide +kernel)
    simp [wp_norm, arm64_norm, s1, s2, s3, s4, s5, s6, s7, length, subtract, BitVec.add_assoc]
  have eighth : Step (program base) s7 s8 := by
    apply driver_step (inst := .addSubShift .W64 .SUBS .xzr .xzr (.gpr 9#5) .LSL 0)
      (s := s7) (off := 0x250#64) rfl running loaded2 (by decide +kernel)
    simp [wp_norm, arm64_norm, s5, s6, s7, s8, BitVec.add_assoc]
  let dest := base + (if xs.length = 1 then 0x28c#64 else 0x258#64)
  let final := s8.setPC dest
  have ninth : Step (program base) s8 final := by
    apply driver_step (inst := .bCond .CS 0x38#64) (s := s8) (off := 0x254#64)
      rfl running loaded2 (by decide +kernel)
    change (if ConditionHolds .CS (subsPState64 0#64 limit) then s8.setPC (s8.pc + 0x38#64)
      else s8.advancePC) = final
    have cond : ConditionHolds .CS (subsPState64 0#64 limit) = decide (xs.length = 1) := by
      rw [conditionHolds_cs_subsPState64, BitVec.ule_eq_decide]
      simp only [limit, BitVec.toNat_ofNat, Nat.zero_mod]
      rw [Nat.mod_eq_of_lt (by omega : xs.length - 1 < 2 ^ 64)]
      have test : xs.length - 1 ≤ 0 ↔ xs.length = 1 := by omega
      simp [test]
    rw [cond]
    by_cases one : xs.length = 1 <;> simp [one, final, dest, s8, wp_norm, arm64_norm, BitVec.add_assoc]
  have exchange : final.mem ⊨ (data ↦₆₄* swapWords xs 0 p) ∗ frame := by
    change m2 ⊨ (data ↦₆₄* swapWords xs 0 p) ∗ frame
    simpa only [wordAddr_zero] using swap_words owned (i := 0) (j := p) (by omega) fits
  have steps : CodeStepsN (program base) 9 s final :=
    linked_step pc (by decide +kernel) first <|
    linked_step (off := 0x238#64) rfl (by decide +kernel) second <|
    linked_step (off := 0x23c#64) rfl (by decide +kernel) third <|
    linked_step (off := 0x240#64) rfl (by decide +kernel) fourth <|
    linked_step (off := 0x244#64) rfl (by decide +kernel) fifth <|
    linked_step (off := 0x248#64) rfl (by decide +kernel) sixth <|
    linked_step (off := 0x24c#64) rfl (by decide +kernel) seventh <|
    linked_step (off := 0x250#64) rfl (by decide +kernel) eighth <|
    linked_step (off := 0x254#64) rfl (by decide +kernel) ninth (.refl _)
  refine ⟨final, steps, running, rfl, loaded2, ?_, ?_, ?_, ?_, ?_, rfl, exchange⟩
  all_goals simp [CalleeSavedPreserved, wp_norm, arm64_norm, final, s1, s2, s3, s4, s5, s6, s7, s8, limit]

end Example04Rust
