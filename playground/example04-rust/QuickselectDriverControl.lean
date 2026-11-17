import QuickselectBounds

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false
set_option maxRecDepth 4000

/-- A decoded instruction at an offset in the linked image, with its evaluated effect. -/
theorem driver_step {base off : BitVec 64} {s t : State} {inst : Instr}
    (pc : s.pc = base + off) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (fetch : (program 0).fetch off = some inst)
    (effect : (program base).evalInst inst s = t) : Step (program base) s t :=
  effect ▸ execute_at base off inst s pc running loaded fetch

/-- The first rank check falls through to the stack prologue on valid calls. -/
theorem driver_check_rank (base : BitVec 64) (s : State)
    (pc : s.pc = entry base) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (rank : (s.readReg64 .x2).toNat < (s.readReg64 .x1).toNat) :
    let cmp := s.setPState (subsPState64 (s.readReg64 .x2) (s.readReg64 .x1))
    CodeStepsN (program base) 2 s (cmp.setPC (base + 0x1b4#64)) := by
  let cmp := s.setPState (subsPState64 (s.readReg64 .x2) (s.readReg64 .x1))
  let s1 := cmp.setPC (base + 0x1b0#64)
  have first : Step (program base) s s1 := by
    apply driver_step (inst := .addSubShift .W64 .SUBS .xzr .x2 .x1 .LSL 0)
      (show s.pc = base + 0x1ac#64 from pc) running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, pc, entry, entryOffset, cmp, s1, BitVec.add_assoc]
  have second : Step (program base) s1 (cmp.setPC (base + 0x1b4#64)) := by
    apply driver_step (inst := .bCond .CS 0x170#64) (s := s1) (off := 0x1b0#64)
      rfl running loaded (by decide +kernel)
    have takeBranch : ConditionHolds .CS s1.pstate = false := by
      change ConditionHolds .CS (subsPState64 (s.readReg64 .x2) (s.readReg64 .x1)) = false
      rw [conditionHolds_cs_subsPState64, BitVec.ule_eq_decide, decide_eq_false_iff_not]
      omega
    change (if ConditionHolds .CS s1.pstate then s1.setPC (s1.pc + 0x170#64)
      else s1.advancePC) = cmp.setPC (base + 0x1b4#64)
    rw [takeBranch]
    simp [wp_norm, arm64_norm, s1, BitVec.add_assoc]
  exact linked_step (show s.pc = base + 0x1ac#64 from pc) (by decide +kernel) first <|
    linked_step (off := 0x1b0#64) rfl (by decide +kernel) second (.refl _)

/-- Right continuations reach the ordinary loop header through a single
instruction that resets the pointer to the first non-pivot word. -/
theorem driver_right_header (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x1e0#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) :
    let final := (s.writeReg64 (.gpr 23#5) (s.readReg64 (.gpr 20#5) + 8#64)).setPC (base + 0x1e4#64)
    CodeStepsN (program base) 1 s final := by
  dsimp only
  refine linked_step pc (by decide +kernel) ?_ (.refl _)
  apply driver_step (inst := .addSubImm .W64 .ADD (.gpr 23#5) (.gpr 20#5) 8#12 false)
    pc running loaded (by decide +kernel)
  simp [wp_norm, arm64_norm, pc, BitVec.add_assoc]

/-- Read the active length at the loop header and dispatch to the recursive
pivot helper for lengths at least nine. The length is copied into X21. -/
theorem driver_header_large (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x1e4#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) (large : 9 ≤ (s.readReg64 .x1).toNat) :
    let copied := s.writeReg64 (.gpr 21#5) (s.readReg64 .x1)
    let final := (copied.setPState (subsPState64 (s.readReg64 .x1) 9#64)).setPC (base + 0x200#64)
    CodeStepsN (program base) 3 s final := by
  let copied := s.writeReg64 (.gpr 21#5) (s.readReg64 .x1)
  let compared := copied.setPState (subsPState64 (s.readReg64 .x1) 9#64)
  let s1 := copied.setPC (base + 0x1e8#64)
  let s2 := compared.setPC (base + 0x1ec#64)
  have first : Step (program base) s s1 := by
    apply driver_step (inst := .logicalShift .W64 .ORR (.gpr 21#5) .xzr .x1 .LSL 0)
      pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, pc, copied, s1, BitVec.add_assoc]
  have second : Step (program base) s1 s2 := by
    apply driver_step (inst := .addSubImm .W64 .SUBS .xzr .x1 9#12 false)
      (s := s1) (off := 0x1e8#64) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, s1, s2, copied, compared, BitVec.add_assoc]
  have takeBranch : ConditionHolds .CS s2.pstate = true := by
    change ConditionHolds .CS (subsPState64 (s.readReg64 .x1) 9#64) = true
    rw [conditionHolds_cs_subsPState64, BitVec.ule_iff_toNat_le]
    exact large
  have third : Step (program base) s2 (compared.setPC (base + 0x200#64)) := by
    apply driver_step (inst := .bCond .CS 0x14#64) (s := s2) (off := 0x1ec#64)
      rfl running loaded (by decide +kernel)
    change (if ConditionHolds .CS s2.pstate then s2.setPC (s2.pc + 0x14#64)
      else s2.advancePC) = compared.setPC (base + 0x200#64)
    rw [takeBranch]
    simp [wp_norm, arm64_norm, s2, BitVec.add_assoc]
  exact linked_step pc (by decide +kernel) first <|
    linked_step (off := 0x1e8#64) rfl (by decide +kernel) second <|
    linked_step (off := 0x1ec#64) rfl (by decide +kernel) third (.refl _)

/-- A valid small active slice uses its first element as pivot. These six
instructions enter the partition with X8 equal to zero. -/
theorem driver_header_small (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x1e4#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (positive : 0 < (s.readReg64 .x1).toNat) (small : (s.readReg64 .x1).toNat < 9) :
    let copied := s.writeReg64 (.gpr 21#5) (s.readReg64 .x1)
    let zeroed := copied.writeReg64 (.gpr 8#5) 0#64
    let final := (zeroed.setPState (subsPState64 0#64 (s.readReg64 .x1))).setPC (base + 0x234#64)
    CodeStepsN (program base) 6 s final := by
  let copied := s.writeReg64 (.gpr 21#5) (s.readReg64 .x1)
  let compared := copied.setPState (subsPState64 (s.readReg64 .x1) 9#64)
  let zeroed := copied.writeReg64 (.gpr 8#5) 0#64
  let final := (zeroed.setPState (subsPState64 0#64 (s.readReg64 .x1))).setPC (base + 0x234#64)
  let s1 := copied.setPC (base + 0x1e8#64)
  let s2 := compared.setPC (base + 0x1ec#64)
  let s3 := compared.setPC (base + 0x1f0#64)
  let s4 := ((compared.writeReg64 (.gpr 8#5) 0#64)).setPC (base + 0x1f4#64)
  let s5 := (zeroed.setPState (subsPState64 0#64 (s.readReg64 .x1))).setPC (base + 0x1f8#64)
  have first : Step (program base) s s1 := by
    apply driver_step (inst := .logicalShift .W64 .ORR (.gpr 21#5) .xzr .x1 .LSL 0)
      pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, pc, copied, s1, BitVec.add_assoc]
  have second : Step (program base) s1 s2 := by
    apply driver_step (inst := .addSubImm .W64 .SUBS .xzr .x1 9#12 false)
      (s := s1) (off := 0x1e8#64) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, s1, s2, copied, compared, BitVec.add_assoc]
  have below : ConditionHolds .CS s2.pstate = false := by
    change ConditionHolds .CS (subsPState64 (s.readReg64 .x1) 9#64) = false
    rw [conditionHolds_cs_subsPState64, BitVec.ule_eq_decide, decide_eq_false_iff_not]
    exact Nat.not_le_of_gt small
  have third : Step (program base) s2 s3 := by
    apply driver_step (inst := .bCond .CS 0x14#64) (s := s2) (off := 0x1ec#64)
      rfl running loaded (by decide +kernel)
    change (if ConditionHolds .CS s2.pstate then s2.setPC (s2.pc + 0x14#64)
      else s2.advancePC) = s3
    rw [below]
    simp [wp_norm, arm64_norm, s2, s3, BitVec.add_assoc]
  have fourth : Step (program base) s3 s4 := by
    apply driver_step (inst := .logicalShift .W64 .ORR (.gpr 8#5) .xzr .xzr .LSL 0)
      (s := s3) (off := 0x1f0#64) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, s3, s4, BitVec.add_assoc]
  have fifth : Step (program base) s4 s5 := by
    apply driver_step (inst := .addSubShift .W64 .SUBS .xzr .xzr (.gpr 21#5) .LSL 0)
      (s := s4) (off := 0x1f4#64) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, s4, s5, zeroed, compared, copied, BitVec.add_assoc]
  have nonzero : ConditionHolds .CC s5.pstate = true := by
    change ConditionHolds .CC (subsPState64 0#64 (s.readReg64 .x1)) = true
    rw [subsPState64, conditionHolds_cc_subs64, BitVec.ult_eq_decide, decide_eq_true_eq]
    exact positive
  have sixth : Step (program base) s5 final := by
    apply driver_step (inst := .bCond .CC 0x3c#64) (s := s5) (off := 0x1f8#64)
      rfl running loaded (by decide +kernel)
    change (if ConditionHolds .CC s5.pstate then s5.setPC (s5.pc + 0x3c#64)
      else s5.advancePC) = final
    rw [nonzero]
    simp [wp_norm, arm64_norm, s5, final, BitVec.add_assoc]
  exact linked_step pc (by decide +kernel) first <|
    linked_step (off := 0x1e8#64) rfl (by decide +kernel) second <|
    linked_step (off := 0x1ec#64) rfl (by decide +kernel) third <|
    linked_step (off := 0x1f0#64) rfl (by decide +kernel) fourth <|
    linked_step (off := 0x1f4#64) rfl (by decide +kernel) fifth <|
    linked_step (off := 0x1f8#64) rfl (by decide +kernel) sixth (.refl _)

/-- The helper returned Some and its index fits. The driver's two bounds
checks succeed and its result index is copied into X8 for partitioning. -/
theorem driver_accept_pivot (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x220#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) (someTag : s.readReg64 .x0 = 1#64)
    (fits : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 21#5)).toNat) :
    let copied := s.writeReg64 (.gpr 8#5) (s.readReg64 .x1)
    let final := (copied.setPState (subsPState64 (s.readReg64 .x1)
      (s.readReg64 (.gpr 21#5)))).setPC (base + 0x234#64)
    CodeStepsN (program base) 5 s final := by
  let cmpTag := s.setPState (subsPState64 (s.readReg64 .x0) 1#64)
  let s1 := cmpTag.setPC (base + 0x224#64)
  let s2 := cmpTag.setPC (base + 0x228#64)
  let s3 := (cmpTag.writeReg64 (.gpr 8#5) (s.readReg64 .x1)).setPC (base + 0x22c#64)
  let copied := s.writeReg64 (.gpr 8#5) (s.readReg64 .x1)
  let cmp := copied.setPState (subsPState64 (s.readReg64 .x1) (s.readReg64 (.gpr 21#5)))
  let s4 := cmp.setPC (base + 0x230#64)
  let final := cmp.setPC (base + 0x234#64)
  have first : Step (program base) s s1 := by
    apply driver_step (inst := .addSubImm .W64 .SUBS .xzr .x0 1#12 false)
      pc running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, pc, cmpTag, s1, BitVec.add_assoc]
  have validTag : ConditionHolds .NE s1.pstate = false := by
    change ConditionHolds .NE (subsPState64 (s.readReg64 .x0) 1#64) = false
    rw [subsPState64, conditionHolds_ne_subs64, someTag]
    rfl
  have second : Step (program base) s1 s2 := by
    apply driver_step (inst := .bCond .NE 0xec#64) (s := s1) (off := 0x224#64)
      rfl running loaded (by decide +kernel)
    change (if ConditionHolds .NE s1.pstate then s1.setPC (s1.pc + 0xec#64)
      else s1.advancePC) = s2
    rw [validTag]
    simp [wp_norm, arm64_norm, s1, s2, BitVec.add_assoc]
  have third : Step (program base) s2 s3 := by
    apply driver_step (inst := .logicalShift .W64 .ORR (.gpr 8#5) .xzr .x1 .LSL 0)
      (s := s2) (off := 0x228#64) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, s2, s3, cmpTag, BitVec.add_assoc]
  have fourth : Step (program base) s3 s4 := by
    apply driver_step (inst := .addSubShift .W64 .SUBS .xzr .x1 (.gpr 21#5) .LSL 0)
      (s := s3) (off := 0x22c#64) rfl running loaded (by decide +kernel)
    simp [wp_norm, arm64_norm, s3, s4, cmp, copied, cmpTag, BitVec.add_assoc]
  have inRange : ConditionHolds .CS s4.pstate = false := by
    change ConditionHolds .CS (subsPState64 (s.readReg64 .x1) (s.readReg64 (.gpr 21#5))) = false
    rw [conditionHolds_cs_subsPState64, BitVec.ule_eq_decide, decide_eq_false_iff_not]
    exact Nat.not_le_of_gt fits
  have fifth : Step (program base) s4 final := by
    apply driver_step (inst := .bCond .CS 0xe0#64) (s := s4) (off := 0x230#64)
      rfl running loaded (by decide +kernel)
    change (if ConditionHolds .CS s4.pstate then s4.setPC (s4.pc + 0xe0#64)
      else s4.advancePC) = final
    rw [inRange]
    simp [wp_norm, arm64_norm, s4, final, BitVec.add_assoc]
  exact linked_step pc (by decide +kernel) first <|
    linked_step (off := 0x224#64) rfl (by decide +kernel) second <|
    linked_step (off := 0x228#64) rfl (by decide +kernel) third <|
    linked_step (off := 0x22c#64) rfl (by decide +kernel) fourth <|
    linked_step (off := 0x230#64) rfl (by decide +kernel) fifth (.refl _)

end Example04Rust
