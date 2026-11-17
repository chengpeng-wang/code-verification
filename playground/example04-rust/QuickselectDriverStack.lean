import CountedExecution
import QuickselectDriverControl

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The driver saves seven registers in a 64-byte frame. The unused slot is
owned as well, so the pivot helper can frame out the entire caller frame. -/
def savedDriverFrame (entryState : State) : SepProp :=
  ∃∗ pad : BitVec 64,
    ((entryState.sp - 64#64) ↦₆₄ entryState.readReg64 (.gpr 29#5)) ∗
    ((entryState.sp - 56#64) ↦₆₄ entryState.readReg64 .lr) ∗
    ((entryState.sp - 48#64) ↦₆₄ entryState.readReg64 (.gpr 23#5)) ∗
    ((entryState.sp - 40#64) ↦₆₄ pad) ∗
    ((entryState.sp - 32#64) ↦₆₄ entryState.readReg64 (.gpr 22#5)) ∗
    ((entryState.sp - 24#64) ↦₆₄ entryState.readReg64 (.gpr 21#5)) ∗
    ((entryState.sp - 16#64) ↦₆₄ entryState.readReg64 (.gpr 20#5)) ∗
    ((entryState.sp - 8#64) ↦₆₄ entryState.readReg64 (.gpr 19#5))

private def driverPushWords : List (BitVec 32) :=
  [0xa9bc7bfd#32, 0xf9000bf7#32, 0xa90257f6#32, 0xa9034ff4#32]

private def driverPopWords : List (BitVec 32) :=
  [0xa9434ff4#32, 0xf9400bf7#32, 0xa94257f6#32, 0xa8c47bfd#32, 0xd65f03c0#32]

private theorem pushWordsAt (base : BitVec 64) :
    (program base).hasWords (base + 0x1b4#64) driverPushWords := by
  unfold Program.hasWords
  rw [show (program base).base = base from rfl, BitVec.add_comm base, BitVec.add_sub_cancel]
  change (program 0#64).hasWordsOff 0x1b4 driverPushWords
  decide +kernel

private theorem popWordsAt (base : BitVec 64) :
    (program base).hasWords (base + 0x310#64) driverPopWords := by
  unfold Program.hasWords
  rw [show (program base).base = base from rfl, BitVec.add_comm base, BitVec.add_sub_cancel]
  change (program 0#64).hasWordsOff 0x310 driverPopWords
  decide +kernel

/-- The four driver stores save the caller registers and allocate the frame.
The frame rule leaves ownership of the array and the rest of the stack intact. -/
theorem driver_save_stack (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x1b4#64) (running : s.status = .Running)
    (aligned : s.spAligned = true) :
    CountedWP (program base) (base + 0x1c4#64) s (stackAt s.sp 64)
      (fun count final P => count = 4 ∧ final.sp = s.sp - 64#64 ∧
        final.readReg64 .x0 = s.readReg64 .x0 ∧ final.readReg64 .x1 = s.readReg64 .x1 ∧
        final.readReg64 .x2 = s.readReg64 .x2 ∧
        P ⊢ savedDriverFrame s) := by
  have code := pushWordsAt base
  have hf0 := Program.fetch_of_hasWords code 0 (by decide)
  have hf1 := Program.fetch_of_hasWords code 1 (by decide)
  have hf2 := Program.fetch_of_hasWords code 2 (by decide)
  have hf3 := Program.fetch_of_hasWords code 3 (by decide)
  have newAligned := s.spAligned_sub 64#64 aligned
  conv =>
    arg 4
    rw [show 64 = 8 * 8 by decide, stackAt_eq_cells s.sp 8 (by decide)]
    simp (disch := decide) only [cells_sub_succ, Nat.reduceSub, Nat.reduceMul, cells_zero, sepConj_emp,
      sepExists_sepConj_right]
  iterate 8 (apply CountedWP.exists_elim; intro)
  cost_steps 4
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine ⟨rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_⟩
  unfold savedDriverFrame
  apply Entails.sepExists_right
  exact Entails.refl _

/-- The epilogue loads the saved registers and returns to the original LR in
five instructions, with the original stack pointer restored. -/
theorem driver_restore_stack (base : BitVec 64) (initial s : State)
    (pc : s.pc = base + 0x310#64) (running : s.status = .Running)
    (aligned : s.spAligned = true) (spEq : s.sp = initial.sp - 64#64) :
    CountedWP (program base) (initial.readReg64 .lr) s (savedDriverFrame initial)
      (fun count final _ => count = 5 ∧ Returned initial final) := by
  have code := popWordsAt base
  have hf0 := Program.fetch_of_hasWords code 0 (by decide)
  have hf1 := Program.fetch_of_hasWords code 1 (by decide)
  have hf2 := Program.fetch_of_hasWords code 2 (by decide)
  have hf3 := Program.fetch_of_hasWords code 3 (by decide)
  have hf4 := Program.fetch_of_hasWords code 4 (by decide)
  conv => arg 4; unfold savedDriverFrame
  apply CountedWP.exists_elim
  intro pad
  cost_steps 5
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine ⟨rfl, by wp_norm_lhs, ?_, by wp_norm_lhs⟩
  simp [wp_norm, arm64_norm]

private def driverInitWords : List (BitVec 32) :=
  [0x910003fd#32, 0xd29c71f6#32, 0xaa0203f3#32, 0xaa0003f4#32,
    0xf2b1c716#32, 0xf2c71c76#32, 0xf2fc71d6#32, 0x91002297#32]

private theorem initWordsAt (base : BitVec 64) :
    (program base).hasWords (base + 0x1c4#64) driverInitWords := by
  unfold Program.hasWords
  rw [show (program base).base = base from rfl, BitVec.add_comm base, BitVec.add_sub_cancel]
  change (program 0#64).hasWordsOff 0x1c4 driverInitWords
  decide +kernel

/-- The eight instructions after the frame stores initialize the working
registers, including the reciprocal constant used by the pivot dispatch. -/
theorem driver_initialize (base : BitVec 64) (s : State) (owned : SepProp)
    (pc : s.pc = base + 0x1c4#64) (running : s.status = .Running) :
    CountedWP (program base) (base + 0x1e4#64) s owned
      (fun count final P => count = 8 ∧ final.sp = s.sp ∧ final.mem = s.mem ∧
        final.readReg64 (.gpr 19#5) = s.readReg64 .x2 ∧
        final.readReg64 (.gpr 20#5) = s.readReg64 .x0 ∧
        final.readReg64 (.gpr 22#5) = 0xe38e38e38e38e38f#64 ∧
        final.readReg64 (.gpr 23#5) = s.readReg64 .x0 + 8#64 ∧
        final.readReg64 .x1 = s.readReg64 .x1 ∧ P = owned) := by
  have code := initWordsAt base
  have hf0 := Program.fetch_of_hasWords code 0 (by decide)
  have hf1 := Program.fetch_of_hasWords code 1 (by decide)
  have hf2 := Program.fetch_of_hasWords code 2 (by decide)
  have hf3 := Program.fetch_of_hasWords code 3 (by decide)
  have hf4 := Program.fetch_of_hasWords code 4 (by decide)
  have hf5 := Program.fetch_of_hasWords code 5 (by decide)
  have hf6 := Program.fetch_of_hasWords code 6 (by decide)
  have hf7 := Program.fetch_of_hasWords code 7 (by decide)
  cost_steps 8
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine ⟨rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, rfl⟩

end Example04Rust
