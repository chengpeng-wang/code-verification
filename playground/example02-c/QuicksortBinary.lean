import Arm64.Trusted.Surface.IncludeBytes
import QuicksortMachine

namespace Example02C

open Arm64 ProofLib

set_option autoImplicit false

/-- The linked .text section, rebased to the caller's entry address. It contains
    the recursive sort and the partition subroutine that it calls. -/
def program (entry : BitVec 64) : Program :=
  { base := entry, code := include_bytes% "build/quicksort_u8.bin" 0 184 }

private theorem quicksort_hasWords (entry : BitVec 64) :
    (program entry).hasWords entry quicksortWords := by
  rw [Program.hasWords, show (program entry).base = entry from rfl, BitVec.sub_self]
  change (program 0).hasWordsOff 0 quicksortWords
  decide +kernel

private theorem partition_hasWords (entry : BitVec 64) :
    (program entry).hasWords (entry + 0x58#64) Partition.words := by
  rw [Program.hasWords, show (program entry).base = entry from rfl]
  have offset : entry + 0x58#64 - entry = 0x58#64 := by
    rw [BitVec.add_comm entry, BitVec.add_sub_cancel]
  rw [offset]
  change (program 0).hasWordsOff 0x58 Partition.words
  decide +kernel

/-- The linked ARM64 routine sorts any input list given sufficient writable stack. -/
theorem quicksort_machine_correct (entry base : BitVec 64) (input : List (BitVec 8))
    (stackFrames : Nat) (depth : input.length ≤ stackFrames)
    (size : 48 * stackFrames ≤ 2^64) :
    subroutine_ok (program entry) entry (quicksortSpec base input stackFrames) :=
  quicksort_of_words (program entry) entry base input stackFrames
    (quicksort_hasWords entry) (partition_hasWords entry) depth size

/-- X0 is the array, X1 is its length, and LR is the return address.
    Read the result back from machine memory and keep the caller's frame. -/
theorem quicksort_returns_sorted (initial : State) (frame : SepProp) (input : List (BitVec 8))
    (running : initial.status = .Running) (stackAligned : initial.spAligned = true)
    (loaded : (program initial.pc).CodeLoaded initial.mem)
    (lengthReg : initial.readReg64 .x1 = BitVec.ofNat 64 input.length)
    (size : 48 * input.length ≤ 2^64)
    (memory : initial.mem ⊨ (initial.readReg64 .x0 ↦ₛ input) ∗
      stackAt initial.sp (48 * input.length) ∗ frame) :
    ∃ final : State, Steps (program initial.pc) initial final ∧
      Returned initial final ∧ CallingConventionPreserved initial final ∧
      final.mem.readBytes (initial.readReg64 .x0) input.length = Spec.quicksort input ∧
      Spec.Sorts input (final.mem.readBytes (initial.readReg64 .x0) input.length) ∧
      (final.mem ⊨ (initial.readReg64 .x0 ↦ₛ Spec.quicksort input) ∗
        stackAt initial.sp (48 * input.length) ∗ frame) := by
  let base := initial.readReg64 .x0
  have pre : initial.mem ⊨ (quicksortSpec base input input.length).pre () initial ∗ frame := by
    rw [quicksortSpec, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc]
    exact ⟨⟨rfl, lengthReg⟩, memory⟩
  have correct := quicksort_machine_correct initial.pc base input input.length (Nat.le_refl _) size
  have reaches := correct.to_outcome () frame initial rfl running pre stackAligned
  obtain ⟨final, steps, outcome⟩ := reaches_outcome_iff.mp reaches loaded
  rcases outcome with ⟨returned, abi, post⟩ | ⟨_, panic⟩ | ⟨_, _, exited⟩ | ⟨_, oom⟩
  · change final.mem ⊨
      ((base ↦ₛ Spec.quicksort input) ∗ stackAt initial.sp (48 * input.length)) ∗ frame at post
    rw [sepConj_assoc] at post
    have readback := ((IsBlock.pointsToBytes base (Spec.quicksort input)).read post).2
    rw [(Spec.quicksort_sorts input).2.length_eq] at readback
    refine ⟨final, steps, returned, abi, readback, ?_, post⟩
    rw [readback]
    exact Spec.quicksort_sorts input
  · exact False.elim (not_satisfies_false_sepConj panic)
  · exact False.elim (not_satisfies_false_sepConj exited)
  · exact False.elim (not_satisfies_false_sepConj oom)

#print axioms quicksort_machine_correct
#print axioms quicksort_returns_sorted

end Example02C
