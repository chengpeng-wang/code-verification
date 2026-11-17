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

/-- The linked ARM64 bytes satisfy `quicksortSpec` for any valid entry address and
array. The stack budget allows at least one frame per input byte, and its total
size fits in the 64-bit address space. -/
theorem quicksort_machine_correct (entry base : BitVec 64) (input : List (BitVec 8))
    (stackFrames : Nat) (depth : input.length ≤ stackFrames)
    (size : 48 * stackFrames ≤ 2^64) :
    subroutine_ok (program entry) entry (quicksortSpec base input stackFrames) :=
  quicksort_of_words (program entry) entry base input stackFrames
    (quicksort_hasWords entry) (partition_hasWords entry) depth size

/-- End-to-end sorting goal. Assume the linked ARM64 code is loaded at the initial
PC, the machine is running, SP is 16-byte aligned, and X1 gives the length of the
writable input array at X0. The caller provides a separate writable stack region
of 48 bytes per element and a separate memory assertion `frame`.

The execution returns to the initial LR in finitely many steps, restores SP and
preserves the callee-saved registers. The bytes read back at the original X0
address are an unsigned sorted permutation of the input. On return the stack
region is writable and the caller's `frame` still holds. -/
theorem quicksort_returns_sorted (initial : State) (frame : SepProp) (input : List (BitVec 8))
    (running : initial.status = .Running) (stackAligned : initial.spAligned = true)
    (loaded : (program initial.pc).CodeLoaded initial.mem)
    (lengthReg : initial.readReg64 .x1 = BitVec.ofNat 64 input.length)
    (size : 48 * input.length ≤ 2^64)
    (memory : initial.mem ⊨ (initial.readReg64 .x0 ↦ₛ input) ∗
      stackAt initial.sp (48 * input.length) ∗ frame) :
    ∃ final : State,
      let output := final.mem.readBytes (initial.readReg64 .x0) input.length
      Steps (program initial.pc) initial final ∧
        Returned initial final ∧ CallingConventionPreserved initial final ∧
        Spec.Sorts input output ∧
        (final.mem ⊨ (initial.readReg64 .x0 ↦ₛ output) ∗
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
      (∃∗ output : List (BitVec 8), ⌜Spec.Sorts input output⌝ ∗ (base ↦ₛ output) ∗
        stackAt initial.sp (48 * input.length)) ∗ frame at post
    rw [sepExists_sepConj_left, satisfies_sepExists] at post
    obtain ⟨output, result⟩ := post
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc] at result
    obtain ⟨sorted, memory⟩ := result
    have readback := ((IsBlock.pointsToBytes base output).read memory).2
    rw [sorted.2.length_eq] at readback
    refine ⟨final, steps, returned, abi, ?_⟩
    rw [readback]
    exact ⟨sorted, memory⟩
  · exact False.elim (not_satisfies_false_sepConj panic)
  · exact False.elim (not_satisfies_false_sepConj exited)
  · exact False.elim (not_satisfies_false_sepConj oom)

#print axioms quicksort_machine_correct
#print axioms quicksort_returns_sorted

end Example02C
