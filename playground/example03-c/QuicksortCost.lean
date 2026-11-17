import Arm64.Trusted.Surface.IncludeBytes
import QuicksortCostInput
import QuicksortDriverCost

namespace Example03C

open Arm64 ProofLib

set_option autoImplicit false

/-- Both linked functions, extracted from the same C sources as Example 02. -/
def program (entry : BitVec 64) : Program :=
  { base := entry, code := include_bytes% "../example02-c/build/quicksort_u8.bin" 0 184 }

private theorem driver_hasWords (entry : BitVec 64) :
    (program entry).hasWords entry Example02C.quicksortWords := by
  rw [Program.hasWords, show (program entry).base = entry from rfl, BitVec.sub_self]
  change (program 0).hasWordsOff 0 Example02C.quicksortWords
  decide +kernel

private theorem partition_hasWords (entry : BitVec 64) :
    (program entry).hasWords (entry + 0x58#64) Example02C.Partition.words := by
  rw [Program.hasWords, show (program entry).base = entry from rfl,
    show entry + 0x58#64 - entry = 0x58#64 by
      rw [BitVec.add_comm entry, BitVec.add_sub_cancel]]
  change (program 0).hasWordsOff 0x58 Example02C.Partition.words
  decide +kernel

/-- Conditions for measuring a call. The caller's continuation is outside the
extracted function code. X0 and X1 give the array address and its length. -/
structure ValidCall (initial : State) (input : List (BitVec 8)) (frame : SepProp) : Prop where
  running : initial.status = .Running
  stackAligned : initial.spAligned = true
  loaded : (program initial.pc).CodeLoaded initial.mem
  returnOutside : ¬ InRegion initial.pc 184 (initial.readReg64 .lr)
  lengthReg : initial.readReg64 .x1 = BitVec.ofNat 64 input.length
  stackSize : 48 * input.length ≤ 2^64
  memory : initial.mem ⊨ (initial.readReg64 .x0 ↦ₛ input) ∗
    stackAt initial.sp (48 * input.length) ∗ frame

/-- Cost is the number of ARM64 steps through the first normal return. The
start state is the function entry and the last step is its returning instruction. -/
def ReturnsIn (prog : Program) (count : Nat) (initial final : State) : Prop :=
  StepsN prog count initial final ∧ Returned initial final ∧
    ∀ k < count, ∀ mid, StepsN prog k initial mid → ¬ Returned initial mid

theorem ReturnsIn.count_eq {prog : Program} {initial final₁ final₂ : State} {count₁ count₂ : Nat}
    (h₁ : ReturnsIn prog count₁ initial final₁) (h₂ : ReturnsIn prog count₂ initial final₂) :
    count₁ = count₂ := by
  rcases Nat.lt_trichotomy count₁ count₂ with hlt | heq | hgt
  · exact (h₂.2.2 count₁ hlt final₁ h₁.1 h₁.2.1).elim
  · exact heq
  · exact (h₁.2.2 count₂ hgt final₂ h₂.1 h₂.2.1).elim

private theorem fetch_return_none {initial : State} {input : List (BitVec 8)} {frame : SepProp}
    (call : ValidCall initial input frame) :
    (program initial.pc).fetch (initial.readReg64 .lr) = none := by
  have hoff : 184 ≤ (initial.readReg64 .lr - initial.pc).toNat :=
    Nat.le_of_not_gt call.returnOutside
  unfold Program.fetch
  split
  · rfl
  · unfold Program.readWordOff
    split
    · rfl
    · rw [List.drop_eq_nil_of_le (by exact hoff)]
      rfl

/-- For every valid call, the linked ARM64 code returns within the quadratic
budget. If all input bytes equal one another, the exact count is equalCost n. -/
theorem quicksort_instruction_count (initial : State) (input : List (BitVec 8)) (frame : SepProp)
    (call : ValidCall initial input frame) :
    ∃ count final, ReturnsIn (program initial.pc) count initial final ∧
      CallingConventionPreserved initial final ∧
      count ≤ stepBudget input.length ∧
      (∀ byte, input = List.replicate input.length byte → count = equalCost input.length) ∧
      let output := final.mem.readBytes (initial.readReg64 .x0) input.length
      Example02C.Spec.Sorts input output ∧
        (final.mem ⊨ (initial.readReg64 .x0 ↦ₛ output) ∗
          stackAt initial.sp (48 * input.length) ∗ frame) := by
  let base := initial.readReg64 .x0
  have pre : initial.mem ⊨ (Example02C.quicksortSpec base input input.length).pre () initial ∗ frame := by
    rw [Example02C.quicksortSpec, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc]
    exact ⟨⟨rfl, call.lengthReg⟩, call.memory⟩
  have correct := quicksort_cost_of_words (program initial.pc) initial.pc base input input.length
    (driver_hasWords initial.pc) (partition_hasWords initial.pc) (Nat.le_refl _) call.stackSize
  obtain ⟨count, final, steps, returned, abi, post⟩ :=
    correct () frame initial rfl call.running call.stackAligned pre call.loaded
  rw [driverPost, sepConj_assoc, satisfies_pure_sepConj] at post
  obtain ⟨⟨upper, equal⟩, result⟩ := post
  have first : ReturnsIn (program initial.pc) count initial final := by
    refine ⟨steps.toStepsN, returned, ?_⟩
    intro k hlt mid shortRun earlier
    exact steps.prefix_pc_ne shortRun hlt (fetch_return_none call) earlier.1
  change final.mem ⊨
      (∃∗ output : List (BitVec 8), ⌜Example02C.Spec.Sorts input output⌝ ∗ (base ↦ₛ output) ∗
        stackAt initial.sp (48 * input.length)) ∗ frame at result
  rw [sepExists_sepConj_left, satisfies_sepExists] at result
  obtain ⟨output, result⟩ := result
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc] at result
  obtain ⟨sorted, memory⟩ := result
  have readback := ((IsBlock.pointsToBytes base output).read memory).2
  rw [sorted.2.length_eq] at readback
  refine ⟨count, final, first, abi, upper, equal, ?_⟩
  rw [readback]
  exact ⟨sorted, memory⟩

/-- Any first normal return of a valid call obeys the quadratic upper bound. -/
theorem quicksort_upper_bound {initial final : State} {input : List (BitVec 8)}
    {frame : SepProp} {count : Nat} (call : ValidCall initial input frame)
    (returned : ReturnsIn (program initial.pc) count initial final) :
    count ≤ stepBudget input.length := by
  obtain ⟨_, _, first, _, upper, _⟩ := quicksort_instruction_count initial input frame call
  exact returned.count_eq first ▸ upper

/-- The input length is possible in the 64-bit model with the required stack. -/
def HasValidCall (n : Nat) : Prop :=
  ∃ (initial : State) (input : List (BitVec 8)) (frame : SepProp),
    input.length = n ∧ ValidCall initial input frame

/-- A concrete layout realizes every length through 2^56. -/
theorem valid_calls_exist (n : Nat) (fits : n ≤ 2 ^ 56) : HasValidCall n := by
  let initial := equalInputState (program 0x1000#64) n 0#8
  obtain ⟨hpc, hlr, running, aligned, loaded, lengthReg, size, memory⟩ :=
    equalInputState_valid (program 0x1000#64) n 0#8 rfl rfl fits
  have call : ValidCall initial (List.replicate n 0#8) SepProp.emp := by
    refine ⟨running, aligned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpc]
      exact loaded
    · rw [hpc, hlr]
      decide +kernel
    · simpa only [List.length_replicate] using lengthReg
    · simpa only [List.length_replicate] using size
    · simpa only [List.length_replicate] using memory
  exact ⟨initial, List.replicate n 0#8, SepProp.emp, by simp, call⟩

private theorem replace_input {initial : State} {input : List (BitVec 8)} {frame : SepProp}
    (call : ValidCall initial input frame) (byte : BitVec 8) :
    ∃ initial', ValidCall initial' (List.replicate input.length byte) frame := by
  let base := initial.readReg64 .x0
  let equalBytes := List.replicate input.length byte
  have length : input.length = equalBytes.length := by simp [equalBytes]
  have size := call.stackSize
  have writable : initial.mem.canWrite base equalBytes.length = true := by
    rw [← length]
    exact (IsBlock.pointsToBytes base input).canWrite (by omega) call.memory
  let initial' := initial.setMem (initial.mem.writeBytes base equalBytes)
  refine ⟨initial', call.running, call.stackAligned, ?_, call.returnOutside, ?_, ?_, ?_⟩
  · exact call.loaded.of_keepsFrozen (Memory.keepsFrozen_writeBytes equalBytes writable)
  · simpa only [initial', State.readReg64_setMem, List.length_replicate] using call.lengthReg
  · simpa only [List.length_replicate] using size
  · rw [← length]
    exact satisfies_writeBytes_step call.memory length

/-- For every feasible length, setting all the input bytes equal gives a legal
call with exact first-return count equalCost n, at least n squared. -/
theorem quicksort_equal_input_lower_bound (n : Nat) (possible : HasValidCall n) (byte : BitVec 8) :
    ∃ initial final frame,
      ValidCall initial (List.replicate n byte) frame ∧
      ReturnsIn (program initial.pc) (equalCost n) initial final ∧ n * n ≤ equalCost n := by
  obtain ⟨initial, input, frame, length, call⟩ := possible
  obtain ⟨equalInitial, valid⟩ := replace_input call byte
  rw [length] at valid
  obtain ⟨count, final, returned, _, _, equal, _⟩ :=
    quicksort_instruction_count equalInitial (List.replicate n byte) frame valid
  have hcount : count = equalCost n := by simpa using equal byte (by simp)
  exact ⟨equalInitial, final, frame, valid, hcount ▸ returned, equalCost_lower n⟩

/-- Count k is realized by a legal call with an array of length n. -/
def CostAtLength (n k : Nat) : Prop :=
  ∃ (initial final : State) (input : List (BitVec 8)) (frame : SepProp),
    input.length = n ∧ ValidCall initial input frame ∧
      ReturnsIn (program initial.pc) k initial final

/-- Review goal for tight worst-case complexity. For every positive feasible
length n, every realized cost is at most 43*n² and some cost is at least n². -/
theorem quicksort_worst_case_quadratic (n : Nat) (positive : 0 < n) (possible : HasValidCall n) :
    (∀ k, CostAtLength n k → k ≤ 43 * n * n) ∧
    (∃ k, CostAtLength n k ∧ n * n ≤ k) := by
  constructor
  · rintro k ⟨initial, final, input, frame, length, call, returned⟩
    have upper := quicksort_upper_bound call returned
    rw [length] at upper
    have squarePositive := Nat.mul_pos positive positive
    simp only [stepBudget, Nat.mul_assoc] at upper ⊢
    omega
  · obtain ⟨initial, final, frame, call, returned, lower⟩ :=
      quicksort_equal_input_lower_bound n possible 0#8
    exact ⟨equalCost n, ⟨initial, final, List.replicate n 0#8, frame, by simp, call, returned⟩, lower⟩

#print axioms quicksort_upper_bound
#print axioms quicksort_equal_input_lower_bound
#print axioms quicksort_worst_case_quadratic

end Example03C
