import ProofLib
import QuicksortPartition

namespace Example02C

open Arm64 ProofLib
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

abbrev Byte := BitVec 8
abbrev Addr := BitVec 64

/-- The 22 instruction words of the compiled recursive driver. -/
def quicksortWords : List (BitVec 32) :=
  [0xf100083f#32, 0x54000283#32, 0xa9bd7bfd#32, 0xf9000bf5#32,
   0x910003fd#32, 0xa9024ff4#32, 0xaa0003f3#32, 0xaa0103f4#32,
   0x9400000e#32, 0xaa0003f5#32, 0xaa1303e0#32, 0xaa1503e1#32,
   0x97fffff4#32, 0x8b150268#32, 0xaa3503e9#32, 0x91000500#32,
   0x8b140121#32, 0x97ffffef#32, 0xa9424ff4#32, 0xf9400bf5#32,
   0xa8c37bfd#32, 0xd65f03c0#32]

/-- Machine contract for sorting in place. At entry, X0 points to the writable
input bytes, X1 gives their length, and the caller provides 48 writable stack bytes
per budgeted frame. On return, `output` names the bytes at the original X0 address
and satisfies `Spec.Sorts input output`. The stack region is writable again at the
entry stack pointer, with its contents left unspecified. -/
def quicksortSpec (base : Addr) (input : List Byte) (stackFrames : Nat) : Arm64.Spec Unit where
  pre := fun _ s => ⌜s.readReg64 .x0 = base ∧ s.readReg64 .x1 = BitVec.ofNat 64 input.length⌝ ∗
    (base ↦ₛ input) ∗ stackAt s.sp (48 * stackFrames)
  post := fun _ s0 _ => ∃∗ output : List Byte,
    ⌜Spec.Sorts input output⌝ ∗ (base ↦ₛ output) ∗ stackAt s0.sp (48 * stackFrames)

private theorem small_input_sorts (input : List Byte) (h : input.length < 2) :
    Spec.Sorts input input := by
  rcases input with _ | ⟨x, _ | ⟨y, xs⟩⟩
  · simp [Spec.Sorts]
  · simp [Spec.Sorts]
  · simp at h; omega

private theorem quicksort_words_aux (prog : Program) (entry : Addr)
    (code : prog.hasWords entry quicksortWords)
    (partition : ∀ base pivot tail, subroutine_ok prog (entry + 0x58#64) (Partition.spec base pivot tail)) :
    ∀ (n : Nat) (base : Addr) (input : List Byte) (stackFrames : Nat),
      input.length = n → n ≤ stackFrames → 48 * stackFrames ≤ 2 ^ 64 →
      subroutine_ok prog entry (quicksortSpec base input stackFrames) := by
  -- Each recursive machine call is justified by the contract for a shorter array.
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro base input stackFrames hlen hdepth hsize
    have hfit : input.length < 2 ^ 64 := by omega
    -- Fetch each instruction at its offset from the caller-supplied entry PC.
    have hf0 := Program.fetch_of_hasWords code 0 (by decide)
    have hf1 := Program.fetch_of_hasWords code 1 (by decide)
    have hf2 := Program.fetch_of_hasWords code 2 (by decide)
    have hf3 := Program.fetch_of_hasWords code 3 (by decide)
    have hf4 := Program.fetch_of_hasWords code 4 (by decide)
    have hf5 := Program.fetch_of_hasWords code 5 (by decide)
    have hf6 := Program.fetch_of_hasWords code 6 (by decide)
    have hf7 := Program.fetch_of_hasWords code 7 (by decide)
    have hf8 := Program.fetch_of_hasWords code 8 (by decide)
    have hf9 := Program.fetch_of_hasWords code 9 (by decide)
    have hf10 := Program.fetch_of_hasWords code 10 (by decide)
    have hf11 := Program.fetch_of_hasWords code 11 (by decide)
    have hf12 := Program.fetch_of_hasWords code 12 (by decide)
    have hf13 := Program.fetch_of_hasWords code 13 (by decide)
    have hf14 := Program.fetch_of_hasWords code 14 (by decide)
    have hf15 := Program.fetch_of_hasWords code 15 (by decide)
    have hf16 := Program.fetch_of_hasWords code 16 (by decide)
    have hf17 := Program.fetch_of_hasWords code 17 (by decide)
    have hf18 := Program.fetch_of_hasWords code 18 (by decide)
    have hf19 := Program.fetch_of_hasWords code 19 (by decide)
    have hf20 := Program.fetch_of_hasWords code 20 (by decide)
    have hf21 := Program.fetch_of_hasWords code 21 (by decide)
    have hnfit : n < 2 ^ 64 := by omega
    wp_init u s0
    wp_step
    wp_step
    wp_if hshort
    · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnfit] at hshort
      have hsorted := small_input_sorts input (by omega)
      wp_step
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      refine ⟨?_, ?_, ?_⟩
      · intro hm
        rw [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨input, ?_⟩
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hsorted, hm⟩
      · wp_norm_lhs
      · simp [CalleeSavedPreserved, wp_norm, arm64_norm, *]
    · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnfit] at hshort
      have hlong : 2 ≤ n := by omega
      -- The prologue uses the top 48 bytes. Both children reuse the region below it.
      have hframe : 48 * stackFrames = 48 * (stackFrames - 1) + 8 * 6 := by omega
      have hstack : stackAt s0.sp (48 * stackFrames) =
          stackAt (s0.sp - 48#64) (48 * (stackFrames - 1)) ∗ cells (s0.sp - 48#64) 6 := by
        simpa only [← hframe] using
          stackAt_split_cells s0.sp (48 * (stackFrames - 1)) 6 (by omega)
      wp_conv_pre =>
        rw [hstack]
        simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
          sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
      iterate 6 (apply SepWP.exists_elim; intro)
      wp_steps
      rcases input with _ | ⟨pivot, tail⟩
      · simp at hlen; omega
      · wp_call (partition base pivot tail) ()
        -- Name the partition witnesses and the facts returned by the callee.
        revert w w_1
        intro left right returnedIndex partitioned leftBound rightBound
        have hparts := partitioned.length_eq
        simp only [List.length_append, List.length_cons, hlen] at hparts
        have leftOk := ih left.length (by omega) base left (stackFrames - 1) rfl (by omega) (by omega)
        have rightOk := ih right.length (by omega) (base + BitVec.ofNat 64 (left.length + 1))
          right (stackFrames - 1) rfl (by omega) (by omega)
        wp_conv_pre => rw [pointsToBytes_append, pointsToBytes_cons_off, sepConj_assoc]
        wp_steps
        wp_call leftOk ()
        revert w
        intro sortedLeft leftSorted
        have hnSplit : n = left.length + 1 + right.length := by omega
        -- The compiler forms the right length as `~left.length + n`.
        have hRightSize : ~~~(BitVec.ofNat 64 left.length) + BitVec.ofNat 64 n =
            BitVec.ofNat 64 right.length := by
          rw [hnSplit, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.not_eq_neg_add]
          bv_arith
        wp_steps
        wp_call rightOk ()
        revert w
        intro sortedRight rightSorted
        have hsorted := Spec.sorts_partition partitioned leftBound rightBound leftSorted rightSorted
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        refine ⟨?_, ?_, ?_⟩
        · intro hm
          -- Join the two sorted slices with the pivot and return the stack region.
          rw [hsp_sf_1, hsp_sf] at hm
          rw [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨sortedLeft ++ pivot :: sortedRight, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨hsorted, ?_⟩
          rw [pointsToBytes_append, leftSorted.2.length_eq, pointsToBytes_cons_off, hstack]
          simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
            sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
          sep_entail
        · wp_norm_lhs
        · simp [CalleeSavedPreserved, wp_norm, arm64_norm, *]

/-- The driver and partition code sort any input that fits the supplied stack budget. -/
theorem quicksort_of_words (prog : Program) (entry base : Addr) (input : List Byte)
    (stackFrames : Nat) (code : prog.hasWords entry quicksortWords)
    (partitionCode : prog.hasWords (entry + 0x58#64) Partition.words)
    (depth : input.length ≤ stackFrames) (size : 48 * stackFrames ≤ 2 ^ 64) :
    subroutine_ok prog entry (quicksortSpec base input stackFrames) :=
  quicksort_words_aux prog entry code
    (fun a pivot tail => Partition.of_words prog (entry + 0x58#64) a pivot tail partitionCode)
    input.length base input stackFrames rfl depth size

#print axioms quicksort_of_words

end Example02C
