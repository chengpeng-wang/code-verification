import QuicksortPartitionCost
import QuicksortMachine

namespace Example03C

open Arm64 ProofLib Example02C

set_option autoImplicit false

/-- Uniform instruction budget for an input of length `n`. -/
def stepBudget (n : Nat) : Nat := 40 * n * n + 3

/-- The exact count on an array of equal bytes. The nontrivial case pays for
the driver, partition, the empty left call, and a right call of length `n-1`. -/
def equalCost : Nat → Nat
  | 0 => 3
  | 1 => 3
  | n + 2 => equalCost (n + 1) + 31 + 6 * (n + 2)

/-- Closed form of the equal-input recurrence at positive lengths. -/
theorem equalCost_closed (n : Nat) (hn : 0 < n) :
    equalCost n + 34 = 3 * n * n + 34 * n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => decide
    | succ k =>
      have h := ih (by omega)
      change equalCost (k + 1) + 31 + 6 * (k + 2) + 34 = 3 * (k + 2) * (k + 2) + 34 * (k + 2)
      change equalCost (k + 1) + 34 = 3 * (k + 1) * (k + 1) + 34 * (k + 1) at h
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_one] at h ⊢
      omega

/-- The equal-input family incurs at least `n²` instructions. -/
theorem equalCost_lower (n : Nat) : n * n ≤ equalCost n := by
  cases n with
  | zero => decide
  | succ n =>
    have h := equalCost_closed (n + 1) (by omega)
    simp only [Nat.mul_assoc] at h
    omega

private theorem budget_partition (left right : Nat) :
    stepBudget left + stepBudget right + 23 + 11 * (left + right + 1) ≤
      stepBudget (left + right + 1) := by
  simp only [stepBudget, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_one]
  omega

private theorem replicate_partition {left right tail : List Byte} {pivot v : Byte}
    (partitioned : (left ++ pivot :: right).Perm (pivot :: tail))
    (leftBound : ∀ a ∈ left, a < pivot)
    (equal : pivot :: tail = List.replicate (pivot :: tail).length v) :
    left = [] ∧ right = List.replicate right.length v := by
  have same (a : Byte) (ha : a ∈ left ++ pivot :: right) : a = v :=
    List.eq_of_mem_replicate (equal ▸ partitioned.mem_iff.mp ha)
  have pivotEq := same pivot (List.mem_append_right _ (by simp))
  refine ⟨?_, List.eq_replicate_iff.mpr ⟨rfl, fun a ha => same a (List.mem_append_right _ (by simp [ha]))⟩⟩
  cases left with
  | nil => rfl
  | cons a as =>
    have h := leftBound a (by simp)
    rw [same a (by simp), pivotEq] at h
    simp at h

/-- The exact instruction count satisfies the uniform budget and the equal-byte
recurrence. The rest of the postcondition is the in-place sorting contract. -/
def driverPost (base : Addr) (input : List Byte) (stackFrames : Nat)
    (count : Nat) (_ : Unit) (s0 sf : State) : SepProp :=
  ⌜count ≤ stepBudget input.length ∧
    (∀ v, input = List.replicate input.length v → count = equalCost input.length)⌝ ∗
  (quicksortSpec base input stackFrames).post () s0 sf

private theorem small_input_sorts (input : List Byte) (h : input.length < 2) :
    Spec.Sorts input input := by
  rcases input with _ | ⟨x, _ | ⟨y, xs⟩⟩
  · simp [Spec.Sorts]
  · simp [Spec.Sorts]
  · simp at h; omega

private theorem call_pre {s : State} {P F : SepProp} {base sp : Addr} {input : List Byte}
    {stackFrames : Nat} (stackPtr : s.sp = sp) (array : s.readReg64 .x0 = base)
    (length : s.readReg64 .x1 = BitVec.ofNat 64 input.length)
    (frame : SepFrame ((base ↦ₛ input) ∗ stackAt sp (48 * stackFrames)) P F) :
    ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ (quicksortSpec base input stackFrames).pre () s ∗ (F ∗ R)) := by
  intro R h
  rw [quicksortSpec, sepConj_assoc, satisfies_pure_sepConj, stackPtr]
  exact ⟨⟨array, length⟩, by simpa only [frame.eq, sepConj_assoc] using h⟩

private theorem frame_right (left stackMem pivot right saved : SepProp) :
    left ∗ stackMem ∗ pivot ∗ right ∗ saved =
      (right ∗ stackMem) ∗ (left ∗ pivot ∗ saved) := by
  ac_rfl

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

private theorem quicksort_cost_aux (prog : Program) (entry : Addr)
    (code : prog.hasWords entry quicksortWords)
    (partition : ∀ base pivot tail,
      CountedOk prog (entry + 0x58#64) (Partition.spec base pivot tail)
        (PartitionCost.post base pivot tail)) :
    ∀ (n : Nat) (base : Addr) (input : List Byte) (stackFrames : Nat),
      input.length = n → n ≤ stackFrames → 48 * stackFrames ≤ 2 ^ 64 →
      CountedOk prog entry (quicksortSpec base input stackFrames) (driverPost base input stackFrames) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro base input stackFrames hlen hdepth hsize
    have hfit : input.length < 2 ^ 64 := by omega
    have hnfit : n < 2 ^ 64 := by omega
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
    refine CountedOk.of_wp
      (prePure := fun _ s => s.readReg64 .x0 = base ∧ s.readReg64 .x1 = BitVec.ofNat 64 input.length)
      (preMem := fun _ s => (base ↦ₛ input) ∗ stackAt s.sp (48 * stackFrames))
      (fun _ _ => rfl) ?_
    intro u R s0 hpc hrun hsp_align ⟨hx0, hx1⟩
    cases u
    cost_steps 2
    cost_if hshort
    · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnfit] at hshort
      have hsmall : input.length < 2 := by omega
      have hsorted := small_input_sorts input hsmall
      cost_steps 1
      apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      refine ⟨?_, ?_, ?_⟩
      · intro hm
        rw [driverPost, sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨by simp [stepBudget], fun _ _ => ?_⟩, ?_⟩
        · have hcases : input.length = 0 ∨ input.length = 1 := by omega
          rcases hcases with heq | heq <;> simp [heq, equalCost]
        · rw [quicksortSpec, sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨input, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          exact ⟨hsorted, hm⟩
      · wp_norm_lhs
      · simp [CalleeSavedPreserved, wp_norm, arm64_norm, *]
    · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnfit] at hshort
      have hlong : 2 ≤ n := by omega
      have hframe : 48 * stackFrames = 48 * (stackFrames - 1) + 8 * 6 := by omega
      have hstack : stackAt s0.sp (48 * stackFrames) =
          stackAt (s0.sp - 48#64) (48 * (stackFrames - 1)) ∗ cells (s0.sp - 48#64) 6 := by
        simpa only [← hframe] using
          stackAt_split_cells s0.sp (48 * (stackFrames - 1)) 6 (by omega)
      conv =>
        arg 4
        rw [hstack]
        simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
          sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
      iterate 6 (apply CountedWP.exists_elim; intro)
      cost_steps 7
      rcases input with _ | ⟨pivot, tail⟩
      · simp at hlen; omega
      · have stackAligned : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
          s0.spAligned_sub 48#64 hsp_align (by decide)
        have callee := partition base pivot tail
        refine CountedWP.call callee () (ret := entry + 0x24#64) (F := ?partitionFrame)
          (by wp_norm_lhs) (by wp_norm_lhs) ?partitionAlign (by wp_norm_lhs) ?partitionPre ?partitionNext
        case partitionAlign =>
          simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using stackAligned
        case partitionPre =>
          intro frame hm
          rw [Partition.spec, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨by wp_norm_lhs, by rw [hlen]; wp_norm_lhs, hfit⟩, ?_⟩
          revert hm
          sep_frame
        case partitionNext =>
          intro partitionSteps sf hpc_sf hrun_sf hsp_sf hcs_sf
          have hspPartition : sf.sp = s0.sp - 48#64 := hsp_sf.trans (by wp_norm_lhs)
          have hreg19 : sf.readReg64 (.gpr 19#5) = base := hcs_sf.1.trans (by wp_norm_lhs)
          have hreg20 : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 n :=
            hcs_sf.2.1.trans (by wp_norm_lhs)
          conv =>
            arg 4
            simp only [PartitionCost.post, sepExists_sepConj_left, sepConj_assoc]
          apply CountedWP.exists_elim
          intro left
          apply CountedWP.exists_elim
          intro right
          apply CountedWP.pure_elim
          intro ⟨returnedIndex, partitioned, leftBound, rightBound, partitionCount⟩
          have hparts := partitioned.length_eq
          simp only [List.length_append, List.length_cons, hlen] at hparts
          have leftOk := ih left.length (by omega) base left (stackFrames - 1) rfl (by omega) (by omega)
          have rightOk := ih right.length (by omega) (base + BitVec.ofNat 64 (left.length + 1))
            right (stackFrames - 1) rfl (by omega) (by omega)
          conv =>
            arg 4
            rw [pointsToBytes_append, pointsToBytes_cons_off, sepConj_assoc]
          cost_steps 4
          refine CountedWP.call leftOk () (ret := entry + 0x34#64) (F := ?leftFrame)
            (by wp_norm_lhs) (by wp_norm_lhs) ?leftAlign (by wp_norm_lhs) ?leftPre ?leftNext
          case leftAlign =>
            simpa only [State.spAligned, wp_norm, arm64_norm, hspPartition] using stackAligned
          case leftPre =>
            apply call_pre (sp := s0.sp - 48#64)
            · wp_norm_lhs
            · wp_norm_lhs
            · wp_norm_lhs
            · constructor
              sep_frame
          case leftNext =>
            intro leftSteps sf_1 hpc_sf_1 hrun_sf_1 hsp_sf_1 hcs_sf_1
            have hspLeft : sf_1.sp = s0.sp - 48#64 := hsp_sf_1.trans (by wp_norm_lhs)
            have hreg19Left : sf_1.readReg64 (.gpr 19#5) = base := hcs_sf_1.1.trans (by wp_norm_lhs)
            have hreg20Left : sf_1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 n :=
              hcs_sf_1.2.1.trans (by wp_norm_lhs)
            have hreg21Left : sf_1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 left.length :=
              hcs_sf_1.2.2.1.trans (by wp_norm_lhs)
            conv =>
              arg 4
              simp only [driverPost, quicksortSpec, sepConj_assoc, wp_norm, arm64_norm, hspPartition,
                sepExists_sepConj_left]
            apply CountedWP.exists_elim
            intro sortedLeft
            apply CountedWP.pure_elim
            intro ⟨⟨leftBudget, leftEqual⟩, leftSorted⟩
            have hnSplit : n = left.length + 1 + right.length := by omega
            have hRightSize : ~~~(BitVec.ofNat 64 left.length) + BitVec.ofNat 64 n =
                BitVec.ofNat 64 right.length := by
              rw [hnSplit, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.not_eq_neg_add]
              bv_arith
            cost_steps 5
            refine CountedWP.call rightOk () (ret := entry + 0x48#64) (F := ?rightFrame)
              (by wp_norm_lhs) (by wp_norm_lhs) ?rightAlign (by wp_norm_lhs) ?rightPre ?rightNext
            case rightAlign =>
              simpa only [State.spAligned, wp_norm, arm64_norm, hspLeft] using stackAligned
            case rightPre =>
              apply call_pre (sp := s0.sp - 48#64)
              · wp_norm_lhs
              · simp only [wp_norm, arm64_norm, BitVec.ofNat_add, BitVec.add_assoc]
              · simpa only [wp_norm, arm64_norm, hreg20Left, hreg21Left, hnSplit] using hRightSize
              · constructor
                simp only [BitVec.ofNat_add]
                exact frame_right _ _ _ _ _
            case rightNext =>
              intro rightSteps sf_2 hpc_sf_2 hrun_sf_2 hsp_sf_2 hcs_sf_2
              have hspRight : sf_2.sp = s0.sp - 48#64 := hsp_sf_2.trans (by wp_norm_lhs)
              conv =>
                arg 4
                simp only [driverPost, quicksortSpec, sepConj_assoc, wp_norm, arm64_norm, hspLeft,
                  sepExists_sepConj_left]
              apply CountedWP.exists_elim
              intro sortedRight
              apply CountedWP.pure_elim
              intro ⟨⟨rightBudget, rightEqual⟩, rightSorted⟩
              have hsorted := Spec.sorts_partition partitioned leftBound rightBound leftSorted rightSorted
              have htail : 0 < tail.length := by simp at hlen; omega
              simp only [PartitionCost.instructionCount, ite_eq_right (by omega : tail.length ≠ 0)] at partitionCount
              cost_steps 4
              apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
              refine ⟨?_, ?_, ?_⟩
              · intro hm
                rw [driverPost, sepConj_assoc, satisfies_pure_sepConj]
                refine ⟨⟨?_, ?_⟩, ?_⟩
                · have hbudget := budget_partition left.length right.length
                  rw [show left.length + right.length + 1 = n by omega, ← hlen] at hbudget
                  simp only [List.length_cons] at hlen hbudget ⊢
                  omega
                · intro v hrep
                  obtain ⟨hempty, hright⟩ := replicate_partition partitioned leftBound hrep
                  have hl := leftEqual v (by simp [hempty])
                  have hr := rightEqual v hright
                  have hleftLen : left.length = 0 := by simp [hempty]
                  have hrightLen : right.length = tail.length := by simp at hlen; omega
                  rw [hleftLen, equalCost] at hl
                  rw [hrightLen] at hr
                  cases hlen' : tail.length with
                  | zero => omega
                  | succ k =>
                    rw [hlen'] at hr
                    simp only [List.length_cons, hlen', Nat.add_assoc, equalCost]
                    omega
                · rw [quicksortSpec, sepExists_sepConj_left, satisfies_sepExists]
                  refine ⟨sortedLeft ++ pivot :: sortedRight, ?_⟩
                  rw [sepConj_assoc, satisfies_pure_sepConj]
                  refine ⟨hsorted, ?_⟩
                  rw [pointsToBytes_append, leftSorted.2.length_eq, pointsToBytes_cons_off, hstack]
                  simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
                    sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
                  sep_entail
              · wp_norm_lhs
              · split_callee_saved
                simp [CalleeSavedPreserved, wp_norm, arm64_norm, *]

/-- Exact instruction counts for the ARM64 driver and partition code, with a
quadratic upper bound for every input and a quadratic witness on equal bytes. -/
theorem quicksort_cost_of_words (prog : Program) (entry base : Addr) (input : List Byte)
    (stackFrames : Nat) (code : prog.hasWords entry quicksortWords)
    (partitionCode : prog.hasWords (entry + 0x58#64) Partition.words)
    (depth : input.length ≤ stackFrames) (size : 48 * stackFrames ≤ 2 ^ 64) :
    CountedOk prog entry (quicksortSpec base input stackFrames) (driverPost base input stackFrames) :=
  quicksort_cost_aux prog entry code
    (fun a pivot tail => PartitionCost.of_words prog (entry + 0x58#64) a pivot tail partitionCode)
    input.length base input stackFrames rfl depth size

end Example03C
