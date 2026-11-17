import Std

namespace Example02C.Spec

set_option autoImplicit false

variable {width : Nat}

/-- The sorting property for the input list and the bytes read back from memory.
`Pairwise (· ≤ ·)` requires nondecreasing unsigned order. `Perm` requires the same
number of occurrences of each value, including duplicates. -/
def Sorts (input output : List (BitVec width)) : Prop :=
  output.Pairwise (· ≤ ·) ∧ output.Perm input

/-- Sorting the two sides of a partition gives a sorted permutation of the original input. -/
theorem sorts_partition {input left right sortedLeft sortedRight : List (BitVec width)}
    {pivot : BitVec width}
    (partition : (left ++ pivot :: right).Perm input)
    (leftBound : ∀ x ∈ left, x < pivot)
    (rightBound : ∀ x ∈ right, pivot ≤ x)
    (leftSorted : Sorts left sortedLeft)
    (rightSorted : Sorts right sortedRight) :
    Sorts input (sortedLeft ++ pivot :: sortedRight) := by
  have lower (x : BitVec width) (hx : x ∈ sortedLeft) : x ≤ pivot :=
    BitVec.le_of_lt (leftBound x (leftSorted.2.mem_iff.mp hx))
  have upper (x : BitVec width) (hx : x ∈ sortedRight) : pivot ≤ x :=
    rightBound x (rightSorted.2.mem_iff.mp hx)
  refine ⟨List.pairwise_append.mpr ⟨leftSorted.1, ?_, ?_⟩,
    (leftSorted.2.append_cons pivot rightSorted.2).trans partition⟩
  · exact List.pairwise_cons.mpr ⟨upper, rightSorted.1⟩
  · intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact lower x hx
    · exact BitVec.le_trans (lower x hx) (upper y hy)

/-- The two stores in a swap both use values from the original array. -/
def swap (arr : List (BitVec width)) (i j : Nat) : List (BitVec width) :=
  (arr.set i arr[j]!).set j arr[i]!

@[simp] theorem swap_length (arr : List (BitVec width)) (i j : Nat) :
    (swap arr i j).length = arr.length := by
  simp [swap]

theorem swap_perm {arr : List (BitVec width)} {i j : Nat}
    (hi : i < arr.length) (hj : j < arr.length) :
    (swap arr i j).Perm arr := by
  simpa only [swap, getElem!_pos arr i hi, getElem!_pos arr j hj] using List.set_set_perm hi hj

theorem swap_getElem! {arr : List (BitVec width)} {i j k : Nat} (hk : k < arr.length) :
    (swap arr i j)[k]! = if k = i then arr[j]! else if k = j then arr[i]! else arr[k]! := by
  have hk' : k < (swap arr i j).length := by simpa using hk
  rw [getElem!_pos (swap arr i j) k hk']
  simp only [swap, List.getElem_set, getElem!_pos arr k hk]
  by_cases hki : k = i <;> by_cases hkj : k = j
  · subst i
    subst j
    simp
  · subst i
    simp [Ne.symm hkj]
  · subst j
    simp [hki]
  · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]

/-- The first element holds the pivot while scanning. Indices `1` through `k` are
below the pivot, and indices strictly between `k` and `i` are at least the pivot. -/
structure PartitionScan (input arr : List (BitVec width)) (pivot : BitVec width) (k i : Nat) : Prop where
  scanBound : i ≤ arr.length
  splitBound : k < i
  pivotAtZero : arr[0]? = some pivot
  leftBound : ∀ j, 0 < j → j ≤ k → arr[j]! < pivot
  rightBound : ∀ j, k < j → j < i → pivot ≤ arr[j]!
  permutation : arr.Perm input

theorem partitionScan_start {arr : List (BitVec width)} {pivot : BitVec width}
    (h : arr[0]? = some pivot) : PartitionScan arr arr pivot 0 1 := by
  obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp h
  exact ⟨hlen, by decide, h, fun j hj hk => by omega, fun j hj hi => by omega, List.Perm.refl _⟩

theorem PartitionScan.advance_low
    {input arr : List (BitVec width)} {pivot : BitVec width} {k i : Nat}
    (h : PartitionScan input arr pivot k i) (hi : i < arr.length) (hx : arr[i]! < pivot) :
    PartitionScan input (swap arr (k + 1) i) pivot (k + 1) (i + 1) := by
  have hki := h.splitBound
  refine ⟨by simpa using Nat.succ_le_of_lt hi, by omega, ?_, ?_, ?_,
    (swap_perm (by omega) hi).trans h.permutation⟩
  · have hzero : 0 < (swap arr (k + 1) i).length := by simp; omega
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨hzero, ?_⟩
    rw [← getElem!_pos (swap arr (k + 1) i) 0 hzero, swap_getElem! (by omega)]
    simpa [show 0 ≠ i by omega] using List.getElem!_of_getElem? h.pivotAtZero
  · intro j hj hjk
    rw [swap_getElem! (by omega)]
    by_cases hnew : j = k + 1
    · simpa [hnew] using hx
    · simpa [hnew, show j ≠ i by omega] using h.leftBound j hj (by omega)
  · intro j hjk hji
    rw [swap_getElem! (by omega)]
    by_cases hnew : j = i
    · simpa [hnew, show i ≠ k + 1 by omega] using h.rightBound (k + 1) (by omega) (by omega)
    · simpa [show j ≠ k + 1 by omega, hnew] using h.rightBound j (by omega) (by omega)

theorem PartitionScan.advance_high
    {input arr : List (BitVec width)} {pivot : BitVec width} {k i : Nat}
    (h : PartitionScan input arr pivot k i) (hi : i < arr.length) (hx : pivot ≤ arr[i]!) :
    PartitionScan input arr pivot k (i + 1) := by
  have hki := h.splitBound
  refine ⟨hi, by omega, h.pivotAtZero, h.leftBound, ?_, h.permutation⟩
  intro j hjk hji
  by_cases hnew : j = i
  · simpa [hnew] using hx
  · exact h.rightBound j hjk (by omega)

/-- The final swap places the pivot between the two partitions. -/
structure PartitionResult (input out : List (BitVec width)) (pivot : BitVec width) (k : Nat) : Prop where
  splitBound : k < out.length
  split : out = out.take k ++ pivot :: out.drop (k + 1)
  leftBound : ∀ x ∈ out.take k, x < pivot
  rightBound : ∀ x ∈ out.drop (k + 1), pivot ≤ x
  permutation : out.Perm input

theorem PartitionScan.finish {input arr : List (BitVec width)} {pivot : BitVec width} {k : Nat}
    (h : PartitionScan input arr pivot k arr.length) : PartitionResult input (swap arr 0 k) pivot k := by
  let out := swap arr 0 k
  have hk := h.splitBound
  have hlen : out.length = arr.length := swap_length arr 0 k
  have hk' : k < out.length := by omega
  have hzero := List.getElem!_of_getElem? h.pivotAtZero
  change PartitionResult input out pivot k
  refine ⟨hk', ?_, ?_, ?_, (swap_perm (by omega) hk).trans h.permutation⟩
  · have hp : out[k] = pivot := by
      rw [← getElem!_pos out k hk', swap_getElem! hk]
      by_cases hz : k = 0 <;> simp [hz, hzero]
    conv => lhs; rw [← List.take_append_drop k out]
    rw [List.drop_eq_getElem_cons hk', hp]
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    have hj' : j < out.length := by omega
    rw [← getElem!_pos out j hj', swap_getElem! (by omega)]
    by_cases hz : j = 0
    · simpa [hz] using h.leftBound k (by omega) (by omega)
    · simpa [hz, show j ≠ k by omega] using h.leftBound j (by omega) (by omega)
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
    have hj' : k + 1 + j < out.length := by omega
    rw [← getElem!_pos out (k + 1 + j) hj', swap_getElem! (by omega)]
    simpa [show k + 1 + j ≠ 0 by omega, show k + 1 + j ≠ k by omega] using
      h.rightBound (k + 1 + j) (by omega) (by omega)

end Example02C.Spec
