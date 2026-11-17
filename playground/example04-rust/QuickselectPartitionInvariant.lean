import QuickselectPartitionScan
import QuickselectPivot

namespace Example04Rust

open Arm64 ProofLib

set_option autoImplicit false

/-- In the suffix after the pivot, `i` and `j` delimit the two processed sides.
    Strict scans leave no pivot copies; only exchanges may put one copy on
    either side, including an exchange of a slot with itself. -/
structure HoareInvariant (rest : List (BitVec 64)) (pivot : BitVec 64)
    (i j swaps : Nat) : Prop where
  leftFits : i ≤ rest.length
  rightFits : j ≤ rest.length
  overlap : i ≤ j + 1
  leftOrder : ∀ k, k < i → rest[k]!.toInt ≤ pivot.toInt
  rightOrder : ∀ k, j ≤ k → k < rest.length → pivot.toInt ≤ rest[k]!.toInt
  leftEquals : Pivot.countEQ (rest.take i) pivot ≤ swaps
  rightEquals : Pivot.countEQ (rest.drop j) pivot ≤ swaps
  swapsLeft : swaps ≤ i
  swapsRight : swaps ≤ rest.length - j

theorem hoareInvariant_start (rest : List (BitVec 64)) (pivot : BitVec 64) :
    HoareInvariant rest pivot 0 rest.length 0 := by
  refine ⟨Nat.zero_le _, Nat.le_refl _, Nat.zero_le _, ?_, ?_, ?_, ?_, Nat.le_refl _, Nat.zero_le _⟩
  · intro k hk; omega
  · intro k lo hi; omega
  · simp [Pivot.countEQ]
  · simp [Pivot.countEQ]

private theorem countEQ_take_strict {xs : List (BitVec 64)} {pivot : BitVec 64} {i j : Nat}
    (lo : i ≤ j) (hi : j ≤ xs.length)
    (distinct : ∀ k, i ≤ k → k < j → xs[k]! ≠ pivot) :
    Pivot.countEQ (xs.take j) pivot = Pivot.countEQ (xs.take i) pivot := by
  induction j with
  | zero =>
    have eq : i = 0 := by omega
    rw [eq]
  | succ j ih =>
    by_cases eq : i = j + 1
    · rw [eq]
    · have fit : j < xs.length := by omega
      have ne : xs[j] ≠ pivot := by
        rw [← getElem!_pos xs j fit]
        exact distinct j (by omega) (by omega)
      have zero : Pivot.countEQ [xs[j]] pivot = 0 := by simp [Pivot.countEQ, ne]
      calc
        _ = Pivot.countEQ (xs.take j) pivot + Pivot.countEQ [xs[j]] pivot := by
          rw [List.take_succ_eq_append_getElem fit]
          simp only [Pivot.countEQ, List.countP_append]
        _ = _ := by
          rw [zero, Nat.add_zero]
          exact ih (by omega) (by omega) (fun k klo khi => distinct k klo (by omega))

private theorem countEQ_split (xs : List (BitVec 64)) (pivot : BitVec 64) (i : Nat) :
    Pivot.countEQ (xs.take i) pivot + Pivot.countEQ (xs.drop i) pivot =
      Pivot.countEQ xs pivot := by
  simp only [Pivot.countEQ, ← List.countP_append, List.take_append_drop]

private theorem countEQ_drop_strict {xs : List (BitVec 64)} {pivot : BitVec 64} {i j : Nat}
    (lo : i ≤ j) (hi : j ≤ xs.length)
    (distinct : ∀ k, i ≤ k → k < j → xs[k]! ≠ pivot) :
    Pivot.countEQ (xs.drop i) pivot = Pivot.countEQ (xs.drop j) pivot := by
  have h := countEQ_take_strict lo hi distinct
  have a := countEQ_split xs pivot i
  have b := countEQ_split xs pivot j
  omega

private theorem HoareInvariant.advance {rest : List (BitVec 64)} {pivot : BitVec 64}
    {i j l r swaps : Nat} (inv : HoareInvariant rest pivot i j swaps)
    (il : i ≤ l) (rj : r ≤ j) (order : l ≤ r + 1) (lfit : l ≤ rest.length)
    (left : ∀ k, i ≤ k → k < l → rest[k]!.toInt < pivot.toInt)
    (right : ∀ k, r ≤ k → k < j → pivot.toInt < rest[k]!.toInt) :
    HoareInvariant rest pivot l r swaps := by
  refine ⟨lfit, Nat.le_trans rj inv.rightFits, order, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases before : k < i
    · exact inv.leftOrder k before
    · exact Int.le_of_lt (left k (by omega) hk)
  · intro k klo khi
    by_cases after : j ≤ k
    · exact inv.rightOrder k after khi
    · exact Int.le_of_lt (right k klo (by omega))
  · rw [countEQ_take_strict il lfit (fun k a b eq => by simpa [eq] using left k a b)]
    exact inv.leftEquals
  · rw [countEQ_drop_strict rj inv.rightFits (fun k a b eq => by simpa [eq] using right k a b)]
    exact inv.rightEquals
  · have := inv.swapsLeft
    omega
  · have := inv.swapsRight
    omega

private theorem HoareInvariant.exchange {rest : List (BitVec 64)} {pivot : BitVec 64}
    {l r swaps : Nat} (inv : HoareInvariant rest pivot l (r + 1) swaps)
    (order : l ≤ r)
    (leftStop : pivot.toInt ≤ rest[l]!.toInt)
    (rightStop : rest[r]!.toInt ≤ pivot.toInt) :
    HoareInvariant (swapWords rest l r) pivot (l + 1) r (swaps + 1) := by
  have rfit := inv.rightFits
  have htake : (swapWords rest l r).take l = rest.take l := by
    unfold swapWords
    rw [List.take_set_of_le order, List.take_set_of_le (Nat.le_refl _)]
  have hdrop : (swapWords rest l r).drop (r + 1) = rest.drop (r + 1) := by
    unfold swapWords
    rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  have ls : l < (swapWords rest l r).length := by simp; omega
  have rs : r < (swapWords rest l r).length := by simp; omega
  have lval : (swapWords rest l r)[l]! = rest[r]! := by
    rw [swapWords_get (by omega)]
    by_cases eq : l = r <;> simp [eq]
  have rval : (swapWords rest l r)[r]! = rest[l]! := by
    rw [swapWords_get (by omega)]
    simp
  refine ⟨by simp; omega, by simp; omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases atLeft : k = l
    · simpa only [atLeft, lval] using rightStop
    · have fit : k < rest.length := by omega
      rw [swapWords_get fit, ite_eq_right (by omega : k ≠ r), ite_eq_right atLeft]
      exact inv.leftOrder k (by omega)
  · intro k klo khi
    by_cases atRight : k = r
    · simpa only [atRight, rval] using leftStop
    · have fit : k < rest.length := by simpa only [swapWords_length] using khi
      rw [swapWords_get fit, ite_eq_right atRight, ite_eq_right (by omega : k ≠ l)]
      exact inv.rightOrder k (by omega) fit
  · rw [List.take_succ_eq_append_getElem ls, htake]
    rw [← getElem!_pos (swapWords rest l r) l ls, lval]
    have bound := inv.leftEquals
    unfold Pivot.countEQ at bound ⊢
    rw [List.countP_append]
    simp only [List.countP_cons, List.countP_nil]
    split <;> omega
  · rw [List.drop_eq_getElem_cons rs, hdrop]
    rw [← getElem!_pos (swapWords rest l r) r rs, rval]
    have bound := inv.rightEquals
    unfold Pivot.countEQ at bound ⊢
    rw [List.countP_cons]
    split <;> omega
  · have := inv.swapsLeft; omega
  · rw [swapWords_length]
    have := inv.swapsRight
    omega

/-- The trace preserves the framed word array, and closes the invariant when
    the cursors meet or cross. This links the actual ARM64 exchanges to the
    signed ordering and duplicate counts used for the rank bound. -/
theorem partition_trace_invariant {data : BitVec 64} {m out : Memory} {i j fi fj : Nat}
    (trace : PartitionTrace data m i j out fi fj)
    {rest : List (BitVec 64)} {pivot : BitVec 64} {swaps : Nat} {frame : SepProp}
    (arr : m ⊨ (data ↦₆₄* (pivot :: rest)) ∗ frame)
    (fits : 8 * (rest.length + 1) ≤ 2^64)
    (inv : HoareInvariant rest pivot i j swaps) :
    ∃ rest' swaps', (out ⊨ (data ↦₆₄* (pivot :: rest')) ∗ frame) ∧
      rest.Perm rest' ∧ HoareInvariant rest' pivot fi fj swaps' ∧ fj ≤ fi ∧
      AgreesOutside m out data (8 * (rest.length + 1)) := by
  induction trace generalizing rest swaps with
  | @crossed m i j done overlap =>
    exact ⟨rest, swaps, arr, .refl _, inv, done, .rfl' _ _ _⟩
  | @finish m i j k il kj leftStrict rightStrict =>
    have pivotRead : m.read64 data = pivot := by
      simpa using (word_at arr (i := 0) (by simp)).1
    have wordRead (x : Nat) (hx : x < rest.length) :
        partitionWord m data x = rest[x]! := by
      simpa only [partitionWord, List.getElem!_cons_succ] using
        (word_at arr (i := x + 1) (by simpa using hx)).1
    refine ⟨rest, swaps, arr, .refl _, inv.advance il kj (by omega) ?_ ?_ ?_, by omega, .rfl' _ _ _⟩
    · exact Nat.le_trans kj inv.rightFits
    · intro x lo hi
      simpa only [pivotRead, wordRead x (by have := inv.rightFits; omega)] using leftStrict x lo hi
    · intro x lo hi
      simpa only [pivotRead, wordRead x (by have := inv.rightFits; omega)] using rightStrict x lo hi
  | @exchange m i j l r out fi fj il lr rj leftStrict rightStrict leftStop rightStop tail ih =>
    have jfit := inv.rightFits
    have lfit : l < rest.length := by omega
    have rfit : r < rest.length := by omega
    have pivotRead : m.read64 data = pivot := by
      simpa using (word_at arr (i := 0) (by simp)).1
    have wordRead (x : Nat) (hx : x < rest.length) :
        partitionWord m data x = rest[x]! := by
      simpa only [partitionWord, List.getElem!_cons_succ] using
        (word_at arr (i := x + 1) (by simpa using hx)).1
    have scanned : HoareInvariant rest pivot l (r + 1) swaps := by
      refine inv.advance il (by omega) (by omega) (by omega) ?_ ?_
      · intro x lo hi
        simpa only [pivotRead, wordRead x (by omega)] using leftStrict x lo hi
      · intro x lo hi
        simpa only [pivotRead, wordRead x (by omega)] using rightStrict x (by omega) hi
    have swapped := scanned.exchange lr
      (by simpa only [pivotRead, wordRead l lfit] using leftStop)
      (by simpa only [pivotRead, wordRead r rfit] using rightStop)
    have nextArr : partitionSwap m data l r ⊨ (data ↦₆₄* (pivot :: swapWords rest l r)) ∗ frame := by
      simpa only [partitionSwap, partitionWord, swapWords, List.getElem!_cons_succ, List.set_cons_succ] using
        swap_words arr (i := l + 1) (j := r + 1) (by simpa using lfit) (by simpa using rfit)
    obtain ⟨rest', swaps', result, perm, resultInv, done, after⟩ :=
      ih nextArr (by simpa using fits) swapped
    have before : AgreesOutside m (partitionSwap m data l r) data (8 * (rest.length + 1)) :=
      swap_words_agreesOutside m data (by omega) (by omega) fits
    rw [swapWords_length] at after
    exact ⟨rest', swaps', result, (swapWords_perm lfit rfit).trans perm, resultInv, done, before.trans after⟩

/-- A closed invariant yields both signed rank counts needed by the
    Quickselect driver. -/
theorem HoareInvariant.count_bounds {input rest : List (BitVec 64)} {pivot : BitVec 64}
    {i j swaps : Nat} (inv : HoareInvariant rest pivot i j swaps)
    (perm : input.Perm (pivot :: rest)) (crossed : j ≤ i) :
    Pivot.countLE input pivot ≤ 2 * i + 1 ∧
      Pivot.countGE input pivot ≤ 2 * (rest.length - i) + 2 := by
  refine Pivot.hoare_counts perm crossed inv.overlap inv.leftFits ?_ ?_
    inv.leftEquals inv.rightEquals inv.swapsLeft inv.swapsRight
  · intro x hx
    obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp hx
    rw [← eq, List.getElem_take, ← getElem!_pos rest k (by rw [List.length_take] at hk; omega)]
    exact inv.leftOrder k (by rw [List.length_take] at hk; omega)
  · intro x hx
    obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp hx
    have fit : j + k < rest.length := by rw [List.length_drop] at hk; omega
    rw [← eq, List.getElem_drop, ← getElem!_pos rest _ fit]
    exact inv.rightOrder _ (by omega) fit

/-- Placing the pivot at the final left cursor preserves the signed order on
    both sides, including when the pivot was already in its final slot. -/
theorem HoareInvariant.pivot_exchange_order {rest : List (BitVec 64)} {pivot : BitVec 64}
    {i j swaps : Nat} (inv : HoareInvariant rest pivot i j swaps) (crossed : j ≤ i) :
    let out := swapWords (pivot :: rest) 0 i
    out[i]! = pivot ∧
      (∀ k, k < i → out[k]!.toInt ≤ pivot.toInt) ∧
      (∀ k, i < k → k < out.length → pivot.toInt ≤ out[k]!.toInt) := by
  dsimp only
  have ilt : i < (pivot :: rest).length := by
    have fit := inv.leftFits
    simp only [List.length_cons]
    omega
  have atPos (k : Nat) (pos : 0 < k) : (pivot :: rest)[k]! = rest[k - 1]! := by
    cases k with
    | zero => omega
    | succ k => simp
  refine ⟨?_, ?_, ?_⟩
  · rw [swapWords_get ilt, ite_eq_left rfl]
    simp
  · intro k hk
    rw [swapWords_get (Nat.lt_trans hk ilt), ite_eq_right (by omega : k ≠ i)]
    by_cases kzero : k = 0
    · rw [ite_eq_left kzero, atPos i (by omega)]
      exact inv.leftOrder _ (by omega)
    · rw [ite_eq_right kzero, atPos k (by omega)]
      exact inv.leftOrder _ (by omega)
  · intro k hik hk
    rw [swapWords_length] at hk
    rw [swapWords_get hk, ite_eq_right (by omega : k ≠ i), ite_eq_right (by omega : k ≠ 0),
      atPos k (by omega)]
    simp only [List.length_cons] at hk
    exact inv.rightOrder _ (by omega) (by omega)


/-- The scan loop from the first pair of cursors to the pending final pivot
    exchange. The count is bounded both by and below in terms of the original
    gap. The upper bound excludes the initial and final pivot exchanges. -/
structure PartitionScanResult (base data : BitVec 64) (s final : State)
    (pivot : BitVec 64) (rest rest' : List (BitVec 64))
    (swaps count : Nat) (frame : SepProp) : Prop where
  steps : Example03C.CodeStepsN (program base) count s final
  pc : final.pc = base + 0x2d8#64
  running : final.status = .Running
  sp : final.sp = s.sp
  loaded : (program base).CodeLoaded final.mem
  regs : PartitionRegs s final
  array : final.mem ⊨ (data ↦₆₄* (pivot :: rest')) ∗ frame
  perm : rest.Perm rest'
  inv : HoareInvariant rest' pivot (final.readReg64 .x1).toNat (final.readReg64 (.gpr 9#5)).toNat swaps
  crossed : (final.readReg64 (.gpr 9#5)).toNat ≤ (final.readReg64 .x1).toNat
  trace : PartitionTrace data s.mem 0 rest.length final.mem
    (final.readReg64 .x1).toNat (final.readReg64 (.gpr 9#5)).toNat
  lower : rest.length ≤ count
  upper : count ≤ 24 * rest.length + 12
  outside : AgreesOutside s.mem final.mem data (8 * (rest.length + 1))
  rankLE : Pivot.countLE (pivot :: rest) pivot ≤ 2 * (final.readReg64 .x1).toNat + 1
  rankGE : Pivot.countGE (pivot :: rest) pivot ≤ 2 * (rest.length - (final.readReg64 .x1).toNat) + 2

/-- The initial pivot exchange sets the cursors to zero and the number of
    non-pivot elements. The compiled code skips straight to the right guard
    for an empty rest. Both paths preserve the framed array and establish the
    signed rank bounds before the final exchange with the pivot. -/
theorem partition_scan_correct (base data : BitVec 64) (s : State)
    (pivot : BitVec 64) (rest : List (BitVec 64)) (frame : SepProp)
    (pc : s.pc = base + (if rest = [] then 0x28c#64 else 0x258#64))
    (running : s.status = .Running) (loaded : (program base).CodeLoaded s.mem)
    (left : s.readReg64 .x1 = 0#64)
    (limit : (s.readReg64 (.gpr 8#5)).toNat = rest.length)
    (right : (s.readReg64 (.gpr 9#5)).toNat = rest.length)
    (array : s.readReg64 (.gpr 20#5) = data)
    (restBase : s.readReg64 (.gpr 23#5) = data + 8#64)
    (arr : s.mem ⊨ (data ↦₆₄* (pivot :: rest)) ∗ frame)
    (fits : 8 * (rest.length + 1) ≤ 2^64) :
    ∃ count final rest' swaps, PartitionScanResult base data s final pivot rest rest' swaps count frame := by
  have start := hoareInvariant_start rest pivot
  have leftNat : (s.readReg64 .x1).toNat = 0 := by simp [left]
  cases rest with
  | nil =>
    simp only [List.length_nil] at right
    have guardPC : s.pc = base + 0x28c#64 := by simpa using pc
    obtain ⟨final, steps, frun, fmem, fsp, fregs, fi, _, fj, _, _, fpc⟩ :=
      partition_right_guard base s guardPC running loaded
    rw [leftNat, right] at fpc
    simp at fpc
    have inv : HoareInvariant [] pivot (final.readReg64 .x1).toNat
        (final.readReg64 (.gpr 9#5)).toNat 0 := by
      rw [fi, fj, leftNat, right]
      exact start
    have crossed : (final.readReg64 (.gpr 9#5)).toNat ≤ (final.readReg64 .x1).toNat := by
      simp [fi, fj, leftNat, right]
    have trace : PartitionTrace data s.mem 0 0 final.mem
        (final.readReg64 .x1).toNat (final.readReg64 (.gpr 9#5)).toNat := by
      rw [fmem, fi, fj, leftNat, right]
      exact .crossed (by simp) (by simp)
    have ranks := inv.count_bounds (.refl (pivot :: [])) crossed
    exact ⟨2, final, [], 0, ⟨steps, fpc, frun, fsp, fmem.symm ▸ loaded, fregs, fmem.symm ▸ arr,
      .refl _, inv, crossed, trace, by simp, by decide, fmem.symm ▸ .rfl' _ _ _, ranks.1, ranks.2⟩⟩
  | cons x xs =>
    have scanPC : s.pc = base + 0x258#64 := by simpa using pc
    have openInterval : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 9#5)).toNat := by
      simp [leftNat, right]
    have buffer : ScanBuffer s := by
      intro k hk
      rw [limit] at hk
      rw [array, ← wordAddr_shift]
      exact (word_at arr (i := k.toNat) (by simp only [List.length_cons] at hk ⊢; omega)).2
    obtain ⟨count, final, steps, fpc, frun, fsp, floaded, _, _, _, _, upper, lower, fregs, trace⟩ :=
      partition_scan_loop base s scanPC running loaded openInterval (by simp only [right, limit, Nat.le_refl])
        (by rw [array, restBase]) buffer
    rw [array, leftNat, right] at trace
    obtain ⟨rest', swaps, result, perm, inv, crossed, outside⟩ :=
      partition_trace_invariant trace arr fits start
    have ranks := inv.count_bounds (perm.cons pivot) crossed
    refine ⟨count, final, rest', swaps, ⟨steps, fpc, frun, fsp, floaded, fregs, result, perm,
      inv, crossed, trace, ?_, ?_, outside, ranks.1, ?_⟩⟩
    · simpa only [leftNat, right, Nat.sub_zero] using lower
    · simpa only [leftNat, right, Nat.sub_zero] using upper
    · simpa only [← perm.length_eq] using ranks.2


end Example04Rust
