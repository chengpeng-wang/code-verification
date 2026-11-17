import QuickselectAdversaryPivot
import QuickselectArray

namespace Example04Rust.Adversary

open Pivot

set_option autoImplicit false

/-- The cursor modes of the two strict Hoare scans. Both cursors below are
    indices in the whole slice, with the right endpoint excluded. -/
inductive Phase
  | left
  | right

/-- The source-level partition trace before the last exchange of the pivot.
    A successful probe advances just its cursor. A failed left probe starts
    the right scan. When both probes stop inside the interval, the exchange
    advances both cursors. -/
inductive Scan (pivot : Word) : Phase → List Word → Nat → Nat → List Word → Nat → Prop
  | leftAdvance {xs ys : List Word} {i j split : Nat}
      (openInterval : i < j) (below : xs[i]!.toInt < pivot.toInt)
      (tail : Scan pivot .left xs (i + 1) j ys split) : Scan pivot .left xs i j ys split
  | rightStart {xs ys : List Word} {i j split : Nat}
      (stop : j ≤ i ∨ pivot.toInt ≤ xs[i]!.toInt)
      (tail : Scan pivot .right xs i j ys split) : Scan pivot .left xs i j ys split
  | rightAdvance {xs ys : List Word} {i j split : Nat}
      (openInterval : i < j) (above : pivot.toInt < xs[j - 1]!.toInt)
      (tail : Scan pivot .right xs i (j - 1) ys split) : Scan pivot .right xs i j ys split
  | exchange {xs ys : List Word} {i j split : Nat}
      (openInterval : i < j) (below : xs[j - 1]!.toInt ≤ pivot.toInt)
      (tail : Scan pivot .left (swapWords xs i (j - 1)) (i + 1) (j - 1) ys split) :
      Scan pivot .right xs i j ys split
  | done {xs : List Word} {i j : Nat} (crossed : j ≤ i) :
      Scan pivot .right xs i j xs (i - 1)

private def remaining (phase : Phase) (i j : Nat) : Nat :=
  2 * (j - i) + match phase with | .left => 1 | .right => 0

theorem Scan.exists_run (pivot : Word) (phase : Phase) (xs : List Word) (i j : Nat) :
    ∃ ys split, Scan pivot phase xs i j ys split := by
  generalize hd : remaining phase i j = d
  induction d using Nat.strongRecOn generalizing phase xs i j with
  | ind d ih =>
    cases phase with
    | left =>
      by_cases hi : i < j
      · by_cases low : xs[i]!.toInt < pivot.toInt
        · have dec : remaining .left (i + 1) j < d := by simp [remaining] at hd ⊢; omega
          obtain ⟨ys, split, tail⟩ := ih _ dec .left xs (i + 1) j rfl
          exact ⟨ys, split, .leftAdvance hi low tail⟩
        · have dec : remaining .right i j < d := by simp [remaining] at hd ⊢; omega
          obtain ⟨ys, split, tail⟩ := ih _ dec .right xs i j rfl
          exact ⟨ys, split, .rightStart (Or.inr (Int.le_of_not_gt low)) tail⟩
      · have dec : remaining .right i j < d := by simp [remaining] at hd ⊢; omega
        obtain ⟨ys, split, tail⟩ := ih _ dec .right xs i j rfl
        exact ⟨ys, split, .rightStart (Or.inl (by omega)) tail⟩
    | right =>
      by_cases hi : i < j
      · by_cases high : pivot.toInt < xs[j - 1]!.toInt
        · have dec : remaining .right i (j - 1) < d := by simp [remaining] at hd ⊢; omega
          obtain ⟨ys, split, tail⟩ := ih _ dec .right xs i (j - 1) rfl
          exact ⟨ys, split, .rightAdvance hi high tail⟩
        · have dec : remaining .left (i + 1) (j - 1) < d := by simp [remaining] at hd ⊢; omega
          obtain ⟨ys, split, tail⟩ := ih _ dec .left (swapWords xs i (j - 1)) (i + 1) (j - 1) rfl
          exact ⟨ys, split, .exchange hi (Int.le_of_not_gt high) tail⟩
      · exact ⟨xs, i - 1, .done (by omega)⟩

/-- The order facts maintained by the scans. The right mode remembers that
    the left cursor stopped on a word at least as large as the pivot. -/
structure ScanInvariant (pivot : Word) (phase : Phase) (xs : List Word) (i j : Nat) : Prop where
  first : 0 < i
  leftFits : i ≤ xs.length
  rightFits : j ≤ xs.length
  pivotAtZero : xs[0]! = pivot
  leftOrder : ∀ k, 0 < k → k < i → xs[k]!.toInt ≤ pivot.toInt
  rightOrder : ∀ k, j ≤ k → k < xs.length → pivot.toInt ≤ xs[k]!.toInt
  leftStopped : phase = .right → i < j → pivot.toInt ≤ xs[i]!.toInt

/-- Ordering facts just before the last exchange of the pivot. -/
structure Scanned (pivot : Word) (input xs : List Word) (split : Nat) : Prop where
  perm : input.Perm xs
  fits : split < xs.length
  pivotAtZero : xs[0]! = pivot
  leftOrder : ∀ k, 0 < k → k ≤ split → xs[k]!.toInt ≤ pivot.toInt
  rightOrder : ∀ k, split < k → k < xs.length → pivot.toInt ≤ xs[k]!.toInt

theorem Scan.scanned {pivot : Word} {phase : Phase} {xs ys : List Word} {i j split : Nat}
    (run : Scan pivot phase xs i j ys split) (inv : ScanInvariant pivot phase xs i j) :
    Scanned pivot xs ys split := by
  induction run with
  | @leftAdvance xs ys i j split openInterval below _ ih =>
    apply ih
    refine ⟨by omega, by have := inv.rightFits; omega, inv.rightFits, inv.pivotAtZero, ?_,
      inv.rightOrder, by simp⟩
    intro k positive hk
    by_cases h : k < i
    · exact inv.leftOrder k positive h
    · have eq : k = i := by omega
      rw [eq]
      exact Int.le_of_lt below
  | rightStart stop _ ih =>
    apply ih
    exact ⟨inv.first, inv.leftFits, inv.rightFits, inv.pivotAtZero, inv.leftOrder, inv.rightOrder,
      fun _ hi => stop.elim (fun closed => (Nat.not_le_of_lt hi closed).elim) id⟩
  | @rightAdvance xs ys i j split openInterval above _ ih =>
    apply ih
    refine ⟨inv.first, inv.leftFits, Nat.le_trans (Nat.sub_le ..) inv.rightFits, inv.pivotAtZero,
      inv.leftOrder, ?_, fun phase hi => inv.leftStopped phase (by omega)⟩
    intro k hk fit
    by_cases h : j ≤ k
    · exact inv.rightOrder k h fit
    · have eq : k = j - 1 := by omega
      rw [eq]
      exact Int.le_of_lt above
  | @exchange xs ys i j split openInterval below _ ih =>
    have ipos := inv.first
    have fits := inv.rightFits
    have hi : i < xs.length := by omega
    have hj : j - 1 < xs.length := by omega
    have after := ih (by
      refine ⟨by omega, by simp; omega, by simp; omega, ?_, ?_, ?_, by simp⟩
      · rw [swapWords_get (by omega : 0 < xs.length)]
        simp [show 0 ≠ i by omega, show 0 ≠ j - 1 by omega, inv.pivotAtZero]
      · intro k positive hk
        have hk' : k < xs.length := by omega
        rw [swapWords_get hk']
        split
        · rename_i heq
          by_cases same : i = j - 1
          · simpa only [same] using below
          · omega
        · split
          · exact below
          · exact inv.leftOrder k positive (by omega)
      · intro k hk fit
        have fit' : k < xs.length := by simpa using fit
        rw [swapWords_get fit']
        split
        · exact inv.leftStopped rfl openInterval
        · split
          · omega
          · exact inv.rightOrder k (by omega) fit')
    exact { after with perm := (swapWords_perm hi hj).trans after.perm }
  | done closed =>
    exact ⟨List.Perm.refl _, by have := inv.first; have := inv.leftFits; omega, inv.pivotAtZero,
      fun k positive hk => inv.leftOrder k positive (by have := inv.first; omega),
      fun k hk fit => inv.rightOrder k (by omega) fit⟩

/-- A complete source Hoare partition, including both exchanges of the pivot. -/
structure Partition (input output : List Word) (index split : Nat) : Prop where
  indexFits : index < input.length
  scan : ∃ scanned, Scan input[index]! .left (swapWords input 0 index) 1 input.length scanned split ∧
    output = swapWords scanned 0 split

/-- Output observations of a source partition. -/
structure PartitionResult (input output : List Word) (pivot : Word) (split : Nat) : Prop where
  perm : input.Perm output
  fits : split < output.length
  pivotAtSplit : output[split]! = pivot
  leftOrder : ∀ k < split, output[k]!.toInt ≤ pivot.toInt
  rightOrder : ∀ k, split < k → k < output.length → pivot.toInt ≤ output[k]!.toInt

theorem Partition.exists_run (input : List Word) (index : Nat) (fits : index < input.length) :
    ∃ output split, Partition input output index split := by
  obtain ⟨scanned, split, run⟩ :=
    Scan.exists_run input[index]! .left (swapWords input 0 index) 1 input.length
  exact ⟨swapWords scanned 0 split, split, ⟨fits, scanned, run, rfl⟩⟩

theorem Partition.result {input output : List Word} {index split : Nat}
    (run : Partition input output index split) : PartitionResult input output input[index]! split := by
  obtain ⟨fits, scanned, trace, rfl⟩ := run
  have h0 : 0 < input.length := by omega
  have done := trace.scanned (by
    refine ⟨by decide, by simpa using (Nat.succ_le_of_lt h0), by simp, ?_, by omega, by intro k hk h; simp at h; omega, by simp⟩
    rw [swapWords_get h0]
    by_cases h : 0 = index
    · simp [h]
    · simp [h])
  have hs := done.fits
  have positive : 0 < scanned.length := by omega
  refine ⟨((swapWords_perm h0 fits).trans done.perm).trans (swapWords_perm positive hs),
    by simpa using hs, ?_, ?_, ?_⟩
  · rw [swapWords_get hs, ite_eq_left rfl, done.pivotAtZero]
  · intro k hk
    rw [swapWords_get (by omega : k < scanned.length), ite_eq_right (by omega)]
    by_cases zero : k = 0
    · rw [ite_eq_left zero]
      by_cases splitZero : split = 0
      · omega
      · exact done.leftOrder split (by omega) (Nat.le_refl _)
    · rw [ite_eq_right zero]
      exact done.leftOrder k (by omega) (by omega)
  · intro k hk fit
    have fit' : k < scanned.length := by simpa using fit
    rw [swapWords_get fit', ite_eq_right (by omega), ite_eq_right (by omega)]
    exact done.rightOrder k hk fit'


private theorem get_mem {xs : List Word} {i : Nat} (fit : i < xs.length) : xs[i]! ∈ xs := by
  rw [getElem!_pos xs i fit]
  exact List.getElem_mem _

theorem get_map (f : Word → Word) {xs : List Word} {i : Nat} (fit : i < xs.length) :
    (xs.map f)[i]! = f (xs[i]!) := by
  have fitMap : i < (xs.map f).length := by simpa using fit
  rw [getElem!_pos (xs.map f) i fitMap, getElem!_pos xs i fit, List.getElem_map]

private theorem swap_map (f : Word → Word) {xs : List Word} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    (swapWords xs i j).map f = swapWords (xs.map f) i j := by
  simp only [swapWords, List.map_set, get_map f hi, get_map f hj]

/-- The comparisons against the pivot determine the Hoare swaps. Reassigning
    values within either strict side of the pivot preserves those comparisons. -/
def PreservesPivot (pivot : Word) (f : Word → Word) (xs : List Word) : Prop :=
  ∀ x ∈ xs,
    ((f x).toInt < (f pivot).toInt ↔ x.toInt < pivot.toInt) ∧
      ((f pivot).toInt < (f x).toInt ↔ pivot.toInt < x.toInt)

private theorem PreservesPivot.perm {pivot : Word} {f : Word → Word} {xs ys : List Word}
    (preserve : PreservesPivot pivot f xs) (perm : xs.Perm ys) : PreservesPivot pivot f ys :=
  fun x hx => preserve x (perm.mem_iff.mpr hx)

theorem Scan.map {pivot : Word} {phase : Phase} {xs ys : List Word} {i j split : Nat}
    (run : Scan pivot phase xs i j ys split) (fit : j ≤ xs.length) (f : Word → Word)
    (preserve : PreservesPivot pivot f xs) :
    Scan (f pivot) phase (xs.map f) i j (ys.map f) split := by
  induction run with
  | @leftAdvance xs ys i j split openInterval below _ ih =>
    apply Scan.leftAdvance openInterval _ (ih fit preserve)
    have hi : i < xs.length := by omega
    rw [get_map f hi]
    exact (preserve _ (get_mem hi)).1.mpr below
  | @rightStart xs ys i j split stop _ ih =>
    apply Scan.rightStart _ (ih fit preserve)
    by_cases hi : i < j
    · have hf : i < xs.length := by omega
      refine Or.inr (Int.le_of_not_gt ?_)
      change ¬(xs.map f)[i]!.toInt < (f pivot).toInt
      rw [get_map f hf, (preserve _ (get_mem hf)).1]
      exact Int.not_lt_of_ge (stop.resolve_left (by omega))
    · exact Or.inl (by omega)
  | @rightAdvance xs ys i j split openInterval above _ ih =>
    apply Scan.rightAdvance openInterval _ (ih (by omega) preserve)
    have hj : j - 1 < xs.length := by omega
    rw [get_map f hj]
    exact (preserve _ (get_mem hj)).2.mpr above
  | @exchange xs ys i j split openInterval below _ ih =>
    have hi : i < xs.length := by omega
    have hj : j - 1 < xs.length := by omega
    refine Scan.exchange openInterval ?_ ?_
    · apply Int.le_of_not_gt
      change ¬(f pivot).toInt < (xs.map f)[j - 1]!.toInt
      rw [get_map f hj, (preserve _ (get_mem hj)).2]
      exact Int.not_lt_of_ge below
    · rw [← swap_map f hi hj]
      exact ih (by simp; omega) (preserve.perm (swapWords_perm hi hj))
  | done crossed => exact Scan.done crossed

theorem Scan.deterministic {pivot : Word} {phase : Phase} {xs ys zs : List Word}
    {i j p q : Nat} (first : Scan pivot phase xs i j ys p)
    (second : Scan pivot phase xs i j zs q) : ys = zs ∧ p = q := by
  induction first generalizing zs q with
  | leftAdvance openInterval below _ ih =>
    cases second with
    | leftAdvance _ _ tail => exact ih tail
    | rightStart stop _ => rcases stop with h | h <;> omega
  | rightStart stop _ ih =>
    cases second with
    | leftAdvance openInterval below _ => rcases stop with h | h <;> omega
    | rightStart _ tail => exact ih tail
  | rightAdvance openInterval above _ ih =>
    cases second with
    | rightAdvance _ _ tail => exact ih tail
    | exchange _ below _ => omega
    | done crossed => omega
  | exchange openInterval below _ ih =>
    cases second with
    | rightAdvance _ above _ => omega
    | exchange _ _ tail => exact ih tail
    | done crossed => omega
  | done crossed =>
    cases second with
    | rightAdvance openInterval _ _ => omega
    | exchange openInterval _ _ => omega
    | done _ => exact ⟨rfl, rfl⟩

theorem Partition.deterministic {input output output' : List Word} {index split split' : Nat}
    (first : Partition input output index split) (second : Partition input output' index split') :
    output = output' ∧ split = split' := by
  obtain ⟨_, scanned, firstTrace, rfl⟩ := first
  obtain ⟨_, scanned', secondTrace, rfl⟩ := second
  obtain ⟨rfl, rfl⟩ := firstTrace.deterministic secondTrace
  exact ⟨rfl, rfl⟩

theorem Partition.map {input output : List Word} {index split : Nat}
    (run : Partition input output index split) (f : Word → Word)
    (preserve : PreservesPivot input[index]! f input) :
    Partition (input.map f) (output.map f) index split := by
  have result := run.result
  obtain ⟨hIndex, scanned, trace, rfl⟩ := run
  have positive : 0 < input.length := by omega
  have splitFit : split < scanned.length := by simpa using result.fits
  have positiveScanned : 0 < scanned.length := by omega
  refine ⟨by simpa using hIndex, scanned.map f, ?_, ?_⟩
  · rw [get_map f hIndex, List.length_map, ← swap_map f positive hIndex]
    exact trace.map (by simp) f (preserve.perm (swapWords_perm positive hIndex))
  · exact swap_map f positiveScanned splitFit

theorem PartitionResult.right_strict {input output : List Word} {pivot : Word} {split : Nat}
    (result : PartitionResult input output pivot split) (distinct : input.Nodup)
    {i : Nat} (hi : split < i) (fit : i < output.length) :
    pivot.toInt < output[i]!.toInt := by
  have le := result.rightOrder i hi fit
  have neq : output[i]! ≠ pivot := by
    intro eq
    have same := ((distinct.perm result.perm).getElem!_inj fit result.fits).mp
      (eq.trans result.pivotAtSplit.symm)
    omega
  by_cases lt : pivot.toInt < output[i]!.toInt
  · exact lt
  · exact (neq (BitVec.toInt_inj.mp (by omega))).elim

theorem PartitionResult.split_eq_rank {input output : List Word} {pivot : Word} {split : Nat}
    (result : PartitionResult input output pivot split) (distinct : input.Nodup) :
    countLE input pivot = split + 1 := by
  let pred := fun x : Word => decide (x.toInt ≤ pivot.toInt)
  change input.countP pred = split + 1
  rw [result.perm.countP_eq pred, ← List.take_append_drop (split + 1) output, List.countP_append]
  have low : (output.take (split + 1)).countP pred = (output.take (split + 1)).length := by
    apply List.countP_eq_length.mpr
    intro x hx
    obtain ⟨k, fit, rfl⟩ := List.mem_iff_getElem.mp hx
    have hlen := result.fits
    have fit' : k < output.length := by
      have := List.length_take_le (split + 1) output
      simp only [List.length_take] at fit
      omega
    rw [List.getElem_take]
    change decide (output[k].toInt ≤ pivot.toInt) = true
    rw [← getElem!_pos output k fit']
    apply decide_eq_true
    have kle : k ≤ split := by
      simp only [List.length_take] at fit
      omega
    by_cases h : k = split
    · rw [h, result.pivotAtSplit]
      exact Int.le_refl _
    · exact result.leftOrder k (by omega)
  have high : (output.drop (split + 1)).countP pred = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    obtain ⟨k, fit, rfl⟩ := List.mem_iff_getElem.mp hx
    have fit' : split + 1 + k < output.length := by
      simp only [List.length_drop] at fit
      omega
    rw [List.getElem_drop]
    change ¬decide (output[split + 1 + k].toInt ≤ pivot.toInt) = true
    rw [← getElem!_pos output (split + 1 + k) fit', decide_eq_true_eq]
    exact Int.not_le_of_gt (result.right_strict distinct (by omega) fit')
  rw [low, high, List.length_take, Nat.min_eq_left (by have := result.fits; omega), Nat.add_zero]

end Example04Rust.Adversary
