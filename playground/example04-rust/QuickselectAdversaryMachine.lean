import QuickselectAdversary
import QuickselectPartitionScan

namespace Example04Rust.Adversary

open Arm64 ProofLib Pivot

set_option autoImplicit false

private theorem Scan.left_prefix {pivot : Word} {xs ys : List Word} {i k j split : Nat}
    (ik : i ≤ k) (kj : k ≤ j)
    (strict : ∀ x, i ≤ x → x < k → xs[x]!.toInt < pivot.toInt)
    (tail : Scan pivot .left xs k j ys split) : Scan pivot .left xs i j ys split := by
  generalize hd : k - i = d
  induction d using Nat.strongRecOn generalizing i with
  | ind d ih =>
    by_cases h : i = k
    · subst i
      exact tail
    · have small : k - (i + 1) < d := by omega
      exact .leftAdvance (by omega) (strict i (by omega) (by omega))
        (ih _ small (i := i + 1) (by omega) (fun x lo hi => strict x (by omega) hi) rfl)

private theorem Scan.right_suffix {pivot : Word} {xs ys : List Word} {i k j split : Nat}
    (kj : k ≤ j) (ik : i ≤ k)
    (strict : ∀ x, k ≤ x → x < j → pivot.toInt < xs[x]!.toInt)
    (tail : Scan pivot .right xs i k ys split) : Scan pivot .right xs i j ys split := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases h : j = k
    · subst j
      exact tail
    · exact .rightAdvance (by omega) (strict (j - 1) (by omega) (by omega))
        (ih (j - 1) (by omega) (by omega) (fun x lo hi => strict x lo (by omega)))

/-- Expand the machine's grouped scans into the comparison-level source
    trace. The memory trace counts indices after the pivot; the source
    trace counts indices in the entire active slice. -/
theorem partition_trace_scan {data : BitVec 64} {m out : Memory} {i j fi fj : Nat}
    (trace : PartitionTrace data m i j out fi fj)
    {xs : List Word} {frame : SepProp}
    (arr : m ⊨ (data ↦₆₄* xs) ∗ frame)
    (leftFits : i + 1 ≤ xs.length) (rightFits : j + 1 ≤ xs.length) :
    ∃ ys, (out ⊨ (data ↦₆₄* ys) ∗ frame) ∧
      Scan xs[0]! .left xs (i + 1) (j + 1) ys fi := by
  induction trace generalizing xs with
  | @crossed m i j done overlap =>
    exact ⟨xs, arr, .rightStart (.inl (by omega)) (.done (by omega))⟩
  | @finish m i j k il kj leftStrict rightStrict =>
    have pivotRead : m.read64 data = xs[0]! := by
      simpa using (word_at arr (i := 0) (by omega)).1
    have leftFull (x : Nat) (lo : i + 1 ≤ x) (hi : x < k + 1) : xs[x]!.toInt < xs[0]!.toInt := by
      have h := leftStrict (x - 1) (by omega) (by omega)
      have read := (word_at arr (i := (x - 1) + 1) (by omega)).1
      unfold partitionWord at h
      rw [read, pivotRead] at h
      simpa only [show x - 1 + 1 = x by omega] using h
    have rightFull (x : Nat) (lo : k + 1 ≤ x) (hi : x < j + 1) :
        xs[0]!.toInt < xs[x]!.toInt := by
      have h := rightStrict (x - 1) (by omega) (by omega)
      have read := (word_at arr (i := (x - 1) + 1) (by omega)).1
      unfold partitionWord at h
      rw [read, pivotRead] at h
      simpa only [show x - 1 + 1 = x by omega] using h
    have stop : j + 1 ≤ k + 1 ∨ xs[0]!.toInt ≤ xs[k + 1]!.toInt := by
      by_cases closed : j ≤ k
      · exact .inl (by omega)
      · exact .inr (Int.le_of_lt (rightFull (k + 1) (by omega) (by omega)))
    have meet : Scan xs[0]! .right xs (k + 1) (k + 1) xs k :=
      .done (Nat.le_refl _)
    exact ⟨xs, arr, .left_prefix (by omega) (by omega) leftFull
      (.rightStart stop (.right_suffix (by omega) (Nat.le_refl _) rightFull meet))⟩
  | @exchange m i j l r out fi fj il lr rj leftStrict rightStrict leftStop rightStop tail ih =>
    let ys := swapWords xs (l + 1) (r + 1)
    have lfit : l + 1 < xs.length := by omega
    have rfit : r + 1 < xs.length := by omega
    have pos : 0 < xs.length := by omega
    have pivotRead : m.read64 data = xs[0]! := by
      simpa using (word_at arr (i := 0) pos).1
    have read (x : Nat) (hx : x + 1 < xs.length) : partitionWord m data x = xs[x + 1]! :=
      (word_at arr hx).1
    have nextArr : partitionSwap m data l r ⊨ (data ↦₆₄* ys) ∗ frame :=
      swap_words arr lfit rfit
    have nextPivot : ys[0]! = xs[0]! := by
      rw [show ys = swapWords xs (l + 1) (r + 1) from rfl, swapWords_get pos]
      simp
    have ylen : ys.length = xs.length := swapWords_length ..
    obtain ⟨zs, mem, next⟩ := ih nextArr (by rw [ylen]; omega) (by rw [ylen]; omega)
    rw [nextPivot] at next
    have leftFull (x : Nat) (lo : i + 1 ≤ x) (hi : x < l + 1) :
        xs[x]!.toInt < xs[0]!.toInt := by
      have h := leftStrict (x - 1) (by omega) (by omega)
      simpa only [pivotRead, read (x - 1) (by omega), show x - 1 + 1 = x by omega] using h
    have rightFull (x : Nat) (lo : r + 2 ≤ x) (hi : x < j + 1) :
        xs[0]!.toInt < xs[x]!.toInt := by
      have h := rightStrict (x - 1) (by omega) (by omega)
      simpa only [pivotRead, read (x - 1) (by omega), show x - 1 + 1 = x by omega] using h
    have leftOrder : xs[0]!.toInt ≤ xs[l + 1]!.toInt := by
      simpa only [pivotRead, read l lfit] using leftStop
    have rightOrder : xs[r + 1]!.toInt ≤ xs[0]!.toInt := by
      simpa only [pivotRead, read r rfit] using rightStop
    have exchange : Scan xs[0]! .right xs (l + 1) (r + 2) zs fi :=
      .exchange (by omega) rightOrder next
    exact ⟨zs, mem, .left_prefix (by omega) (by omega) leftFull
      (.rightStart (.inr leftOrder) (.right_suffix (by omega) (by omega) rightFull exchange))⟩

private theorem words_equal {m : Memory} {data : BitVec 64} {xs ys : List Word}
    {frame frame' : SepProp} (left : m ⊨ (data ↦₆₄* xs) ∗ frame)
    (right : m ⊨ (data ↦₆₄* ys) ∗ frame') (length : xs.length = ys.length) : xs = ys := by
  apply List.ext_getElem length
  intro i hxs hys
  rw [← getElem!_pos xs i hxs, ← getElem!_pos ys i hys]
  exact (word_at left hxs).1.symm.trans (word_at right hys).1

/-- The actual scan in the linked binary is a source Hoare partition once
    combined with the first and last swaps of the pivot. -/
theorem partition_trace_partition {data : BitVec 64} {m out : Memory}
    {xs scanned : List Word} {p split right : Nat} {frame frame' : SepProp}
    (pFits : p < xs.length) (trace : PartitionTrace data m 0 (xs.length - 1) out split right)
    (before : m ⊨ (data ↦₆₄* swapWords xs 0 p) ∗ frame)
    (after : out ⊨ (data ↦₆₄* scanned) ∗ frame') (length : scanned.length = xs.length) :
    Partition xs (swapWords scanned 0 split) p split := by
  have pos : 0 < xs.length := by omega
  have rightFits : xs.length - 1 + 1 ≤ (swapWords xs 0 p).length := by
    simp only [swapWords_length]
    omega
  have leftFits : 0 + 1 ≤ (swapWords xs 0 p).length := by simp; omega
  obtain ⟨ys, mem, run⟩ := partition_trace_scan trace before leftFits rightFits
  have pivot : (swapWords xs 0 p)[0]! = xs[p]! := by
    rw [swapWords_get pos]
    by_cases h : 0 = p <;> simp [h]
  have j : xs.length - 1 + 1 = xs.length := by omega
  rw [pivot, j] at run
  have result := run.scanned (by
    refine ⟨by decide, by simpa using (Nat.succ_le_of_lt pos), by simp, pivot,
      by omega, ?_, by simp⟩
    intro k lo hi
    rw [swapWords_length] at hi
    omega)
  have len : ys.length = scanned.length := by
    rw [← result.perm.length_eq, swapWords_length, length]
  rw [words_equal mem after len] at run
  exact ⟨pFits, scanned, run, rfl⟩

end Example04Rust.Adversary
