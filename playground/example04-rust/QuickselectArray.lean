import ProofLib.SepLogic.SliceArray

namespace Example04Rust

open Arm64 ProofLib

set_option autoImplicit false

/-- The address of word index `i` in an i64 slice. -/
def wordAddr (data : BitVec 64) (i : Nat) : BitVec 64 :=
  data + BitVec.ofNat 64 (8 * i)

@[simp]
theorem wordAddr_zero (data : BitVec 64) : wordAddr data 0 = data := by
  simp [wordAddr]

theorem wordAddr_add (data : BitVec 64) (i j : Nat) :
    wordAddr (wordAddr data i) j = wordAddr data (i + j) := by
  simp [wordAddr, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem wordAddr_shift (data : BitVec 64) (i : BitVec 64) :
    wordAddr data i.toNat = data + (i <<< 3) := by
  unfold wordAddr
  congr 1
  change BitVec.ofNat 64 (8 * i.toNat) = BitVec.ofNat 64 (i.toNat <<< 3)
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem wordAddr_succ_shift (data : BitVec 64) (i : BitVec 64) :
    wordAddr data (i.toNat + 1) = data + ((i <<< 3) + 8#64) := by
  rw [← wordAddr_add, wordAddr, wordAddr_shift, BitVec.add_assoc]


/-- Read access, write access and the decoded word of a framed array cell. -/
theorem word_at {m : Memory} {data : BitVec 64} {xs : List (BitVec 64)} {frame : SepProp}
    (arr : m ⊨ (data ↦₆₄* xs) ∗ frame) {i : Nat} (hi : i < xs.length) :
    m.read64 (wordAddr data i) = xs[i]! ∧
      m.canRead (wordAddr data i) 8 = true ∧ m.canWrite (wordAddr data i) 8 = true := by
  rw [pointsToWords64_eq_pointsToArray, pointsToArray_focus _ _ _ _ _ hi, sepConj_assoc] at arr
  have block := IsBlock.pointsTo64 (wordAddr data i) (xs.getD i default)
  rw [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  exact ⟨block.read arr, block.canRead (by decide) arr, block.canWrite (by decide) arr⟩

/-- A store replaces one word and preserves the disjoint frame. -/
theorem write_word {m : Memory} {data : BitVec 64} {xs : List (BitVec 64)} {frame : SepProp}
    (arr : m ⊨ (data ↦₆₄* xs) ∗ frame) {i : Nat} (hi : i < xs.length) (v : BitVec 64) :
    m.write64 (wordAddr data i) v ⊨ (data ↦₆₄* xs.set i v) ∗ frame := by
  rw [pointsToWords64_eq_pointsToArray, pointsToArray_focus _ _ _ _ _ hi, sepConj_assoc] at arr
  rw [pointsToWords64_eq_pointsToArray, ← pointsToArray_update _ _ _ _ _ _ hi, sepConj_assoc]
  exact (IsBlock.pointsTo64 (wordAddr data i) (xs.getD i default)).update
    (IsBlock.pointsTo64 (wordAddr data i) v) (Nat.le_refl _) arr
    ((AgreesOutside.rfl' m (wordAddr data i) 8).write64 (by simp) (by decide))
    (Memory.read64_write64_same m (wordAddr data i) v)

/-- Swap two indexed words, reading both old values before either write. -/
def swapWords (xs : List (BitVec 64)) (i j : Nat) : List (BitVec 64) :=
  (xs.set i xs[j]!).set j xs[i]!

@[simp]
theorem swapWords_length (xs : List (BitVec 64)) (i j : Nat) :
    (swapWords xs i j).length = xs.length := by simp [swapWords]

theorem swap_words {m : Memory} {data : BitVec 64} {xs : List (BitVec 64)} {frame : SepProp}
    (arr : m ⊨ (data ↦₆₄* xs) ∗ frame) {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) :
    ((m.write64 (wordAddr data i) (m.read64 (wordAddr data j))).write64
      (wordAddr data j) (m.read64 (wordAddr data i))) ⊨ (data ↦₆₄* swapWords xs i j) ∗ frame := by
  rw [(word_at arr hi).1, (word_at arr hj).1]
  exact write_word (write_word arr hi _) (by simpa using hj) _

theorem swapWords_get {xs : List (BitVec 64)} {i j k : Nat} (hk : k < xs.length) :
    (swapWords xs i j)[k]! =
      if k = j then xs[i]! else if k = i then xs[j]! else xs[k]! := by
  unfold swapWords
  have h2 : k < ((xs.set i xs[j]!).set j xs[i]!).length := by simpa using hk
  rw [getElem!_pos _ k h2]
  rw [List.getElem_set, List.getElem_set]
  rw [getElem!_pos xs k hk]
  simp only [eq_comm (a := i) (b := k), eq_comm (a := j) (b := k)]

private theorem perm_set_cons (v : BitVec 64) (ys : List (BitVec 64)) (j : Nat)
    (hj : j < ys.length) :
    (v :: ys).Perm (ys[j]! :: ys.set j v) := by
  induction ys generalizing j with
  | nil => simp at hj
  | cons x ys ih =>
    cases j with
    | zero => simpa using List.Perm.swap x v ys
    | succ j =>
      have hj' : j < ys.length := by simp at hj; omega
      simpa only [List.getElem!_cons_succ, List.set_cons_succ] using
        (List.Perm.swap x v ys).trans (((ih j hj').cons x).trans (List.Perm.swap ys[j]! x (ys.set j v)))

theorem swapWords_perm {xs : List (BitVec 64)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) : xs.Perm (swapWords xs i j) := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    cases i <;> cases j
    · simp [swapWords]
    · next j =>
      have hj' : j < xs.length := by simp at hj; omega
      simpa [swapWords] using perm_set_cons x xs j hj'
    · next i =>
      have hi' : i < xs.length := by simp at hi; omega
      simpa [swapWords] using perm_set_cons x xs i hi'
    · next i j =>
      have hi' : i < xs.length := by simp at hi; omega
      have hj' : j < xs.length := by simp at hj; omega
      simpa [swapWords] using (ih hi' hj').cons x

/-- Swapping within an array preserves bytes and permissions outside it. -/
theorem swap_words_agreesOutside (m : Memory) (data : BitVec 64) {n i j : Nat}
    (hi : i < n) (hj : j < n) (hn : 8 * n ≤ 2^64) :
    AgreesOutside m ((m.write64 (wordAddr data i) (m.read64 (wordAddr data j))).write64
      (wordAddr data j) (m.read64 (wordAddr data i))) data (8 * n) := by
  have hword (k : Nat) (hk : k < n) : (wordAddr data k - data).toNat + 8 ≤ 8 * n := by
    simp only [wordAddr, BitVec.add_comm data _, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 8 * k < 2^64)]
    omega
  exact ((AgreesOutside.rfl' m data (8 * n)).write64 (hword i hi) hn).write64 (hword j hj) hn


/-- Use the prefix of a framed word array. -/
theorem word_array_take {m : Memory} {data : BitVec 64} {xs : List (BitVec 64)} {frame : SepProp}
    (arr : m ⊨ (data ↦₆₄* xs) ∗ frame) {i : Nat} (hi : i ≤ xs.length) :
    m ⊨ (data ↦₆₄* xs.take i) ∗ ((wordAddr data i ↦₆₄* xs.drop i) ∗ frame) := by
  simpa only [pointsToWords64_eq_pointsToArray, wordAddr, pointsToArray_split_at _ _ data xs i hi,
    sepConj_assoc] using arr

/-- Use the suffix of a framed word array. -/
theorem word_array_drop {m : Memory} {data : BitVec 64} {xs : List (BitVec 64)} {frame : SepProp}
    (arr : m ⊨ (data ↦₆₄* xs) ∗ frame) {i : Nat} (hi : i ≤ xs.length) :
    m ⊨ (wordAddr data i ↦₆₄* xs.drop i) ∗ ((data ↦₆₄* xs.take i) ∗ frame) := by
  simpa only [← sepConj_assoc, sepConj_comm (data ↦₆₄* xs.take i) (wordAddr data i ↦₆₄* xs.drop i)] using
    word_array_take arr hi

end Example04Rust
