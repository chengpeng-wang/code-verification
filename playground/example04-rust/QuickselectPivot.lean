import QuickselectCost

namespace Example04Rust.Pivot

open scoped List

abbrev Word := BitVec 64

/-- The rank guaranteed by recursively sampling three disjoint blocks. -/
abbrev gap := QuickselectCost.rank

private theorem gap_small {n : Nat} (h : n < 9) : gap n = 1 :=
  QuickselectCost.rank_small h

private theorem gap_large {n : Nat} (h : 9 ≤ n) : gap n = 2 * gap (n / 9) :=
  QuickselectCost.rank_large h

/-- Count entries, including repetitions, using the signed i64 order. -/
def countLE (xs : List Word) (pivot : Word) : Nat :=
  xs.countP fun x => decide (x.toInt ≤ pivot.toInt)

def countGE (xs : List Word) (pivot : Word) : Nat :=
  xs.countP fun x => decide (pivot.toInt ≤ x.toInt)

def slice {α : Type} (xs : List α) (start len : Nat) : List α :=
  (xs.drop start).take len

def blocks (xs : List Word) (a b c len : Nat) : List Word :=
  slice xs a len ++ slice xs b len ++ slice xs c len

/-- Three nonempty blocks in address order, each wholly inside the input. -/
structure ThreeBlocks (xs : List Word) (a b c len : Nat) : Prop where
  positive : 0 < len
  ab : a + len ≤ b
  bc : b + len ≤ c
  fits : c + len ≤ xs.length

/-- The relation established by the comparisons of the three loaded candidates. -/
structure Median (xs : List Word) (a b c p : Nat) : Prop where
  chosen : p = a ∨ p = b ∨ p = c
  lower :
    (xs[a]!.toInt ≤ xs[p]!.toInt ∧ xs[b]!.toInt ≤ xs[p]!.toInt) ∨
    (xs[a]!.toInt ≤ xs[p]!.toInt ∧ xs[c]!.toInt ≤ xs[p]!.toInt) ∨
    (xs[b]!.toInt ≤ xs[p]!.toInt ∧ xs[c]!.toInt ≤ xs[p]!.toInt)
  upper :
    (xs[p]!.toInt ≤ xs[a]!.toInt ∧ xs[p]!.toInt ≤ xs[b]!.toInt) ∨
    (xs[p]!.toInt ≤ xs[a]!.toInt ∧ xs[p]!.toInt ≤ xs[c]!.toInt) ∨
    (xs[p]!.toInt ≤ xs[b]!.toInt ∧ xs[p]!.toInt ≤ xs[c]!.toInt)

/-- This implication reads the three comparison outcomes of median3. -/
theorem median_of_choice {xs : List Word} {a b c p : Nat}
    (h : p = if decide (xs[a]!.toInt < xs[b]!.toInt) != decide (xs[a]!.toInt < xs[c]!.toInt)
      then a else if decide (xs[b]!.toInt < xs[c]!.toInt) == decide (xs[a]!.toInt < xs[b]!.toInt)
      then b else c) :
    Median xs a b c p := by
  by_cases hab : xs[a]!.toInt < xs[b]!.toInt <;>
  by_cases hac : xs[a]!.toInt < xs[c]!.toInt <;>
  by_cases hbc : xs[b]!.toInt < xs[c]!.toInt
  all_goals
    simp only [hab, hac, hbc, decide_true, decide_false] at h
    simp at h
    subst p
    first
    | exact ⟨Or.inl rfl, by omega, by omega⟩
    | exact ⟨Or.inr (Or.inl rfl), by omega, by omega⟩
    | exact ⟨Or.inr (Or.inr rfl), by omega, by omega⟩

/-- Rank certificate for the returned index of the recursive pseudo-median.
Counts range over the actual three enclosing blocks. -/
structure Ranked (xs : List Word) (a b c len p : Nat) : Prop where
  first : a ≤ p
  last : p < c + len
  lower : 2 * gap len ≤ countLE (blocks xs a b c len) xs[p]!
  upper : 2 * gap len ≤ countGE (blocks xs a b c len) xs[p]!

private theorem slice_one {xs : List Word} {a : Nat} (ha : a < xs.length) :
    slice xs a 1 = [xs[a]!] := by
  rw [slice, List.take_one, List.head?_drop, getElem?_pos xs a ha, getElem!_pos xs a ha]
  rfl

private theorem first_sublist_slice {xs : List Word} {a len : Nat}
    (ha : a < xs.length) (h : 0 < len) : [xs[a]!] <+ slice xs a len := by
  rw [← slice_one ha]
  have ht := List.take_sublist 1 ((xs.drop a).take len)
  simpa only [slice, List.take_take, Nat.min_eq_left h] using ht

private theorem countP_three {α : Type} {test : α → Bool} {a b c : α}
    (h : (test a ∧ test b) ∨ (test a ∧ test c) ∨ (test b ∧ test c)) :
    2 ≤ List.countP test [a,b,c] := by
  simp only [List.countP_cons, List.countP_nil]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
  · simp only [ha, hb, ite_true]; omega
  · simp only [ha, hc, ite_true]; omega
  · simp only [hb, hc, ite_true]; omega

theorem ranked_base {xs : List Word} {a b c len p : Nat}
    (h : ThreeBlocks xs a b c len) (short : len < 9) (m : Median xs a b c p) :
    Ranked xs a b c len p := by
  obtain ⟨pos, ab, bc, fits⟩ := h
  have hsub : [xs[a]!, xs[b]!, xs[c]!] <+ blocks xs a b c len := by
    exact ((first_sublist_slice (by omega) pos).append
      (first_sublist_slice (by omega) pos)).append (first_sublist_slice (by omega) pos)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases m.chosen with h | h | h <;> omega
  · rcases m.chosen with h | h | h <;> omega
  · rw [gap_small short]
    exact Nat.le_trans (countP_three (by simpa only [decide_eq_true_eq] using m.lower)) hsub.countP_le
  · rw [gap_small short]
    exact Nat.le_trans (countP_three (by simpa only [decide_eq_true_eq] using m.upper)) hsub.countP_le

private theorem prepend_slice_sublist {α : Type} {xs ys : List α} {a len : Nat}
    (tail : ys <+ xs.drop (a + len)) :
    slice xs a len ++ ys <+ xs.drop a := by
  have htail : ys <+ (xs.drop a).drop len := by simpa only [List.drop_drop]
  have ht := (List.Sublist.refl ((xs.drop a).take len)).append htail
  simpa only [slice, List.take_append_drop] using ht

private theorem blocks_sublist_drop {xs : List Word} {a b c len : Nat}
    (ab : a + len ≤ b) (bc : b + len ≤ c) :
    blocks xs a b c len <+ xs.drop a := by
  have hc : slice xs c len <+ xs.drop c := List.take_sublist len (xs.drop c)
  have hc' := hc.trans (List.drop_sublist_drop_left xs bc)
  have hbc := prepend_slice_sublist hc'
  have hbc' := hbc.trans (List.drop_sublist_drop_left xs ab)
  simpa only [blocks, List.append_assoc] using prepend_slice_sublist hbc'

private theorem slice_take {xs : List Word} {a len bound : Nat} (h : a + len ≤ bound) :
    slice (xs.take bound) a len = slice xs a len := by
  simp only [slice, List.take_drop, List.take_take, Nat.min_eq_left h]

private theorem sample_sublist {xs : List Word} {a len : Nat} :
    blocks xs a (a + 4 * (len / 9)) (a + 8 * (len / 9)) (len / 9) <+ slice xs a len := by
  have h := blocks_sublist_drop (xs := xs.take (a + len)) (a := a)
    (b := a + 4 * (len / 9)) (c := a + 8 * (len / 9)) (len := len / 9) (by omega) (by omega)
  rw [blocks, slice_take (by omega), slice_take (by omega), slice_take (by omega)] at h
  rw [slice, List.take_drop]
  exact h

theorem child_blocks {xs : List Word} {a len : Nat} (large : 9 ≤ len) (fits : a + len ≤ xs.length) :
    ThreeBlocks xs a (a + 4 * (len / 9)) (a + 8 * (len / 9)) (len / 9) :=
  ⟨by omega, by omega, by omega, by omega⟩

private theorem countLE_mono (xs : List Word) {x y : Word} (h : x.toInt ≤ y.toInt) :
    countLE xs x ≤ countLE xs y :=
  List.countP_mono_left fun _ _ hz => decide_eq_true (Int.le_trans (of_decide_eq_true hz) h)

private theorem countGE_mono (xs : List Word) {x y : Word} (h : x.toInt ≤ y.toInt) :
    countGE xs y ≤ countGE xs x :=
  List.countP_mono_left fun _ _ hz => decide_eq_true (Int.le_trans h (of_decide_eq_true hz))

private theorem child_lower {xs : List Word} {a len p q : Nat}
    (r : Ranked xs a (a + 4 * (len / 9)) (a + 8 * (len / 9)) (len / 9) q)
    (h : xs[q]!.toInt ≤ xs[p]!.toInt) :
    2 * gap (len / 9) ≤ countLE (slice xs a len) xs[p]! :=
  Nat.le_trans r.lower (Nat.le_trans sample_sublist.countP_le (countLE_mono _ h))

private theorem child_upper {xs : List Word} {a len p q : Nat}
    (r : Ranked xs a (a + 4 * (len / 9)) (a + 8 * (len / 9)) (len / 9) q)
    (h : xs[p]!.toInt ≤ xs[q]!.toInt) :
    2 * gap (len / 9) ≤ countGE (slice xs a len) xs[p]! :=
  Nat.le_trans r.upper (Nat.le_trans sample_sublist.countP_le (countGE_mono _ h))

/-- Combine three recursively certified candidates using the actual median3
comparison result. Two child blocks contribute to each rank bound. -/
theorem ranked_step {xs : List Word} {a b c len pa pb pc p : Nat}
    (h : ThreeBlocks xs a b c len) (large : 9 ≤ len)
    (ra : Ranked xs a (a + 4 * (len / 9)) (a + 8 * (len / 9)) (len / 9) pa)
    (rb : Ranked xs b (b + 4 * (len / 9)) (b + 8 * (len / 9)) (len / 9) pb)
    (rc : Ranked xs c (c + 4 * (len / 9)) (c + 8 * (len / 9)) (len / 9) pc)
    (m : Median xs pa pb pc p) :
    Ranked xs a b c len p := by
  obtain ⟨_, ab, bc, _⟩ := h
  have ha1 := ra.first
  have hb1 := rb.first
  have hc1 := rc.first
  have ha2 := ra.last
  have hb2 := rb.last
  have hc2 := rc.last
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases m.chosen with h | h | h <;> omega
  · rcases m.chosen with h | h | h <;> omega
  · rw [gap_large large]
    simp only [blocks, countLE, List.countP_append]
    rcases m.lower with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
    · have ha := child_lower ra ha
      have hb := child_lower rb hb
      unfold countLE at ha hb
      omega
    · have ha := child_lower ra ha
      have hc := child_lower rc hc
      unfold countLE at ha hc
      omega
    · have hb := child_lower rb hb
      have hc := child_lower rc hc
      unfold countLE at hb hc
      omega
  · rw [gap_large large]
    simp only [blocks, countGE, List.countP_append]
    rcases m.upper with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
    · have ha := child_upper ra ha
      have hb := child_upper rb hb
      unfold countGE at ha hb
      omega
    · have ha := child_upper ra ha
      have hc := child_upper rc hc
      unfold countGE at ha hc
      omega
    · have hb := child_upper rb hb
      have hc := child_upper rc hc
      unfold countGE at hb hc
      omega

/-- Rank certificate over the full active slice for the driver. -/
structure Chosen (xs : List Word) (p : Nat) : Prop where
  index : p < xs.length
  lower : gap xs.length ≤ countLE xs xs[p]!
  upper : gap xs.length ≤ countGE xs xs[p]!

theorem chosen_small {xs : List Word} (positive : 0 < xs.length) (short : xs.length < 9) :
    Chosen xs 0 := by
  cases xs with
  | nil => simp at positive
  | cons x xs =>
    refine ⟨positive, ?_, ?_⟩
    · rw [gap_small short]
      simp [countLE]
    · rw [gap_small short]
      simp [countGE]

theorem chosen_large {xs : List Word} {p : Nat} (large : 9 ≤ xs.length)
    (r : Ranked xs 0 (4 * (xs.length / 9)) (8 * (xs.length / 9)) (xs.length / 9) p) :
    Chosen xs p := by
  have hsub : blocks xs 0 (4 * (xs.length / 9)) (8 * (xs.length / 9)) (xs.length / 9) <+ xs := by
    simpa only [List.drop_zero] using blocks_sublist_drop (a := 0) (by omega) (by omega)
  have last := r.last
  refine ⟨by omega, ?_, ?_⟩
  · rw [gap_large large]
    exact Nat.le_trans r.lower hsub.countP_le
  · rw [gap_large large]
    exact Nat.le_trans r.upper hsub.countP_le

/-- Counts used by the Hoare invariant. Each completed exchange can leave at
most one copy of the pivot in each processed side. -/
def countEQ (xs : List Word) (pivot : Word) : Nat :=
  xs.countP fun x => decide (x = pivot)

private theorem countLE_le_eq {xs : List Word} {pivot : Word}
    (h : ∀ x ∈ xs, pivot.toInt ≤ x.toInt) : countLE xs pivot ≤ countEQ xs pivot :=
  List.countP_mono_left fun x hx hle =>
    decide_eq_true (BitVec.toInt_inj.mp (Int.le_antisymm (of_decide_eq_true hle) (h x hx)))

private theorem countGE_le_eq {xs : List Word} {pivot : Word}
    (h : ∀ x ∈ xs, x.toInt ≤ pivot.toInt) : countGE xs pivot ≤ countEQ xs pivot :=
  List.countP_mono_left fun x hx hge =>
    decide_eq_true (BitVec.toInt_inj.mp (Int.le_antisymm (h x hx) (of_decide_eq_true hge)))

/-- At the end of the two Hoare scans, the pending exchange with the pivot
does not affect counts. The left scan may cross the right scan by one entry,
which accounts for the extra constant in the bound on `countGE`. -/
theorem hoare_counts {input rest : List Word} {pivot : Word} {i j swaps : Nat}
    (perm : input.Perm (pivot :: rest))
    (crossed : j ≤ i) (overlap : i ≤ j + 1) (fits : i ≤ rest.length)
    (leftOrder : ∀ x ∈ rest.take i, x.toInt ≤ pivot.toInt)
    (rightOrder : ∀ x ∈ rest.drop j, pivot.toInt ≤ x.toInt)
    (leftEquals : countEQ (rest.take i) pivot ≤ swaps)
    (rightEquals : countEQ (rest.drop j) pivot ≤ swaps)
    (swapsLeft : swaps ≤ i) (swapsRight : swaps ≤ rest.length - j) :
    countLE input pivot ≤ 2 * i + 1 ∧
      countGE input pivot ≤ 2 * (rest.length - i) + 2 := by
  have rightSub := List.drop_sublist_drop_left rest crossed
  have rightOrder' : ∀ x ∈ rest.drop i, pivot.toInt ≤ x.toInt :=
    fun x hx => rightOrder x (rightSub.subset hx)
  have rightEquals' : countEQ (rest.drop i) pivot ≤ countEQ (rest.drop j) pivot :=
    rightSub.countP_le
  have perm' : input.Perm (pivot :: (rest.take i ++ rest.drop i)) := by
    simpa only [List.take_append_drop] using perm
  have leL : countLE (rest.take i) pivot ≤ i := by
    have h : countLE (rest.take i) pivot ≤ (rest.take i).length := List.countP_le_length
    rwa [List.length_take, Nat.min_eq_left fits] at h
  have geR : countGE (rest.drop i) pivot ≤ rest.length - i := by
    have h : countGE (rest.drop i) pivot ≤ (rest.drop i).length := List.countP_le_length
    rwa [List.length_drop] at h
  have leR := countLE_le_eq rightOrder'
  have geL := countGE_le_eq leftOrder
  constructor
  · unfold countLE at leL leR ⊢
    rw [perm'.countP_eq]
    simp only [List.countP_cons, List.countP_append, Int.le_refl, decide_true, ite_true]
    omega
  · unfold countGE at geL geR ⊢
    rw [perm'.countP_eq]
    simp only [List.countP_cons, List.countP_append, Int.le_refl, decide_true, ite_true]
    omega

/-- Translate the rank and partition counts to the shrinkage obligation for
either continuation of Quickselect. The pivot itself is discarded. -/
theorem hoare_discard {xs : List Word} {p split : Nat}
    (r : Chosen xs p) (fits : split < xs.length)
    (lower : countLE xs xs[p]! ≤ 2 * split + 1)
    (upper : countGE xs xs[p]! ≤ 2 * (xs.length - (split + 1)) + 2) :
    gap xs.length ≤ 2 * (xs.length - split) ∧
      gap xs.length ≤ 2 * (xs.length - (xs.length - (split + 1))) := by
  have le := r.lower
  have ge := r.upper
  omega

end Example04Rust.Pivot
