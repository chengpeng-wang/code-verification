import QuickselectPivot

namespace Example04Rust.Pivot

/-- The recursive comparisons that choose an index from three sampled blocks. -/
inductive PivotChoice (xs : List Word) : Nat → Nat → Nat → Nat → Nat → Prop
  | leaf {a b c len p : Nat} (short : len < 9) (chosen : Median xs a b c p) :
      PivotChoice xs a b c len p
  | branch {a b c len pa pb pc p : Nat} (large : 9 ≤ len)
      (left : PivotChoice xs a (a + 4 * (len / 9)) (a + 8 * (len / 9)) (len / 9) pa)
      (mid : PivotChoice xs b (b + 4 * (len / 9)) (b + 8 * (len / 9)) (len / 9) pb)
      (right : PivotChoice xs c (c + 4 * (len / 9)) (c + 8 * (len / 9)) (len / 9) pc)
      (chosen : Median xs pa pb pc p) : PivotChoice xs a b c len p

theorem PivotChoice.ranked {xs : List Word} {a b c len p : Nat}
    (choice : PivotChoice xs a b c len p) (blocks : ThreeBlocks xs a b c len) :
    Ranked xs a b c len p := by
  induction choice with
  | leaf short chosen => exact ranked_base blocks short chosen
  | branch large _ _ _ chosen ihA ihB ihC =>
    have := blocks.ab
    have := blocks.bc
    have := blocks.fits
    exact ranked_step blocks large (ihA (child_blocks large (by omega)))
      (ihB (child_blocks large (by omega))) (ihC (child_blocks large (by omega))) chosen

/-- Mark both low subtrees of each sampled median. At a leaf mark its only
    sampled index. These positions depend on the active length alone. -/
def marked (start len : Nat) : List Nat :=
  if len < 9 then [start]
  else marked start (len / 9) ++ marked (start + 4 * (len / 9)) (len / 9)
termination_by len
decreasing_by all_goals omega

theorem marked_short {start len : Nat} (short : len < 9) :
    marked start len = [start] := by
  rw [marked, ite_eq_left short]

theorem marked_large {start len : Nat} (large : 9 ≤ len) :
    marked start len =
      marked start (len / 9) ++ marked (start + 4 * (len / 9)) (len / 9) := by
  rw [marked, ite_eq_right (by omega)]

theorem marked_length (start len : Nat) : (marked start len).length = gap len := by
  induction len using Nat.strongRecOn generalizing start with
  | ind len ih =>
    by_cases short : len < 9
    · simp only [marked_short short, QuickselectCost.rank_small short, List.length_cons,
        List.length_nil, Nat.zero_add]
    · rw [marked_large (by omega), List.length_append, ih (len / 9) (by omega),
        ih (len / 9) (by omega)]
      simp only [gap, QuickselectCost.rank_large (n := len) (by omega), Nat.two_mul]

theorem marked_index {start len index : Nat} (positive : 0 < len)
    (mark : index ∈ marked start len) : start ≤ index ∧ index < start + len := by
  induction len using Nat.strongRecOn generalizing start with
  | ind len ih =>
    by_cases short : len < 9
    · rw [marked_short short] at mark
      simp only [List.mem_singleton] at mark
      omega
    · rw [marked_large (by omega), List.mem_append] at mark
      rcases mark with h | h
      · have := ih (len / 9) (by omega) (by omega) h
        omega
      · have := ih (len / 9) (by omega) (by omega) h
        omega

theorem marked_nodup (start len : Nat) : (marked start len).Nodup := by
  induction len using Nat.strongRecOn generalizing start with
  | ind len ih =>
    by_cases short : len < 9
    · simp [marked_short short]
    · rw [marked_large (by omega), List.nodup_append]
      refine ⟨ih (len / 9) (by omega) _, ih (len / 9) (by omega) _, ?_⟩
      intro i hi j hj
      have := marked_index (by omega) hi
      have := marked_index (by omega) hj
      omega

def InBlock (start len index : Nat) : Prop :=
  start ≤ index ∧ index < start + len

private theorem InBlock.parent {start len j : Nat}
    (h : InBlock start (len / 9) j ∨
      InBlock (start + 4 * (len / 9)) (len / 9) j ∨
      InBlock (start + 8 * (len / 9)) (len / 9) j) : InBlock start len j := by
  rcases h with h | h | h <;> unfold InBlock at h ⊢ <;> omega

private theorem median_two_low {xs : List Word} {a b c p : Nat}
    (h : Median xs a b c p)
    (ha : xs[a]!.toInt < xs[c]!.toInt)
    (hb : xs[b]!.toInt < xs[c]!.toInt) :
    (p = a ∨ p = b) ∧ xs[a]!.toInt ≤ xs[p]!.toInt ∧ xs[b]!.toInt ≤ xs[p]!.toInt := by
  have hne : p ≠ c := by
    intro hc
    subst p
    rcases h.upper with hx | hx | hx <;> omega
  have chooseAB : p = a ∨ p = b := by
    rcases h.chosen with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hne h).elim
  refine ⟨chooseAB, ?_⟩
  rcases chooseAB with rfl | rfl <;>
    rcases h.lower with hx | hx | hx <;> omega

theorem PivotChoice.in_blocks {xs : List Word} {a b c len p : Nat}
    (choice : PivotChoice xs a b c len p) (positive : 0 < len) :
    InBlock a len p ∨ InBlock b len p ∨ InBlock c len p := by
  induction choice with
  | leaf _ m =>
    rcases m.chosen with rfl | rfl | rfl <;> simp [InBlock, positive]
  | branch large _ _ _ m ihA ihB ihC =>
    rcases m.chosen with rfl | rfl | rfl
    · exact Or.inl (InBlock.parent (ihA (by omega)))
    · exact Or.inr (Or.inl (InBlock.parent (ihB (by omega))))
    · exact Or.inr (Or.inr (InBlock.parent (ihC (by omega))))

/-- The two marked groups are lower than all unmarked positions in the three
    sampled blocks. The median is then the largest marked entry. -/
theorem PivotChoice.marked_max {xs : List Word} {a b c len p : Nat}
    (choice : PivotChoice xs a b c len p)
    (blocks : ThreeBlocks xs a b c len)
    (below : ∀ i ∈ marked a len ++ marked b len, ∀ j,
      (InBlock a len j ∨ InBlock b len j ∨ InBlock c len j) →
      j ∉ marked a len ++ marked b len → xs[i]!.toInt < xs[j]!.toInt) :
    p ∈ marked a len ++ marked b len ∧
      ∀ i ∈ marked a len ++ marked b len, xs[i]!.toInt ≤ xs[p]!.toInt := by
  induction choice with
  | @leaf a b c len p short m =>
    have pos := blocks.positive
    have ab := blocks.ab
    have bc := blocks.bc
    have hc : c ∉ marked a len ++ marked b len := by
      simp only [marked_short short, List.mem_append, List.mem_singleton]
      omega
    have ha := below a (by simp [marked_short short]) c (Or.inr (Or.inr ⟨by omega, by omega⟩)) hc
    have hb := below b (by simp [marked_short short]) c (Or.inr (Or.inr ⟨by omega, by omega⟩)) hc
    obtain ⟨chosen, leA, leB⟩ := median_two_low m ha hb
    simp only [marked_short short, List.mem_append, List.mem_singleton]
    exact ⟨chosen, fun _ hi => hi.elim (fun h => h ▸ leA) (fun h => h ▸ leB)⟩
  | @branch a b c len pa pb pc p large _ _ runC m ihA ihB _ =>
    have pos := blocks.positive
    have ab := blocks.ab
    have bc := blocks.bc
    have fits := blocks.fits
    have maxA := ihA (child_blocks large (by omega)) (by
      intro i hi j hj hjm
      have hj' := InBlock.parent hj
      apply below i (List.mem_append_left _ (by rwa [marked_large large])) j (Or.inl hj')
      intro hall
      rcases List.mem_append.mp hall with inA | inB
      · exact hjm (by rwa [← marked_large large])
      · have h := marked_index pos inB
        unfold InBlock at hj'
        omega)
    have maxB := ihB (child_blocks large (by omega)) (by
      intro i hi j hj hjm
      have hj' := InBlock.parent hj
      apply below i (List.mem_append_right _ (by rwa [marked_large large])) j (Or.inr (Or.inl hj'))
      intro hall
      rcases List.mem_append.mp hall with inA | inB
      · have h := marked_index pos inA
        unfold InBlock at hj'
        omega
      · exact hjm (by rwa [← marked_large large]))
    rw [← marked_large large] at maxA maxB
    have hpc := InBlock.parent (runC.in_blocks (by omega))
    have pcHigh : pc ∉ marked a len ++ marked b len := by
      intro mem
      rcases List.mem_append.mp mem with h | h
      all_goals
        have range := marked_index pos h
        unfold InBlock at hpc
        omega
    have ltA := below pa (List.mem_append_left _ maxA.1) pc (Or.inr (Or.inr hpc)) pcHigh
    have ltB := below pb (List.mem_append_right _ maxB.1) pc (Or.inr (Or.inr hpc)) pcHigh
    obtain ⟨chosen, leA, leB⟩ := median_two_low m ltA ltB
    constructor
    · rcases chosen with rfl | rfl
      · exact List.mem_append_left _ maxA.1
      · exact List.mem_append_right _ maxB.1
    · intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact Int.le_trans (maxA.2 i h) leA
      · exact Int.le_trans (maxB.2 i h) leB


/-- The driver uses index zero on a small slice and otherwise invokes the
    recursive median on the three specified sub-blocks. -/
inductive SelectsPivot (xs : List Word) : Nat → Prop
  | small (short : xs.length < 9) : SelectsPivot xs 0
  | large {p : Nat} (large : 9 ≤ xs.length)
      (choice : PivotChoice xs 0 (4 * (xs.length / 9)) (8 * (xs.length / 9)) (xs.length / 9) p) :
      SelectsPivot xs p

theorem SelectsPivot.ranked {xs : List Word} {p : Nat}
    (choice : SelectsPivot xs p) (positive : 0 < xs.length) : Chosen xs p := by
  cases choice with
  | small short => exact chosen_small positive short
  | large large choice => exact chosen_large large (choice.ranked ⟨by omega, by omega, by omega, by omega⟩)

/-- All marked positions contain words strictly less than the words at every
    unmarked position. The words within each group may have any order. -/
def MarkedBelow (xs : List Word) : Prop :=
  ∀ i ∈ marked 0 xs.length, ∀ j < xs.length, j ∉ marked 0 xs.length →
    xs[i]!.toInt < xs[j]!.toInt

theorem SelectsPivot.marked_max {xs : List Word} {p : Nat}
    (choice : SelectsPivot xs p) (below : MarkedBelow xs) :
    p ∈ marked 0 xs.length ∧
      ∀ i ∈ marked 0 xs.length, xs[i]!.toInt ≤ xs[p]!.toInt := by
  cases choice with
  | small short => simp [marked_short short]
  | large large choice =>
    rw [marked_large large, Nat.zero_add]
    apply choice.marked_max ⟨by omega, by omega, by omega, by omega⟩
    intro i hi j jrange jhi
    have jfit : j < xs.length := by
      rcases jrange with h | h | h <;> unfold InBlock at h <;> omega
    exact below i (by simpa only [marked_large large, Nat.zero_add] using hi) j jfit
      (by simpa only [marked_large large, Nat.zero_add] using jhi)

private theorem map_read_range (xs : List Word) :
    (List.range xs.length).map (fun i => xs[i]!) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [getElem?_pos xs i hj]

/-- The adversarial pivot has exactly the guaranteed weak lower rank, even
    when the values at all unmarked positions are freely rearranged. -/
theorem SelectsPivot.exact_lower_rank {xs : List Word} {p : Nat}
    (choice : SelectsPivot xs p) (below : MarkedBelow xs) (positive : 0 < xs.length) :
    countLE xs xs[p]! = gap xs.length := by
  obtain ⟨chosen, largest⟩ := choice.marked_max below
  let marks := marked 0 xs.length
  let pick := fun i : Nat => decide (xs[i]!.toInt ≤ xs[p]!.toInt)
  have count : countLE xs xs[p]! = ((List.range xs.length).filter pick).length := by
    calc
      countLE xs xs[p]! = countLE ((List.range xs.length).map (fun i => xs[i]!)) xs[p]! := by
        rw [map_read_range]
      _ = ((List.range xs.length).filter pick).length := by
        rw [countLE, List.countP_map, List.countP_eq_length_filter]
        rfl
  have same : ((List.range xs.length).filter pick).Perm marks := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) (marked_nodup ..)).2
    intro i
    constructor
    · intro h
      obtain ⟨fit, le⟩ := List.mem_filter.mp h
      by_cases hm : i ∈ marks
      · exact hm
      · have lt := below p chosen i (List.mem_range.mp fit) hm
        have le' : xs[i]!.toInt ≤ xs[p]!.toInt := of_decide_eq_true le
        exact ((Int.not_le_of_gt lt) le').elim
    · intro h
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr (by simpa only [Nat.zero_add] using (marked_index positive h).2), decide_eq_true (largest i h)⟩
  rw [count, same.length_eq]
  exact marked_length 0 xs.length


private theorem median_exists (xs : List Word) (a b c : Nat) :
    ∃ p, Median xs a b c p := by
  let p := if decide (xs[a]!.toInt < xs[b]!.toInt) != decide (xs[a]!.toInt < xs[c]!.toInt)
    then a else if decide (xs[b]!.toInt < xs[c]!.toInt) == decide (xs[a]!.toInt < xs[b]!.toInt)
    then b else c
  exact ⟨p, median_of_choice rfl⟩

theorem PivotChoice.exists_run (xs : List Word) (a b c len : Nat) :
    ∃ p, PivotChoice xs a b c len p := by
  induction len using Nat.strongRecOn generalizing a b c with
  | ind len ih =>
    by_cases short : len < 9
    · obtain ⟨p, m⟩ := median_exists xs a b c
      exact ⟨p, .leaf short m⟩
    · have smaller : len / 9 < len := by omega
      obtain ⟨pa, ra⟩ := ih _ smaller a (a + 4 * (len / 9)) (a + 8 * (len / 9))
      obtain ⟨pb, rb⟩ := ih _ smaller b (b + 4 * (len / 9)) (b + 8 * (len / 9))
      obtain ⟨pc, rc⟩ := ih _ smaller c (c + 4 * (len / 9)) (c + 8 * (len / 9))
      obtain ⟨p, m⟩ := median_exists xs pa pb pc
      exact ⟨p, .branch (by omega) ra rb rc m⟩

theorem SelectsPivot.exists_run (xs : List Word) : ∃ p, SelectsPivot xs p := by
  by_cases short : xs.length < 9
  · exact ⟨0, .small short⟩
  · obtain ⟨p, choice⟩ := PivotChoice.exists_run xs 0 (4 * (xs.length / 9)) (8 * (xs.length / 9))
      (xs.length / 9)
    exact ⟨p, .large (by omega) choice⟩

theorem SelectsPivot.same_marked_choice {xs ys : List Word} {p q : Nat}
    (first : SelectsPivot xs p) (second : SelectsPivot ys q)
    (length : ys.length = xs.length) (positive : 0 < xs.length)
    (below : MarkedBelow xs) (below' : MarkedBelow ys) (distinct : xs.Nodup)
    (same : ∀ i ∈ marked 0 xs.length, ys[i]! = xs[i]!) : p = q := by
  obtain ⟨hp, pmax⟩ := first.marked_max below
  obtain ⟨hq, qmax⟩ := second.marked_max below'
  rw [length] at hq qmax
  have hpFit : p < xs.length := by simpa only [Nat.zero_add] using (marked_index positive hp).2
  have hqFit : q < xs.length := by simpa only [Nat.zero_add] using (marked_index positive hq).2
  have le := pmax q hq
  have ge := qmax p hp
  rw [same p hp, same q hq] at ge
  exact (distinct.getElem!_inj hpFit hqFit).mp (BitVec.toInt_inj.mp (Int.le_antisymm ge le))

end Example04Rust.Pivot
