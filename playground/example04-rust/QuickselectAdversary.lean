import QuickselectAdversaryPartition

namespace Example04Rust.Adversary

open Pivot

set_option autoImplicit false

/-- Distinct signed words of a fixed length in the given interval. -/
structure InInterval (xs : List Word) (start n : Nat) : Prop where
  length : xs.length = n
  distinct : xs.Nodup
  range : ∀ x ∈ xs, (start : Int) ≤ x.toInt ∧ x.toInt < (start + n : Nat)

private theorem signed_word {n : Nat} (fit : n < 2^63) :
    (BitVec.ofNat 64 n).toInt = (n : Int) := by
  have hNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [hNat]; omega), hNat]

private theorem getElem_range_map (f : Nat → Word) {n i : Nat} (fit : i < n) :
    ((List.range n).map f)[i]! = f i := by
  have fit' : i < ((List.range n).map f).length := by simpa using fit
  rw [getElem!_pos _ i fit', List.getElem_map, List.getElem_range]

private theorem idxOf_inj {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {a b : α} (ha : a ∈ xs) (hb : b ∈ xs)
    (eq : xs.idxOf a = xs.idxOf b) : a = b := by
  have ai := List.getElem_idxOf (List.idxOf_lt_length_of_mem ha)
  have bi := List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)
  exact ai.symm.trans (by simpa only [eq] using bi)

/-- Place the smallest `rank n` words on exactly the marked positions.
    The remaining positions get distinct larger words. -/
theorem marked_input (start n : Nat) (positive : 0 < n) (fit : start + n ≤ 2^63) :
    ∃ xs, InInterval xs start n ∧
      ∀ i < n, i ∈ marked 0 n ↔ xs[i]!.toInt < (start + gap n : Nat) := by
  let low := marked 0 n
  let high := (List.range n).filter (fun i => decide (i ∉ low))
  let order := low ++ high
  have lowFits (i : Nat) (hi : i ∈ low) : i < n := by
    simpa only [Nat.zero_add] using (marked_index positive hi).2
  have orderNd : order.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨marked_nodup .., List.nodup_range.filter _, ?_⟩
    intro i hi j hj eq
    subst j
    exact (of_decide_eq_true (List.mem_filter.mp hj).2) hi
  have orderMem (i : Nat) : i ∈ order ↔ i < n := by
    change i ∈ low ++ high ↔ i < n
    rw [List.mem_append]
    constructor
    · intro h
      exact h.elim (lowFits i) (fun hi => List.mem_range.mp (List.mem_filter.mp hi).1)
    · intro hi
      by_cases hm : i ∈ low
      · exact Or.inl hm
      · exact Or.inr (List.mem_filter.mpr ⟨List.mem_range.mpr hi, decide_eq_true hm⟩)
  have orderLen : order.length = n := by
    have perm : order.Perm (List.range n) :=
      (List.perm_ext_iff_of_nodup orderNd List.nodup_range).mpr
        (fun i => (orderMem i).trans List.mem_range.symm)
    simpa using perm.length_eq
  have rankFits (i : Nat) (hi : i < n) : order.idxOf i < n := by
    simpa only [orderLen] using List.idxOf_lt_length_of_mem ((orderMem i).mpr hi)
  let place := fun i => BitVec.ofNat 64 (start + order.idxOf i)
  let xs := (List.range n).map place
  have value (i : Nat) (hi : i < n) : (place i).toInt = (start + order.idxOf i : Nat) := by
    apply signed_word
    have := rankFits i hi
    omega
  refine ⟨xs, ⟨by simp [xs], ?_, ?_⟩, ?_⟩
  · apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map]
    refine (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp_of_mem ?_
    intro a b ha hb different eq
    apply different
    have h := congrArg BitVec.toInt eq
    rw [value a (List.mem_range.mp ha), value b (List.mem_range.mp hb)] at h
    exact idxOf_inj ((orderMem a).mpr (List.mem_range.mp ha)) ((orderMem b).mpr (List.mem_range.mp hb))
      (by omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hfit := List.mem_range.mp hi
    have := rankFits i hfit
    rw [value i hfit]
    omega
  · intro i hi
    rw [show xs[i]! = place i from getElem_range_map place hi, value i hi]
    change i ∈ low ↔ _
    have count : low.length = gap n := marked_length ..
    by_cases hm : i ∈ low
    · have lower : order.idxOf i < low.length := by
        rw [show order = low ++ high from rfl, List.idxOf_append, ite_eq_left hm]
        exact List.idxOf_lt_length_of_mem hm
      exact iff_of_true hm (by omega)
    · have upper : low.length ≤ order.idxOf i := by
        rw [show order = low ++ high from rfl, List.idxOf_append, ite_eq_right hm]
        omega
      exact iff_of_false hm (by omega)

private theorem get_drop {xs : List Word} {i j : Nat} (fit : j < (xs.drop i).length) :
    (xs.drop i)[j]! = xs[i + j]! := by
  have hi : i + j < xs.length := by
    simp only [List.length_drop] at fit
    omega
  rw [getElem!_pos (xs.drop i) j fit, getElem!_pos xs (i + j) hi, List.getElem_drop]

private theorem mem_index {xs : List Word} {x : Word} (h : x ∈ xs) :
    ∃ i < xs.length, xs[i]! = x := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, hi, (getElem!_pos xs i hi).trans heq⟩

private theorem in_suffix_iff {xs ys : List Word} {pivot : Word} {p : Nat}
    (res : PartitionResult xs ys pivot p) (distinct : xs.Nodup) (x : Word) :
    x ∈ ys.drop (p + 1) ↔ x ∈ xs ∧ pivot.toInt < x.toInt := by
  constructor
  · intro hx
    obtain ⟨j, hj, eq⟩ := mem_index hx
    have jFit : p + 1 + j < ys.length := by simp only [List.length_drop] at hj; omega
    rw [get_drop hj] at eq
    exact ⟨res.perm.mem_iff.mpr (by rw [← eq, getElem!_pos ys _ jFit]; exact List.getElem_mem jFit),
      eq ▸ res.right_strict distinct (by omega) jFit⟩
  · rintro ⟨hx, above⟩
    obtain ⟨j, hj, eq⟩ := mem_index (res.perm.mem_iff.mp hx)
    have after : p < j := by
      by_cases early : j < p
      · have h := res.leftOrder j early
        rw [eq] at h
        omega
      · by_cases same : j = p
        · rw [same, res.pivotAtSplit] at eq
          rw [← eq] at above
          omega
        · omega
    let k := j - (p + 1)
    have hk : k < (ys.drop (p + 1)).length := by simp [k]; omega
    rw [← eq, show j = p + 1 + k from by unfold k; omega, ← get_drop hk,
      getElem!_pos (ys.drop (p + 1)) k hk]
    exact List.getElem_mem hk

private theorem suffix_map (suffix desired : List Word) (length : desired.length = suffix.length)
    (distinct : suffix.Nodup) (f : Word → Word)
    (assign : ∀ x ∈ suffix, f x = desired[suffix.idxOf x]!) :
    suffix.map f = desired := by
  apply List.ext_getElem
  · simpa using length.symm
  · intro i hi hi'
    have fit : i < suffix.length := by simpa using hi
    have eq := assign suffix[i] (List.getElem_mem fit)
    rw [List.getElem_map, eq, distinct.idxOf_getElem i fit, getElem!_pos desired i hi']


/-- Given any desired arrangement of the upper ranks, construct the input to
    one preceding round. Keep all marked low words fixed and pull back the
    desired upper words through the permutation of the baseline partition. -/
theorem prepend_round (start n : Nat) {desired : List Word} (positive : 0 < n)
    (fit : start + n ≤ 2^63) (after : InInterval desired (start + gap n) (n - gap n)) :
    ∃ xs output p split, InInterval xs start n ∧ MarkedBelow xs ∧
      SelectsPivot xs p ∧ Partition xs output p split ∧ split + 1 = gap n ∧
      output.drop (split + 1) = desired := by
  obtain ⟨before, interval, labels⟩ := marked_input start n positive fit
  let cut := start + gap n
  have beforePositive : 0 < before.length := interval.length.symm ▸ positive
  have lowLabels : MarkedBelow before := by
    intro i markedI j fitJ unmarkedJ
    rw [interval.length] at markedI fitJ unmarkedJ
    have fitI : i < n := by simpa only [Nat.zero_add] using (marked_index positive markedI).2
    have low := (labels i fitI).mp markedI
    have high := mt (labels j fitJ).mpr unmarkedJ
    omega
  obtain ⟨p, picked⟩ := SelectsPivot.exists_run before
  have pivotFits := (picked.ranked beforePositive).index
  let pivot := before[p]!
  obtain ⟨markedP, largest⟩ := picked.marked_max lowLabels
  have pivotLow : pivot.toInt < (cut : Int) := by
    have hp := pivotFits
    rw [interval.length] at hp markedP
    exact (labels p hp).mp markedP
  have above_iff {x : Word} (hx : x ∈ before) :
      pivot.toInt < x.toInt ↔ (cut : Int) ≤ x.toInt := by
    obtain ⟨i, hi, rfl⟩ := mem_index hx
    have hiN : i < n := interval.length ▸ hi
    by_cases hm : i ∈ marked 0 before.length
    · have small := (labels i hiN).mp (interval.length ▸ hm)
      have le := largest i hm
      exact iff_of_false (by exact Int.not_lt_of_ge le) (by omega)
    · have big := lowLabels p markedP i hi hm
      have high := mt (labels i hiN).mpr (show i ∉ marked 0 n from interval.length ▸ hm)
      exact iff_of_true big (by omega)
  obtain ⟨baseline, split, run⟩ := Partition.exists_run before p pivotFits
  have result := run.result
  have exactRank := picked.exact_lower_rank lowLabels beforePositive
  rw [result.split_eq_rank interval.distinct, interval.length] at exactRank
  let suffix := baseline.drop (split + 1)
  have desiredLength : desired.length = suffix.length := by
    rw [after.length, show suffix.length = baseline.length - (split + 1) from List.length_drop]
    rw [← result.perm.length_eq, interval.length, exactRank]
  have suffixNd : suffix.Nodup :=
    (interval.distinct.perm result.perm).sublist (List.drop_sublist _ _)
  let f := fun x : Word => if pivot.toInt < x.toInt then desired[suffix.idxOf x]! else x
  have pivotFixed : f pivot = pivot := ite_eq_right (Int.lt_irrefl _)
  have desiredFit (x : Word) (hx : x ∈ before) (high : pivot.toInt < x.toInt) :
      suffix.idxOf x < desired.length := by
    rw [desiredLength]
    exact List.idxOf_lt_length_of_mem ((in_suffix_iff result interval.distinct x).mpr ⟨hx, high⟩)
  have highRange (x : Word) (hx : x ∈ before) (high : pivot.toInt < x.toInt) :
      (cut : Int) ≤ (f x).toInt ∧ (f x).toInt < (start + n : Nat) := by
    have hfit := desiredFit x hx high
    have hmem : desired[suffix.idxOf x]! ∈ desired := by
      rw [getElem!_pos desired _ hfit]
      exact List.getElem_mem hfit
    have h := after.range _ hmem
    rw [show f x = desired[suffix.idxOf x]! from ite_eq_left high]
    have hg := QuickselectCost.rank_le positive
    unfold cut
    omega
  have reassign : PreservesPivot pivot f before := by
    intro x hx
    rw [pivotFixed]
    by_cases high : pivot.toInt < x.toInt
    · have big := (highRange x hx high).1
      constructor <;> omega
    · rw [show f x = x from ite_eq_right high]
      exact ⟨Iff.rfl, Iff.rfl⟩
  let xs := before.map f
  have xsLen : xs.length = before.length := List.length_map f
  have xDistinct : xs.Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map]
    refine (List.nodup_iff_pairwise_ne.mp interval.distinct).imp_of_mem ?_
    intro a b ha hb different eq
    have eqInt := congrArg BitVec.toInt eq
    by_cases highA : pivot.toInt < a.toInt <;> by_cases highB : pivot.toInt < b.toInt
    · apply different
      have ea : f a = desired[suffix.idxOf a]! := ite_eq_left highA
      have eb : f b = desired[suffix.idxOf b]! := ite_eq_left highB
      rw [ea, eb] at eq
      have indices := (after.distinct.getElem!_inj (desiredFit a ha highA) (desiredFit b hb highB)).mp eq
      exact idxOf_inj ((in_suffix_iff result interval.distinct a).mpr ⟨ha, highA⟩)
        ((in_suffix_iff result interval.distinct b).mpr ⟨hb, highB⟩) indices
    · have big := (highRange a ha highA).1
      rw [show f b = b from ite_eq_right highB] at eqInt
      omega
    · have big := (highRange b hb highB).1
      rw [show f a = a from ite_eq_right highA] at eqInt
      omega
    · apply different
      rw [show f a = a from ite_eq_right highA, show f b = b from ite_eq_right highB] at eq
      exact eq
  have sameMarked (i : Nat) (hi : i ∈ marked 0 before.length) : xs[i]! = before[i]! := by
    have iFit : i < before.length := by simpa only [Nat.zero_add] using (marked_index beforePositive hi).2
    rw [show xs[i]! = f (before[i]!) from get_map f iFit]
    exact ite_eq_right (Int.not_lt_of_ge (largest i hi))
  have xsBelow : MarkedBelow xs := by
    intro i hi j jFit hj
    rw [xsLen] at hi jFit hj
    rw [sameMarked i hi, show xs[j]! = f (before[j]!) from get_map f jFit]
    have high := lowLabels p markedP j jFit hj
    have mem : before[j]! ∈ before := by rw [getElem!_pos before j jFit]; exact List.getElem_mem jFit
    have h := (highRange _ mem high).1
    have hle := largest i hi
    change _ ≤ pivot.toInt at hle
    omega
  obtain ⟨q, selected⟩ := SelectsPivot.exists_run xs
  have sameP := picked.same_marked_choice selected xsLen beforePositive lowLabels xsBelow interval.distinct sameMarked
  have replay := run.map f reassign
  have xsInterval : InInterval xs start n := by
    refine ⟨xsLen.trans interval.length, xDistinct, ?_⟩
    intro x hx
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hx
    by_cases high : pivot.toInt < old.toInt
    · have range := highRange old hold high
      have low : (start : Int) ≤ (cut : Int) := by unfold cut; omega
      exact ⟨Int.le_trans low range.1, range.2⟩
    · rw [show f old = old from ite_eq_right high]
      exact interval.range old hold
  refine ⟨xs, baseline.map f, p, split, xsInterval, xsBelow, sameP.symm ▸ selected, replay, exactRank, ?_⟩
  rw [← List.map_drop]
  apply suffix_map suffix desired desiredLength suffixNd f
  intro x hx
  exact ite_eq_left ((in_suffix_iff result interval.distinct x).mp hx).2


/-- A round of selecting the maximum whose pivot discards exactly the
    guaranteed lower rank. `suffix` is its next active slice. -/
structure MaxRound (input suffix : List Word) : Prop where
  positive : 0 < input.length
  distinct : input.Nodup
  marked : MarkedBelow input
  partition : ∃ output index split, SelectsPivot input index ∧ Partition input output index split ∧
    split + 1 = gap input.length ∧ output.drop (split + 1) = suffix

theorem MaxRound.suffix_length {input suffix : List Word} (round : MaxRound input suffix) :
    suffix.length = input.length - gap input.length := by
  obtain ⟨output, index, split, _, run, rank, suffixEq⟩ := round.partition
  rw [← suffixEq, List.length_drop, ← run.result.perm.length_eq, rank]

/-- Every realization of the pivot and partition comparisons in this round
    has the prescribed successor. The distinct words make the selected
    marked maximum unique. -/
theorem MaxRound.realized {input suffix output : List Word} {index split : Nat}
    (round : MaxRound input suffix) (choice : SelectsPivot input index)
    (run : Partition input output index split) :
    split + 1 = gap input.length ∧ output.drop (split + 1) = suffix := by
  obtain ⟨output', index', split', choice', run', rank, suffixEq⟩ := round.partition
  have eq := choice.same_marked_choice choice' rfl round.positive round.marked round.marked
    round.distinct (fun _ _ => rfl)
  subst index'
  obtain ⟨rfl, rfl⟩ := run.deterministic run'
  exact ⟨rank, suffixEq⟩

/-- A full source execution selecting the maximum. The numeric index is the
    sum of active slice lengths along its sequence of real partitions. -/
inductive MaxRounds : List Word → Nat → Prop
  | last {input : List Word} (round : MaxRound input []) :
      MaxRounds input input.length
  | next {input suffix : List Word} {tail : Nat}
      (round : MaxRound input suffix) (suffixPositive : 0 < suffix.length)
      (rest : MaxRounds suffix tail) :
      MaxRounds input (input.length + tail)

private theorem square_difference {m r n : Nat} (sum : n = m + r) :
    n ^ 2 = m ^ 2 + r * (n + m) := by
  rw [sum]
  simp only [Nat.pow_two, Nat.mul_add, Nat.add_mul]
  ac_rfl

/-- Concrete arrays of distinct signed i64 words realize the slow
    partition sequence for every representable positive length. Each round
    discards exactly `rank` of its current length. -/
theorem worst_source (start n : Nat) (positive : 0 < n) (fit : start + n ≤ 2^63) :
    ∃ xs work, InInterval xs start n ∧ MaxRounds xs work ∧ n ^ 2 ≤ 2 * work * gap n := by
  induction n using Nat.strongRecOn generalizing start with
  | ind n ih =>
    let r := gap n
    let m := n - r
    have rPos : 0 < r := QuickselectCost.rank_pos n
    have rLe : r ≤ n := QuickselectCost.rank_le positive
    have sum : n = m + r := by unfold m; omega
    have build (suffix : List Word) (suf : InInterval suffix (start + r) m) :
        ∃ xs, InInterval xs start n ∧ MaxRound xs suffix := by
      obtain ⟨xs, output, p, split, range, marked, picked, part, rank, next⟩ :=
        prepend_round start n positive fit suf
      refine ⟨xs, range, range.length.symm ▸ positive, range.distinct, marked,
        output, p, split, picked, part, ?_, next⟩
      simpa only [range.length] using rank
    by_cases empty : m = 0
    · obtain ⟨xs, interval, round⟩ := build [] ⟨by simp [empty], by simp, by simp⟩
      refine ⟨xs, xs.length, interval, .last round, ?_⟩
      rw [interval.length, show gap n = n from by omega]
      simpa only [Nat.pow_two, Nat.mul_assoc, Nat.one_mul] using
        (Nat.mul_le_mul_right (n * n) (show 1 ≤ 2 by decide))
    · have tailPos : 0 < m := Nat.pos_of_ne_zero empty
      have small : m < n := by omega
      obtain ⟨suffix, tail, interval, run, bound⟩ := ih m small (start + r) tailPos (by omega)
      obtain ⟨xs, range, first⟩ := build suffix interval
      refine ⟨xs, xs.length + tail, range, .next first (by rw [interval.length]; exact tailPos) run, ?_⟩
      rw [range.length]
      have mono : gap m ≤ gap n := QuickselectCost.rank_mono (by omega)
      have tailBound := Nat.le_trans bound (Nat.mul_le_mul_left (2 * tail) mono)
      have thisRound := Nat.mul_le_mul_left r (show n + m ≤ 2 * n by omega)
      calc
        n ^ 2 = m ^ 2 + r * (n + m) := square_difference sum
        _ ≤ 2 * tail * r + r * (2 * n) := Nat.add_le_add tailBound thisRound
        _ = 2 * (n + tail) * gap n := by
          change _ = 2 * (n + tail) * r
          simp only [Nat.mul_add, Nat.add_mul]
          ac_rfl

end Example04Rust.Adversary
