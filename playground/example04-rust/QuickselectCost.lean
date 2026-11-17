import Std

namespace QuickselectCost

set_option autoImplicit false

/-- Guaranteed weak rank of the recursively sampled pivot on a nonempty slice.
Each level of median-of-three doubles the rank in three disjoint windows. -/
def rank (n : Nat) : Nat :=
  if n < 9 then 1 else 2 * rank (n / 9)
termination_by n
decreasing_by omega

theorem rank_small {n : Nat} (h : n < 9) : rank n = 1 := by
  rw [rank, ite_eq_left h]

theorem rank_large {n : Nat} (h : 9 ≤ n) : rank n = 2 * rank (n / 9) := by
  rw [rank, ite_eq_right (by omega)]

theorem rank_pos (n : Nat) : 0 < rank n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 9
    · simp [rank_small h]
    · rw [rank_large (by omega)]
      have := ih (n / 9) (by omega)
      omega

theorem rank_le {n : Nat} (hn : 0 < n) : rank n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 9
    · rw [rank_small h]
      omega
    · rw [rank_large (by omega)]
      have := ih (n / 9) (by omega) (by omega)
      omega

theorem rank_mono {m n : Nat} (hmn : m ≤ n) : rank m ≤ rank n := by
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    by_cases hm : m < 9
    · rw [rank_small hm]
      exact rank_pos n
    · rw [rank_large (by omega : 9 ≤ m), rank_large (by omega : 9 ≤ n)]
      exact Nat.mul_le_mul_left 2 (ih (n / 9) (by omega) (Nat.div_le_div_right hmn))

/-- Thus for `n ≥ 1`, the denominator in the instruction budget is exactly
`2^⌊log₉ n⌋`. -/
theorem rank_eq_pow {n depth : Nat} (lower : 9 ^ depth ≤ n) (upper : n < 9 ^ (depth + 1)) :
    rank n = 2 ^ depth := by
  induction depth generalizing n with
  | zero => exact rank_small (by simpa using upper)
  | succ depth ih =>
    rw [Nat.pow_succ] at lower
    rw [Nat.pow_succ] at upper
    have h : 9 ≤ n := by
      have positive : 0 < 9 ^ depth := Nat.pow_pos (by decide)
      omega
    rw [rank_large h, ih ((Nat.le_div_iff_mul_le (by decide)).2 lower)
      ((Nat.div_lt_iff_lt_mul (by decide)).2 upper), Nat.pow_succ, Nat.mul_comm]

private theorem rank_scale {j n : Nat} (hj : 0 < j) (hjn : j ≤ n) :
    rank n * (j + 1) ≤ 2 * n * rank j := by
  induction n using Nat.strongRecOn generalizing j with
  | ind n ih =>
    by_cases hn : n < 9
    · rw [rank_small hn, rank_small (by omega : j < 9), Nat.one_mul, Nat.mul_one]
      omega
    · by_cases hsmall : j < 9
      · rw [rank_large (by omega), rank_small hsmall, Nat.mul_one]
        calc
          2 * rank (n / 9) * (j + 1) ≤ 2 * (n / 9) * (j + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (rank_le (by omega)))
          _ ≤ 2 * (n / 9) * 9 := Nat.mul_le_mul_left _ (by omega)
          _ ≤ 2 * n := by omega
      · have bound := ih (n / 9) (by omega) (j := j / 9) (by omega)
          (Nat.div_le_div_right hjn)
        rw [rank_large (by omega : 9 ≤ n), rank_large (by omega : 9 ≤ j)]
        calc
          2 * rank (n / 9) * (j + 1) ≤ 2 * rank (n / 9) * (9 * (j / 9 + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 18 * (rank (n / 9) * (j / 9 + 1)) := by
            rw [show 18 = 2 * 9 by decide]
            ac_rfl
          _ ≤ 18 * (2 * (n / 9) * rank (j / 9)) := Nat.mul_le_mul_left _ bound
          _ = (2 * (9 * (n / 9))) * (2 * rank (j / 9)) := by
            rw [show 18 = 2 * 9 by decide]
            ac_rfl
          _ ≤ 2 * n * (2 * rank (j / 9)) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

private def weight (j : Nat) : Nat := j / rank j + 1

/-- Sum of the cost credits for active lengths `1` through `n`. -/
def potential : Nat → Nat
  | 0 => 0
  | n + 1 => potential n + weight (n + 1)

private theorem potential_mono {m n : Nat} (hmn : m ≤ n) : potential m ≤ potential n := by
  induction n with
  | zero => simp [Nat.eq_zero_of_le_zero hmn]
  | succ n ih =>
    by_cases h : m = n + 1
    · subst m
      exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

private theorem potential_segment (start count scale unit : Nat)
    (weights : ∀ j, start < j → j ≤ start + count → unit ≤ scale * weight j) :
    count * unit + scale * potential start ≤ scale * potential (start + count) := by
  induction count with
  | zero => simp
  | succ count ih =>
    have before := ih (fun j hj hle => weights j hj (by omega))
    have last := weights (start + count + 1) (by omega) (by omega)
    change (count + 1) * unit + scale * potential start ≤ scale * potential (start + (count + 1))
    rw [← Nat.add_assoc, potential, Nat.mul_add, Nat.add_mul]
    omega

/-- A round discarding at least half the pivot's rank spends at least `n / 4`
credits. The integer form avoids a rounded-down lower bound. -/
theorem potential_charge {n m : Nat} (hn : 0 < n) (hm : m ≤ n)
    (gap : rank n ≤ 2 * (n - m)) : n + 4 * potential m ≤ 4 * potential n := by
  by_cases hnsmall : n < 9
  · have h := rank_small hnsmall
    have hpred : m ≤ n - 1 := by omega
    have hpot := potential_mono hpred
    have hstep : potential n = potential (n - 1) + n + 1 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      simp [potential, weight, h, Nat.add_assoc]
    omega
  · let d := rank (n / 9)
    have hd : 0 < d := rank_pos _
    have h : rank n = 2 * d := rank_large (by omega)
    have hr := rank_le hn
    have hdle : d ≤ n - m := by omega
    have hsum := potential_segment (n - d) d (2 * rank n) n (fun j hj hjn => by
      have hjle : j ≤ n := by omega
      have hjmid : n ≤ 2 * j := by omega
      have hweight : j ≤ rank j * weight j :=
        Nat.le_of_lt (Nat.lt_mul_div_succ j (rank_pos j))
      calc
        n ≤ 2 * j := hjmid
        _ ≤ 2 * (rank j * weight j) := Nat.mul_le_mul_left _ hweight
        _ ≤ 2 * (rank n * weight j) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (rank_mono hjle))
        _ = 2 * rank n * weight j := by rw [Nat.mul_assoc])
    have hpot := potential_mono (show m ≤ n - d by omega)
    have hsum' : d * n + 2 * rank n * potential m ≤ 2 * rank n * potential n := by
      rw [show n - d + d = n by omega] at hsum
      exact Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hpot) _) hsum
    have scale : d * 4 = 2 * rank n := by rw [h]; omega
    apply Nat.le_of_mul_le_mul_left (c := d) _ hd
    simpa only [Nat.mul_add, ← Nat.mul_assoc, scale] using hsum'

private theorem weight_bound {n j : Nat} (hj : 0 < j) (hjn : j ≤ n) :
    rank n * weight j ≤ 3 * n := by
  have hquot : rank n * (j / rank j) ≤ 2 * n := by
    apply Nat.le_of_mul_le_mul_right (c := rank j) _ (rank_pos j)
    calc
      rank n * (j / rank j) * rank j = rank n * (j / rank j * rank j) :=
        Nat.mul_assoc ..
      _ ≤ rank n * (j + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_trans (Nat.div_mul_le_self ..) (Nat.le_succ _))
      _ ≤ 2 * n * rank j := rank_scale hj hjn
  have hrank := rank_le (Nat.lt_of_lt_of_le hj hjn)
  rw [weight, Nat.mul_add, Nat.mul_one]
  omega

theorem potential_bound (n : Nat) : rank n * potential n ≤ 3 * n ^ 2 := by
  have prefixBound : ∀ m ≤ n, rank n * potential m ≤ 3 * n * m := by
    intro m hmn
    induction m with
    | zero => simp [potential]
    | succ m ih =>
      have before := ih (Nat.le_trans (Nat.le_succ m) hmn)
      have last := weight_bound (j := m + 1) (Nat.zero_lt_succ m) hmn
      rw [potential, Nat.mul_add, Nat.mul_succ (3 * n)]
      omega
  simpa only [Nat.pow_two, ← Nat.mul_assoc] using prefixBound n (Nat.le_refl _)

/-- Recursive median-of-three costs. Each node's local cost excludes its three
child calls. `span` is the length of each of the three sampled windows. -/
inductive PivotCosts (perNode : Nat) : Nat → Nat → Prop
  | leaf {span cost : Nat} : 0 < span → span < 9 → cost ≤ perNode → PivotCosts perNode span cost
  | branch {span localCost a b c : Nat} : 9 ≤ span → localCost ≤ perNode →
      PivotCosts perNode (span / 9) a → PivotCosts perNode (span / 9) b →
      PivotCosts perNode (span / 9) c → PivotCosts perNode span (localCost + a + b + c)

theorem PivotCosts.linear_bound {perNode span cost : Nat} (run : PivotCosts perNode span cost) :
    cost ≤ perNode * span := by
  induction run with
  | leaf positive _ bound =>
    exact Nat.le_trans bound (by simpa using Nat.mul_le_mul_left perNode positive)
  | @branch span localCost a b c large localBound _ _ _ aBound bBound cBound =>
    calc
      localCost + a + b + c ≤ perNode + perNode * (span / 9) + perNode * (span / 9) +
          perNode * (span / 9) := by omega
      _ = perNode * (1 + span / 9 + span / 9 + span / 9) := by simp only [Nat.mul_add, Nat.mul_one]
      _ ≤ perNode * span := Nat.mul_le_mul_left _ (by omega)

/-- Completed Quickselect rounds, recording active lengths and per-round costs.
The gap is an obligation for a continuing round and comes from pivot rank and
Hoare partition. This relation makes no claim about any machine trace by itself. -/
inductive SelectionRounds (perElement : Nat) : Nat → Nat → Prop
  | done {n cost : Nat} : 0 < n → cost ≤ perElement * n → SelectionRounds perElement n cost
  | next {n m cost tail : Nat} : 0 < n → m < n → rank n ≤ 2 * (n - m) →
      cost ≤ perElement * n → SelectionRounds perElement m tail →
      SelectionRounds perElement n (cost + tail)

theorem SelectionRounds.potential_bound {perElement n cost : Nat}
    (run : SelectionRounds perElement n cost) : cost ≤ perElement * (4 * potential n) := by
  induction run with
  | @done n cost positive bound =>
    have charge := potential_charge (m := 0) positive (Nat.zero_le n) (by have := rank_le positive; omega)
    exact Nat.le_trans bound (Nat.mul_le_mul_left _ (by simpa [potential] using charge))
  | @next n m cost tail positive smaller gap bound _ rest =>
    have charge := Nat.mul_le_mul_left perElement (potential_charge positive (Nat.le_of_lt smaller) gap)
    rw [Nat.mul_add] at charge
    omega

/-- Integer worst-case upper bound on the total cost of the recorded rounds.
Fixed entry/exit costs can be charged to the first/last round or added separately. -/
theorem SelectionRounds.instruction_bound {perElement n cost : Nat}
    (run : SelectionRounds perElement n cost) : cost ≤ 12 * perElement * n ^ 2 / rank n := by
  apply (Nat.le_div_iff_mul_le (rank_pos n)).2
  calc
    cost * rank n ≤ (perElement * (4 * potential n)) * rank n :=
      Nat.mul_le_mul_right _ run.potential_bound
    _ = (4 * perElement) * (rank n * potential n) := by ac_rfl
    _ ≤ (4 * perElement) * (3 * n ^ 2) := Nat.mul_le_mul_left _ (QuickselectCost.potential_bound n)
    _ = 12 * perElement * n ^ 2 := by
      rw [show 12 = 4 * 3 by decide]
      ac_rfl

private theorem SelectionRounds.fixed_discard (perElement drop rounds : Nat) {n : Nat}
    (dropPos : 0 < drop) (enough : rounds * drop + 1 ≤ n) (gap : rank n ≤ 2 * drop) :
    ∃ cost, SelectionRounds perElement n cost ∧
      (rounds + 1) * (perElement * (n - rounds * drop)) ≤ cost := by
  induction rounds generalizing n with
  | zero => exact ⟨perElement * n, .done (by omega) (Nat.le_refl _), by simp⟩
  | succ rounds ih =>
    have more : rounds * drop + drop + 1 ≤ n := by
      simpa only [Nat.succ_mul] using enough
    have remainingGap : rank (n - drop) ≤ 2 * drop :=
      Nat.le_trans (rank_mono (Nat.sub_le _ _)) gap
    obtain ⟨tail, run, bound⟩ := ih (by omega) remainingGap
    have actualDrop : n - (n - drop) = drop := by omega
    refine ⟨perElement * n + tail,
      .next (by omega) (by omega) (by simpa only [actualDrop] using gap) (Nat.le_refl _) run, ?_⟩
    have remaining : n - (rounds + 1) * drop = n - drop - rounds * drop := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have head : perElement * (n - drop - rounds * drop) ≤ perElement * n :=
      Nat.mul_le_mul_left _ (by omega)
    change ((rounds + 1) + 1) * (perElement * (n - (rounds + 1) * drop)) ≤ _
    rw [remaining, Nat.add_mul, Nat.one_mul]
    omega

/-- The abstract round constraints admit costs of the same asymptotic order
as `instruction_bound`. The witness uses a fixed drop of `rank n` and charges
each round its full budget. There is no machine reachability premise here.

For the concrete algorithm, an adversary would designate two low child
windows at every marked median node. The selected pivot is the maximum of
the designated low leaves, independently of the order of the other elements.
For selection of the maximum, a concrete proof would pull back an adversarial
next suffix through the permutation induced by Hoare's low/high comparisons.
It would also need a machine lower bound on the cost of each such partition. -/
theorem SelectionRounds.abstract_lower_bound (perElement n : Nat) (positive : 0 < n) :
    ∃ cost, SelectionRounds perElement n cost ∧
      (n / (2 * rank n) + 1) * (perElement * (n / 2)) ≤ cost := by
  let rounds := n / (2 * rank n)
  have halved : 2 * (rounds * rank n) ≤ n := by
    calc
      2 * (rounds * rank n) = rounds * (2 * rank n) := by ac_rfl
      _ ≤ n := Nat.div_mul_le_self _ _
  obtain ⟨cost, run, bound⟩ := fixed_discard perElement (rank n) rounds (rank_pos n)
    (n := n) (by omega) (by have h := rank_pos n; omega)
  refine ⟨cost, run, Nat.le_trans ?_ bound⟩
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

end QuickselectCost
