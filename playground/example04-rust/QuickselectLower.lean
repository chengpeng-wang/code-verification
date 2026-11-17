import QuickselectRounds
import QuickselectAdversary
import QuickselectRoundTrace
import QuickselectReinitialize

namespace Example04Rust

open Arm64 ProofLib Example03C Pivot Adversary

set_option autoImplicit false

/-- Specialize the verified driver to the largest active rank. -/
private theorem run_max_round {base : BitVec 64} {initial s : State}
    {frame : SepProp} {xs : List Word}
    (ready : DriverReady base initial s frame xs (xs.length - 1)) :
    ∃ count next output p split,
      CodeStepsN (program base) count s next ∧ xs.length ≤ count ∧
      SelectsPivot xs p ∧ Partition xs output p split ∧
      ((split + 1 = xs.length ∧ Returned initial next) ∨
        (split + 1 < xs.length ∧ ∃ frame', DriverReady base initial next frame'
          (output.drop (split + 1)) ((output.drop (split + 1)).length - 1))) := by
  obtain ⟨output, p, split, count, final, result⟩ := driver_round ready
  refine ⟨count, final, output, p, split, result.steps, result.lower, result.choice, result.partition, ?_⟩
  have fits := result.fits
  have outcome := result.next
  rw [ite_eq_right (show ¬xs.length - 1 < split by omega)] at outcome
  by_cases done : xs.length - 1 = split
  · rw [ite_eq_left done] at outcome
    exact Or.inl ⟨by omega, outcome⟩
  · rw [ite_eq_right done] at outcome
    obtain ⟨nextFrame, readyNext⟩ := outcome
    have indexEq : xs.length - 1 - (split + 1) = (output.drop (split + 1)).length - 1 := by
      rw [List.length_drop, result.outputLen]
      omega
    exact Or.inr ⟨by omega, nextFrame, indexEq ▸ readyNext⟩

/-- Lift the adversarial sequence of source partitions to the corresponding
    machine execution. The chosen rank remains the last index of each active
    slice. Each round's verified local instruction lower bound is charged
    once. -/
theorem execute_max_rounds {base : BitVec 64} {initial s : State} {frame : SepProp}
    {xs : List Word} {work : Nat}
    (run : MaxRounds xs work)
    (ready : DriverReady base initial s frame xs (xs.length - 1)) :
    ∃ count final, CodeStepsN (program base) count s final ∧ Returned initial final ∧ work ≤ count := by
  induction run generalizing s frame with
  | @last xs round =>
    obtain ⟨count, next, output, p, split, steps, cost, picked, partition, outcome⟩ :=
      run_max_round ready
    have successor := (round.realized picked partition).2
    have len := partition.result.perm.length_eq
    rcases outcome with ⟨_, returned⟩ | ⟨proper, _⟩
    · exact ⟨count, next, steps, returned, cost⟩
    · have empty := congrArg List.length successor
      rw [List.length_drop, ← len] at empty
      simp only [List.length_nil] at empty
      omega
  | @next xs suffix work round positive rest ih =>
    obtain ⟨count, next, output, p, split, steps, cost, picked, partition, outcome⟩ :=
      run_max_round ready
    have successor := (round.realized picked partition).2
    have len := partition.result.perm.length_eq
    rcases outcome with ⟨last, _⟩ | ⟨_, frame', nextReady⟩
    · have empty := congrArg List.length successor
      rw [List.length_drop, ← len, last, Nat.sub_self] at empty
      omega
    · rw [successor] at nextReady
      obtain ⟨remaining, final, tail, returned, bound⟩ := ih nextReady
      exact ⟨count + remaining, final, steps.append tail, returned, Nat.add_le_add cost bound⟩

/-- Place the constructed word list in any address layout admitting the
    given call length, then charge the machine trace of the adversarial
    sequence through its first return. -/
theorem quickselect_worst_case_lower : WorstCaseLower 2 := by
  refine ⟨by decide, ?_⟩
  intro n large feasible
  obtain ⟨base, s, frame, k, valid⟩ := feasible
  have size := valid.rustSliceSize
  obtain ⟨xs, work, interval, source, bound⟩ :=
    worst_source 0 n (by omega) (by omega)
  let initial := (s.setMem (s.mem.writeBytes (s.readReg64 .x0) (unpackL xs))).writeReg64
    .x2 (BitVec.ofNat 64 (n - 1))
  have prepared : ValidCall base initial frame n (n - 1) ∧
      initial.mem ⊨ (initial.readReg64 .x0 ↦₆₄* xs) ∗ stackAt initial.sp stackBytes ∗ frame :=
    valid.reinitialize xs interval.length
  obtain ⟨legal, ownership⟩ := prepared
  obtain ⟨ready, prologue, readySpec⟩ :=
    driver_prologue_words base initial frame xs n (n - 1) interval.length legal ownership
  have kEq : n - 1 = xs.length - 1 := by rw [interval.length]
  obtain ⟨count, final, tail, returned, cost⟩ :=
    execute_max_rounds source (kEq ▸ readySpec)
  have steps := prologue.append tail
  have first : FirstReturn base (14 + count) initial final := by
    refine ⟨steps.toStepsN, returned, ?_⟩
    intro m shorter mid earlier
    exact steps.prefix_pc_ne earlier shorter (fetch_outside legal.returnOutside)
  refine ⟨base, initial, frame, n - 1, 14 + count, final, legal, first, ?_⟩
  exact Nat.le_trans bound (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega)))

end Example04Rust
