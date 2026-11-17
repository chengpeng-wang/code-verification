import QuickselectRounds

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false

/-- Every active slice drives a complete ARM64 trace to the original
caller. The recursion is on the length in X1 at the loop header. -/
theorem driver_rounds {base : BitVec 64} {initial start : State} {frame : SepProp}
    {xs : List (BitVec 64)} {k : Nat} (ready : DriverReady base initial start frame xs k) :
    ∃ count final, MachineRounds base 64 start xs.length count final ∧ Returned initial final := by
  generalize length : xs.length = n
  induction n using Nat.strongRecOn generalizing xs start frame k with
  | ind n ih =>
    obtain ⟨output, p, split, count, mid, round⟩ := driver_round ready
    have positive : 0 < n := by have h := ready.index; omega
    have smaller := round.fits
    have outLen := round.outputLen
    have upper : count ≤ 64 * n := by simpa only [length] using round.upper
    have hreg : start.readReg64 .x1 = BitVec.ofNat 64 n := by
      simpa only [length] using ready.lengthReg
    have follow := round.next
    by_cases left : k < split
    · rw [ite_eq_left left] at follow
      obtain ⟨frame', nextReady⟩ := follow
      have newLen : (output.take split).length = split := List.length_take_of_le (by omega)
      have small : split < n := by omega
      obtain ⟨tail, final, rest, returned⟩ := ih split small nextReady newLen
      have gap : QuickselectCost.rank n ≤ 2 * (n - split) := by
        simpa only [length] using round.discardLeft
      exact ⟨count + tail, final, .next hreg positive small gap upper round.steps nextReady.pc rest,
        returned⟩
    · rw [ite_eq_right left] at follow
      by_cases done : k = split
      · rw [ite_eq_left done] at follow
        exact ⟨count, mid, .done hreg positive upper round.steps, follow⟩
      · rw [ite_eq_right done] at follow
        obtain ⟨frame', nextReady⟩ := follow
        have newLen : (output.drop (split + 1)).length = n - (split + 1) := by
          rw [List.length_drop, outLen, length]
        have small : n - (split + 1) < n := by omega
        obtain ⟨tail, final, rest, returned⟩ := ih _ small nextReady newLen
        have gap : QuickselectCost.rank n ≤ 2 * (n - (n - (split + 1))) := by
          simpa only [length] using round.discardRight
        exact ⟨count + tail, final, .next hreg positive small gap upper round.steps nextReady.pc rest,
          returned⟩

private theorem enlarge_budget {base : BitVec 64} {start final : State} {n count : Nat}
    (trace : MachineRounds base 64 start n count final) : MachineRounds base 80 start n count final := by
  induction trace with
  | done reg positive localCost steps => exact .done reg positive (by omega) steps
  | next reg positive smaller discarded localCost steps header _ tail =>
    exact .next reg positive smaller discarded (by omega) steps header tail

private theorem with_prologue {base : BitVec 64} {initial start final : State} {n count : Nat}
    (startReg : initial.readReg64 .x1 = BitVec.ofNat 64 n)
    (setup : CodeStepsN (program base) 14 initial start)
    (trace : MachineRounds base 64 start n count final) :
    MachineRounds base 80 initial n (14 + count) final := by
  cases trace with
  | done _ positive localCost steps =>
    exact .done startReg positive (by omega) (setup.append steps)
  | @next _ mid _ _ m cost tail _ positive smaller discarded localCost steps header rest =>
    rw [← Nat.add_assoc]
    exact .next startReg positive smaller discarded (by omega) (setup.append steps) header (enlarge_budget rest)

/-- Every valid call returns to the caller after at most
`960 * n^2 / 2^floor(log₉ n)` executed ARM64 instructions. The integer
denominator is characterized by `QuickselectCost.rank_eq_pow`.
The count begins at the public function entry and includes the final RET. -/
theorem quickselect_worst_case_upper : WorstCaseUpper (stepBudget 80) := by
  apply upper_of_machine_rounds
  intro base initial frame n k valid
  obtain ⟨xs, start, length, prologue, ready⟩ := driver_prologue base initial frame n k valid
  obtain ⟨count, final, trace, returned⟩ := driver_rounds ready
  rw [length] at trace
  exact ⟨14 + count, final, with_prologue valid.lengthReg prologue trace, returned⟩

end Example04Rust
