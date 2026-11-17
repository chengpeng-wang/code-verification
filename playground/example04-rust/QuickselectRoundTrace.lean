import CountedExecution
import QuickselectSpec

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false

/-- Counted machine trace split at the driver's active-slice loop header.
    A continuing segment must establish both its linear cost and the amount
    it discarded. Each segment records the actual instruction steps. The
    first segment may include the prologue, and the last includes the RET. -/
inductive MachineRounds (base : BitVec 64) (perElement : Nat) :
    State → Nat → Nat → State → Prop where
  | done {s final : State} {n count : Nat}
      (length : s.readReg64 .x1 = BitVec.ofNat 64 n)
      (positive : 0 < n) (localCost : count ≤ perElement * n)
      (steps : CodeStepsN (program base) count s final) :
      MachineRounds base perElement s n count final
  | next {s mid final : State} {n m count tail : Nat}
      (length : s.readReg64 .x1 = BitVec.ofNat 64 n)
      (positive : 0 < n) (smaller : m < n)
      (discarded : QuickselectCost.rank n ≤ 2 * (n - m))
      (localCost : count ≤ perElement * n)
      (steps : CodeStepsN (program base) count s mid)
      (header : mid.pc = base + 0x1e4#64)
      (rest : MachineRounds base perElement mid m tail final) :
      MachineRounds base perElement s n (count + tail) final

theorem MachineRounds.steps {base : BitVec 64} {perElement n count : Nat}
    {s final : State} (trace : MachineRounds base perElement s n count final) :
    CodeStepsN (program base) count s final := by
  induction trace with
  | done _ _ _ steps => exact steps
  | next _ _ _ _ _ steps _ _ rest => exact steps.append rest

theorem MachineRounds.costs {base : BitVec 64} {perElement n count : Nat}
    {s final : State} (trace : MachineRounds base perElement s n count final) :
    QuickselectCost.SelectionRounds perElement n count := by
  induction trace with
  | done _ positive localCost _ => exact .done positive localCost
  | next _ positive smaller discarded localCost _ _ _ rest =>
    exact .next positive smaller discarded localCost rest

theorem fetch_outside {base pc : BitVec 64}
    (outside : ¬ InRegion base codeSize pc) : (program base).fetch pc = none := by
  have length : (program base).code.length = codeSize := by
    change codeBytes.length = codeSize
    decide +kernel
  have off : (program base).code.length ≤ (pc - base).toNat := by
    rw [length]
    exact Nat.le_of_not_gt outside
  unfold Program.fetch
  split
  · rfl
  · unfold Program.readWordOff
    split
    · rfl
    · rw [show (program base).base = base from rfl, List.drop_eq_nil_of_le off]
      rfl

/-- End-to-end upper-bound reduction. The remaining machine proof obligation is
    to construct a `MachineRounds` trace ending in a normal return for every
    `ValidCall`, with one uniform instruction budget per active element. -/
theorem upper_of_machine_rounds (perElement : Nat)
    (rounds : ∀ (base : BitVec 64) (s : State) (frame : SepProp) (n k : Nat),
      ValidCall base s frame n k →
        ∃ count final, MachineRounds base perElement s n count final ∧ Returned s final) :
    WorstCaseUpper (stepBudget perElement) := by
  intro base s frame n k valid
  obtain ⟨count, final, trace, returned⟩ := rounds base s frame n k valid
  have steps := trace.steps
  refine ⟨count, final, ⟨steps.toStepsN, returned, ?_⟩, trace.costs.instruction_bound⟩
  intro m shorter mid earlier
  exact steps.prefix_pc_ne earlier shorter (fetch_outside valid.returnOutside)

end Example04Rust
