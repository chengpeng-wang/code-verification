import QuickselectMachine
import QuickselectCost
import ProofLib.Hoare.SafeReaches
import ProofLib.SepLogic.Stack

namespace Example04Rust

open Arm64 ProofLib

set_option autoImplicit false

/-- The driver uses 64 bytes and each recursive pivot helper uses 80 bytes.
    For a valid slice on this target, the length is below 9^19, so there
    can be at most 18 nested helper calls. -/
def stackBytes : Nat := 64 + 80 * 18

/-- A helper depth supported by the divide-by-nine recursion fits the stack
    budget for any length admitted by the Rust slice contract. -/
theorem stack_fits_depth {n depth : Nat} (sliceSize : 8 * n < 2 ^ 63)
    (depthWitness : 9 ^ depth ≤ n) : 64 + 80 * depth ≤ stackBytes := by
  unfold stackBytes
  by_cases possible : depth ≤ 18
  · omega
  · have tooBig := Nat.pow_le_pow_of_le (by decide : 1 < 9) (show 19 ≤ depth by omega)
    omega

/-- The Rust entry-point contract. The byte values are unrestricted. The
    stack, array and frame are disjoint; code is loaded as executable memory. -/
structure ValidCall (codeBase : BitVec 64) (initial : State) (frame : SepProp)
    (n k : Nat) : Prop where
  atEntry : initial.pc = entry codeBase
  running : initial.status = .Running
  loaded : (program codeBase).CodeLoaded initial.mem
  returnOutside : ¬ InRegion codeBase codeSize (initial.readReg64 .lr)
  returnAligned : (initial.readReg64 .lr).toNat % 4 = 0
  stackAligned : initial.spAligned = true
  stackNoWrap : stackBytes ≤ initial.sp.toNat
  rankInRange : k < n
  rustSliceSize : 8 * n < 2 ^ 63
  lengthReg : initial.readReg64 .x1 = BitVec.ofNat 64 n
  rankReg : initial.readReg64 .x2 = BitVec.ofNat 64 k
  arrayAligned : (initial.readReg64 .x0).toNat % 8 = 0
  arrayNoWrap : (initial.readReg64 .x0).toNat + 8 * n < 2 ^ 64
  memory : ∃ bytes : List (BitVec 8), bytes.length = 8 * n ∧
    initial.mem ⊨ (initial.readReg64 .x0 ↦ₛ bytes) ∗ stackAt initial.sp stackBytes ∗ frame

/-- The cost is the number of ARM64 transitions up to the first visit to the
    caller PC, including the RET. A normal return must restore SP. -/
def FirstReturn (codeBase : BitVec 64) (count : Nat) (initial final : State) : Prop :=
  StepsN (program codeBase) count initial final ∧ Returned initial final ∧
    ∀ m < count, ∀ mid, StepsN (program codeBase) m initial mid →
      mid.pc ≠ initial.readReg64 .lr

/-- Upper-bound goal for review. Every valid call must return within the budget.
    A bound over successful executions alone would omit the termination claim. -/
def WorstCaseUpper (budget : Nat → Nat) : Prop :=
  ∀ (codeBase : BitVec 64) (initial : State) (frame : SepProp) (n k : Nat),
    ValidCall codeBase initial frame n k →
      ∃ count final, FirstReturn codeBase count initial final ∧ count ≤ budget n

/-- The matching lower-bound goal. For every feasible length at or above the
    first sampling threshold (nine), a legal input and rank must cost at least
    `n^2 / (factor * rank n)`. Fixing the threshold keeps this goal meaningful
    on a finite address space. The inequality avoids rounded-down division. -/
def WorstCaseLower (factor : Nat) : Prop :=
  0 < factor ∧ ∀ n ≥ 9,
    (∃ codeBase initial frame k, ValidCall codeBase initial frame n k) →
      ∃ codeBase initial frame k count final,
        ValidCall codeBase initial frame n k ∧ FirstReturn codeBase count initial final ∧
          n ^ 2 ≤ factor * count * QuickselectCost.rank n

/-- The staircase denominator is exactly `2 ^ floor(log₉ n)` for positive
    lengths. `perElement` is a bound to establish from the actual binary. -/
def stepBudget (perElement n : Nat) : Nat :=
  12 * perElement * n ^ 2 / QuickselectCost.rank n

/-- The selected index is in range, the output preserves multiplicities, and
    its elements to the left/right are respectively ≤/≥ the selected value,
    using signed i64 comparison. This is the direct functional specification. -/
def Selects (input output : List (BitVec 64)) (k : Nat) : Prop :=
  input.Perm output ∧ k < output.length ∧
    (∀ x ∈ output.take k, x.toInt ≤ output[k]!.toInt) ∧
    (∀ x ∈ output.drop (k + 1), output[k]!.toInt ≤ x.toInt)

theorem FirstReturn.count_eq {codeBase : BitVec 64} {initial final₁ final₂ : State}
    {count₁ count₂ : Nat} (one : FirstReturn codeBase count₁ initial final₁)
    (two : FirstReturn codeBase count₂ initial final₂) : count₁ = count₂ := by
  rcases Nat.lt_trichotomy count₁ count₂ with lt | eq | gt
  · exact (two.2.2 count₁ lt final₁ one.1 one.2.1.1).elim
  · exact eq
  · exact (one.2.2 count₂ gt final₂ two.1 two.2.1.1).elim

end Example04Rust
