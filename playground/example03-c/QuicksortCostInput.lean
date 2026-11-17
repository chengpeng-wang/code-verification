import ProofLib.BV.MaskLemmas
import ProofLib.Disproof.ModelBuilder
import ProofLib.SepLogic.Stack

namespace Example03C

open Arm64 ProofLib ProofLib.Disproof

set_option autoImplicit false

/-- The disjoint writable array and stack for an equal-byte input of length at most 2^56. -/
private def equalRegions (n : Nat) (byte : BitVec 8) : List DisproofRegion :=
  [.rwBytes 0x1000_0000_0000_0000#64 (List.replicate n byte),
   .rwRegion 0x4000_0000_0000_0000#64 (48 * n)]

/-- The caller address 0x2000 lies outside the 184-byte image at 0x1000. -/
def equalInputState (prog : Program) (n : Nat) (byte : BitVec 8) : State :=
  mkDisproofState prog 0x1000#64 (0x4000_0000_0000_0000#64 + BitVec.ofNat 64 (48 * n)) 0x2000#64
    [(.x0, 0x1000_0000_0000_0000#64), (.x1, BitVec.ofNat 64 n)] (equalRegions n byte)

/-- For each length in the stated range, the witness meets the actual entry
requirements with a writable array and stack and an executable copy of the program. -/
theorem equalInputState_valid (prog : Program) (n : Nat) (byte : BitVec 8)
    (hbase : prog.base = 0x1000#64) (hlen : prog.code.length = 184) (hn : n ≤ 2 ^ 56) :
    let initial := equalInputState prog n byte
    initial.pc = 0x1000#64 ∧ initial.readReg64 .lr = 0x2000#64 ∧
    initial.status = .Running ∧ initial.spAligned = true ∧ prog.CodeLoaded initial.mem ∧
    initial.readReg64 .x1 = BitVec.ofNat 64 n ∧ 48 * n ≤ 2^64 ∧
    (initial.mem ⊨ (initial.readReg64 .x0 ↦ₛ List.replicate n byte) ∗
      stackAt initial.sp (48 * n) ∗ SepProp.emp) := by
  dsimp only
  have hvalid : DisproofRegionsValidB 0x1000#64 184 (equalRegions n byte) = true := by
    simp only [equalRegions, DisproofRegionsValidB, RegionsPairwiseDisjointB, DisproofRegion.toSpec,
      List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq,
      MemRegionSpec.disjointB_iff, DisjointRegions, MemRegionSpec.rwBytes, MemRegionSpec.rwRegion,
      List.length_replicate, BitVec.reduceSub, BitVec.reduceToNat, true_and, and_true]
    omega
  have hm := buildDisproofMem_satisfies prog (equalRegions n byte) hbase hlen hvalid
  have hloaded := buildDisproofMem_codeLoaded_of_valid prog (equalRegions n byte) hbase hlen hvalid
  refine ⟨rfl, rfl, rfl, ?_, hloaded, rfl, by omega, ?_⟩
  · change ((0x4000_0000_0000_0000#64 + BitVec.ofNat 64 (48 * n)) &&& 15#64 == 0#64) = true
    rw [BitVec.beq_and_zero_eq_true_iff_mod_eq_zero _ _ 16]
    rw [BitVec.toNat_add]
    change ((0x4000_0000_0000_0000 + (48 * n) % 2 ^ 64) % 2 ^ 64) % 16 = 0
    rw [Nat.mod_eq_of_lt (by omega : 48 * n < 2 ^ 64)]
    rw [Nat.mod_eq_of_lt (by omega : 0x4000_0000_0000_0000 + 48 * n < 2 ^ 64)]
    omega
  · change (equalInputState prog n byte).mem ⊨
      (0x1000_0000_0000_0000#64 ↦ₛ List.replicate n byte) ∗
      stackAt (0x4000_0000_0000_0000#64 + BitVec.ofNat 64 (48 * n)) (48 * n) ∗ SepProp.emp
    rw [stackAt, BitVec.add_sub_cancel, sepConj_emp]
    exact hm

end Example03C
