import QuickselectDriver
import QuickselectPivotMachine

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- State and counted steps at the point where the driver begins partitioning
around the index in X8. The pivot relation records the helper's actual choice. -/
structure DriverPivot (base : BitVec 64) (initial start final : State) (frame : SepProp)
    (xs : List (BitVec 64)) (k p count : Nat) : Prop where
  steps : CodeStepsN (program base) count start final
  pc : final.pc = base + 0x234#64
  running : final.status = .Running
  loaded : (program base).CodeLoaded final.mem
  sp : final.sp = start.sp
  indexReg : final.readReg64 (.gpr 19#5) = BitVec.ofNat 64 k
  dataReg : final.readReg64 (.gpr 20#5) = start.readReg64 (.gpr 20#5)
  lengthReg : final.readReg64 (.gpr 21#5) = BitVec.ofNat 64 xs.length
  reciprocal : final.readReg64 (.gpr 22#5) = 0xe38e38e38e38e38f#64
  restBase : final.readReg64 (.gpr 23#5) = final.readReg64 (.gpr 20#5) + 8#64
  pivotReg : final.readReg64 (.gpr 8#5) = BitVec.ofNat 64 p
  choice : Pivot.SelectsPivot xs p
  memory : final.mem ⊨ (start.readReg64 (.gpr 20#5) ↦₆₄* xs) ∗
    stackAt start.sp (80 * 18) ∗ savedDriverFrame initial ∗ frame
  budget : count ≤ 16 + 96 * (xs.length / 9)

/-- Both machine branches of pivot selection reach the partition. Small
slices choose zero; large slices execute the recursive pivot helper. -/
theorem driver_choose_pivot {base : BitVec 64} {initial s : State} {frame : SepProp}
    {xs : List (BitVec 64)} {k : Nat} (ready : DriverReady base initial s frame xs k) :
    ∃ p count final, DriverPivot base initial s final frame xs k p count := by
  let n := xs.length
  have fit : n < 2 ^ 64 := by have := ready.size; dsimp [n]; omega
  have positive : 0 < n := Nat.zero_lt_of_lt ready.index
  have nReg : (s.readReg64 .x1).toNat = n := by
    rw [ready.lengthReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  by_cases small : n < 9
  · let copied := s.writeReg64 (.gpr 21#5) (s.readReg64 .x1)
    let zeroed := copied.writeReg64 (.gpr 8#5) 0#64
    let final := (zeroed.setPState (subsPState64 0#64 (s.readReg64 .x1))).setPC (base + 0x234#64)
    have path : CodeStepsN (program base) 6 s final :=
      driver_header_small base s ready.pc ready.running ready.loaded (nReg.symm ▸ positive) (nReg.symm ▸ small)
    refine ⟨0, 6, final, path, rfl, ready.running, ready.loaded, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
      .small small, ready.memory, by omega⟩
    all_goals simp [final, zeroed, copied, wp_norm, arm64_norm,
      ready.lengthReg, ready.indexReg, ready.reciprocal, ready.restBase]
  · have large : 9 ≤ n := Nat.le_of_not_gt small
    let data := s.readReg64 (.gpr 20#5)
    let span := n / 9
    let saved := savedDriverFrame initial ∗ frame
    let entryCopied := s.writeReg64 (.gpr 21#5) (s.readReg64 .x1)
    let dispatch := (entryCopied.setPState (subsPState64 (s.readReg64 .x1) 9#64)).setPC (base + 0x200#64)
    have header : CodeStepsN (program base) 3 s dispatch :=
      driver_header_large base s ready.pc ready.running ready.loaded (nReg.symm ▸ large)
    have magic : dispatch.readReg64 (.gpr 22#5) = 0xe38e38e38e38e38f#64 := by
      simpa [dispatch, entryCopied, wp_norm, arm64_norm] using ready.reciprocal
    obtain ⟨callee, call, cpc, crun, cmem, csp, csave, clr, c0, c1, c2, c5, c3, c4⟩ :=
      pivot_call_setup base dispatch rfl ready.running ready.loaded magic
    have csp' : callee.sp = s.sp := csp
    have cloaded : (program base).CodeLoaded callee.mem := cmem.symm ▸ ready.loaded
    have caligned : callee.spAligned = true := by simpa [State.spAligned, csp'] using ready.aligned
    have hblocks : Pivot.ThreeBlocks xs 0 (4 * span) (8 * span) span := by
      constructor <;> dsimp [span, n] at * <;> omega
    have hdepth : span < 9 ^ 18 := by
      have rust := ready.size
      dsimp [span, n]
      omega
    have hx21 : dispatch.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n := by
      simpa [dispatch, entryCopied, wp_norm, arm64_norm] using ready.lengthReg
    have hx21n : (dispatch.readReg64 (.gpr 21#5)).toNat = n := by
      rw [hx21, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
    have hdata : dispatch.readReg64 (.gpr 20#5) = data := by
      simp [dispatch, entryCopied, data, wp_norm, arm64_norm]
    have shift4 : BitVec.ofNat 64 span <<< 2 = BitVec.ofNat 64 (4 * span) := by
      rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofNat_mul, BitVec.mul_comm]
      rfl
    have shift8 : BitVec.ofNat 64 span <<< 3 = BitVec.ofNat 64 (8 * span) := by
      rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofNat_mul, BitVec.mul_comm]
      rfl
    have c5' : callee.readReg64 (.gpr 5#5) = BitVec.ofNat 64 span := by
      change callee.readReg64 (.gpr 5) = _
      rw [c5, show dispatch.readReg64 (.gpr 21) = dispatch.readReg64 (.gpr 21#5) from rfl, hx21n]
    have c3' : callee.readReg64 .x3 = BitVec.ofNat 64 (4 * span) := by
      change callee.readReg64 (.gpr 3) = _
      rw [c3, show dispatch.readReg64 (.gpr 21) = dispatch.readReg64 (.gpr 21#5) from rfl, hx21n]
      exact shift4
    have c4' : callee.readReg64 (.gpr 4#5) = BitVec.ofNat 64 (8 * span) := by
      change callee.readReg64 (.gpr 4) = _
      rw [c4, show dispatch.readReg64 (.gpr 21) = dispatch.readReg64 (.gpr 21#5) from rfl, hx21n]
      exact shift8
    have pre : callee.mem ⊨ (pivotHelperSpec data xs 0 (4 * span) (8 * span) span 18).pre () callee ∗ saved := by
      rw [pivotHelperSpec, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc]
      refine ⟨⟨c0.trans hdata, c1.trans hx21, c2, c3', c4', c5'⟩, ?_⟩
      rw [cmem, csp']
      exact ready.memory
    obtain ⟨helperCost, picked, helper, returned, abi, post⟩ :=
      pivot_helper_correct base data xs 0 (4 * span) (8 * span) span 18 hblocks fit hdepth (by decide)
        () saved callee cpc crun caligned pre cloaded
    have pickedPC : picked.pc = base + 0x220#64 := returned.1.trans clr
    have pickedSP : picked.sp = s.sp := abi.1.trans csp'
    have pickedLoaded := helper.toStepsN.toSteps.codeLoaded cloaded
    rw [pivotHelperPost, sepExists_sepConj_left, satisfies_sepExists] at post
    obtain ⟨p, post⟩ := post
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc] at post
    obtain ⟨⟨tag, chosenIndex, choice, cost⟩, mem⟩ := post
    have selected : Pivot.SelectsPivot xs p := .large large choice
    have pivotFits := (selected.ranked positive).index
    have same : CalleeSavedPreserved dispatch picked := csave.trans abi.2
    have plen : picked.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n := same.2.2.1.trans hx21
    have pIdx : (picked.readReg64 .x1).toNat < (picked.readReg64 (.gpr 21#5)).toNat := by
      rw [chosenIndex, plen, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : p < 2^64), Nat.mod_eq_of_lt fit]
      exact pivotFits
    let copied := picked.writeReg64 (.gpr 8#5) (picked.readReg64 .x1)
    let final := (copied.setPState (subsPState64 (picked.readReg64 .x1)
      (picked.readReg64 (.gpr 21#5)))).setPC (base + 0x234#64)
    have accept : CodeStepsN (program base) 5 picked final :=
      driver_accept_pivot base picked pickedPC returned.2.2 pickedLoaded tag pIdx
    have p19 : picked.readReg64 (.gpr 19#5) = BitVec.ofNat 64 k := by
      rw [same.1]
      simpa [dispatch, entryCopied, wp_norm, arm64_norm] using ready.indexReg
    have p20 : picked.readReg64 (.gpr 20#5) = data := same.2.1.trans hdata
    have p22 : picked.readReg64 (.gpr 22#5) = 0xe38e38e38e38e38f#64 := same.2.2.2.1.trans magic
    have p23 : picked.readReg64 (.gpr 23#5) = data + 8#64 := by
      rw [same.2.2.2.2.1]
      simpa [dispatch, entryCopied, data, wp_norm, arm64_norm] using ready.restBase
    have path := ((header.append call).append helper).append accept
    have countBound := cost.linear_bound
    refine ⟨p, 3 + 8 + helperCost + 5, final, path, rfl, returned.2.2, pickedLoaded, pickedSP,
      ?_, ?_, ?_, ?_, ?_, ?_, selected, ?_, by omega⟩
    · simpa [final, copied, wp_norm, arm64_norm] using p19
    · simpa [final, copied, wp_norm, arm64_norm] using p20
    · simpa [final, copied, wp_norm, arm64_norm] using plen
    · simpa [final, copied, wp_norm, arm64_norm] using p22
    · simpa [final, copied, p20, wp_norm, arm64_norm] using p23
    · simpa [final, copied, wp_norm, arm64_norm] using chosenIndex
    · rw [csp'] at mem
      exact mem

end Example04Rust
