import QuickselectDriverPivot
import QuickselectPartitionInvariant
import QuickselectAdversaryMachine
import QuickselectRoundTrace

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- A pivot selection and partition of the active slice. The exact linked
trace stops at the branch choosing a continuation. Its memory postcondition
retains the helper stack and the original caller's saved registers. -/
structure DriverPartition (base : BitVec 64) (initial start final : State) (frame : SepProp)
    (xs output : List (BitVec 64)) (k p split count : Nat) : Prop where
  steps : CodeStepsN (program base) count start final
  pc : final.pc = base + 0x2f4#64
  running : final.status = .Running
  loaded : (program base).CodeLoaded final.mem
  sp : final.sp = start.sp
  indexReg : final.readReg64 (.gpr 19#5) = BitVec.ofNat 64 k
  dataReg : final.readReg64 (.gpr 20#5) = start.readReg64 (.gpr 20#5)
  lengthReg : final.readReg64 (.gpr 21#5) = BitVec.ofNat 64 xs.length
  reciprocal : final.readReg64 (.gpr 22#5) = 0xe38e38e38e38e38f#64
  restBase : final.readReg64 (.gpr 23#5) = final.readReg64 (.gpr 20#5) + 8#64
  splitReg : final.readReg64 .x1 = BitVec.ofNat 64 split
  flags : final.pstate = subsPState64 (final.readReg64 (.gpr 19#5)) (final.readReg64 .x1)
  choice : Pivot.SelectsPivot xs p
  partition : Adversary.Partition xs output p split
  fits : split < xs.length
  outputLen : output.length = xs.length
  discardLeft : QuickselectCost.rank xs.length ≤ 2 * (xs.length - split)
  discardRight : QuickselectCost.rank xs.length ≤ 2 * (xs.length - (xs.length - (split + 1)))
  memory : final.mem ⊨ (start.readReg64 (.gpr 20#5) ↦₆₄* output) ∗
    stackAt start.sp (80 * 18) ∗ savedDriverFrame initial ∗ frame
  lower : xs.length ≤ count
  upper : count ≤ 56 * xs.length

theorem driver_partition {base : BitVec 64} {initial start : State} {frame : SepProp}
    {xs : List (BitVec 64)} {k : Nat} (ready : DriverReady base initial start frame xs k) :
    ∃ output p split count final, DriverPartition base initial start final frame xs output k p split count := by
  have size := ready.size
  have positive := Nat.zero_lt_of_lt ready.index
  have bound : xs.length < 2 ^ 64 := by omega
  obtain ⟨p, chooseCost, selected, pivot⟩ := driver_choose_pivot ready
  have chosen := pivot.choice.ranked positive
  let data := selected.readReg64 (.gpr 20#5)
  let protectedFrame := stackAt start.sp (80 * 18) ∗ savedDriverFrame initial ∗ frame
  have owned : selected.mem ⊨ (data ↦₆₄* xs) ∗ protectedFrame := by
    rw [show data = start.readReg64 (.gpr 20#5) from pivot.dataReg]
    exact pivot.memory
  obtain ⟨before, prep, runBefore, spBefore, loadedBefore, preserved, _, i0, limit, j0, pcBefore, arrBefore⟩ :=
    partition_start base selected xs p protectedFrame pivot.pc pivot.running pivot.loaded pivot.pivotReg
      pivot.lengthReg bound chosen.index owned
  let first := swapWords xs 0 p
  have firstLen : first.length = xs.length := swapWords_length ..
  have head : first[0]! = xs[p]! := by
    unfold first
    rw [swapWords_get positive]
    by_cases z : 0 = p <;> simp [z]
  obtain ⟨v, rest, shape⟩ := List.exists_cons_of_ne_nil (l := first) (by intro h; rw [h] at firstLen; simp at firstLen; omega)
  have value : v = xs[p]! := by simpa [shape] using head
  subst v
  have restLen : rest.length + 1 = xs.length := by
    rw [shape, List.length_cons] at firstLen
    exact firstLen
  have arr : before.mem ⊨ (data ↦₆₄* (xs[p]! :: rest)) ∗ protectedFrame := by
    rwa [← shape]
  have pc : before.pc = base + (if rest = [] then 0x28c#64 else 0x258#64) := by
    rw [pcBefore]
    have iff : xs.length = 1 ↔ rest = [] := by
      rw [← List.length_eq_zero_iff]
      omega
    simp only [iff]
  have cursor (r : Reg) (eq : before.readReg64 r = BitVec.ofNat 64 (xs.length - 1)) :
      (before.readReg64 r).toNat = rest.length := by
    rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have beforeRest : before.readReg64 (.gpr 23#5) = data + 8#64 :=
    preserved.2.2.2.2.1.trans pivot.restBase
  obtain ⟨scanCost, scanned, rest', swaps, scan⟩ :=
    partition_scan_correct base data before xs[p]! rest protectedFrame pc runBefore loadedBefore i0
      (cursor _ limit) (cursor _ j0) preserved.2.1 beforeRest arr (by omega)
  let middle := xs[p]! :: rest'
  let split := (scanned.readReg64 .x1).toNat
  let output := swapWords middle 0 split
  have midLen : middle.length = xs.length := by
    simpa only [middle, List.length_cons, ← scan.perm.length_eq] using restLen
  have splitFits : split < xs.length := by
    have h := scan.inv.leftFits
    change split ≤ rest'.length at h
    simp only [middle, List.length_cons] at midLen
    omega
  have oldPerm : xs.Perm (xs[p]! :: rest) := shape ▸ swapWords_perm (by omega) chosen.index
  have scanLE : Pivot.countLE xs xs[p]! ≤ 2 * split + 1 := by
    unfold Pivot.countLE
    rw [oldPerm.countP_eq]
    exact scan.rankLE
  have scanGE : Pivot.countGE xs xs[p]! ≤ 2 * (xs.length - (split + 1)) + 2 := by
    unfold Pivot.countGE
    rw [oldPerm.countP_eq, show xs.length - (split + 1) = rest.length - split by omega]
    exact scan.rankGE
  have discard := Pivot.hoare_discard chosen splitFits scanLE scanGE
  have scannedSave : CalleeSavedPreserved selected scanned := preserved.trans scan.regs.1
  have scannedLen : scanned.readReg64 (.gpr 21#5) = BitVec.ofNat 64 middle.length := by
    rw [midLen, scannedSave.2.2.1, pivot.lengthReg]
  have scanOwned : scanned.mem ⊨ (scanned.readReg64 (.gpr 20#5) ↦₆₄* middle) ∗ protectedFrame := by
    rw [scannedSave.2.1]
    exact scan.array
  have splitReg : scanned.readReg64 .x1 = BitVec.ofNat 64 split := by
    simp [split]
  obtain ⟨final, finish, fpc, frun, fsp, floaded, fsave, fsplit, flags, result⟩ :=
    partition_finish base scanned middle split protectedFrame scan.pc scan.running scan.loaded
      splitReg scannedLen (by omega) (by omega) scanOwned
  have trace : PartitionTrace data before.mem 0 (xs.length - 1) scanned.mem split
      (scanned.readReg64 (.gpr 9#5)).toNat := by
    simpa only [show xs.length - 1 = rest.length by omega] using scan.trace
  have part : Adversary.Partition xs output p split :=
    Adversary.partition_trace_partition chosen.index trace arrBefore scan.array midLen
  have same := scannedSave.trans fsave
  have sp : final.sp = start.sp := fsp.trans (scan.sp.trans (spBefore.trans pivot.sp))
  have combined := ((pivot.steps.append prep).append scan.steps).append finish
  have upper := scan.upper
  have lower := scan.lower
  have overhead := pivot.budget
  refine ⟨output, p, split, chooseCost + 9 + scanCost + 7, final, combined, fpc, frun, floaded, sp,
    same.1.trans pivot.indexReg, same.2.1.trans pivot.dataReg, same.2.2.1.trans pivot.lengthReg,
    same.2.2.2.1.trans pivot.reciprocal, ?_, fsplit.trans splitReg, flags, pivot.choice, part, splitFits,
    (swapWords_length ..).trans midLen, discard.1, discard.2, ?_, by omega, by omega⟩
  · rw [same.2.2.2.2.1, same.2.1, pivot.restBase]
  · rw [scannedSave.2.1, pivot.dataReg] at result
    exact result

/-- One full machine round, including the transition to the next header or
the returning epilogue. Both bounds count the same decoded execution. -/
structure DriverRoundResult (base : BitVec 64) (initial start final : State) (frame : SepProp)
    (xs output : List (BitVec 64)) (k p split count : Nat) : Prop where
  steps : CodeStepsN (program base) count start final
  choice : Pivot.SelectsPivot xs p
  partition : Adversary.Partition xs output p split
  fits : split < xs.length
  outputLen : output.length = xs.length
  discardLeft : QuickselectCost.rank xs.length ≤ 2 * (xs.length - split)
  discardRight : QuickselectCost.rank xs.length ≤ 2 * (xs.length - (xs.length - (split + 1)))
  lower : xs.length ≤ count
  upper : count ≤ 64 * xs.length
  next :
    if k < split then
      ∃ frame', DriverReady base initial final frame' (output.take split) k
    else if k = split then
      Returned initial final
    else
      ∃ frame', DriverReady base initial final frame' (output.drop (split + 1)) (k - (split + 1))

theorem driver_round {base : BitVec 64} {initial start : State} {frame : SepProp}
    {xs : List (BitVec 64)} {k : Nat} (ready : DriverReady base initial start frame xs k) :
    ∃ output p split count final, DriverRoundResult base initial start final frame xs output k p split count := by
  obtain ⟨output, p, split, count, partitioned, part⟩ := driver_partition ready
  have size := ready.size
  have rank := ready.index
  have bound : xs.length < 2 ^ 64 := by omega
  obtain ⟨tailCount, next, tail, mem, sp, running, x22, x23, nextCase⟩ :=
    quickselect_driver_tail base partitioned xs.length k split part.pc part.running part.loaded
      bound rank part.fits part.lengthReg part.indexReg part.splitReg part.flags
  let data := start.readReg64 (.gpr 20#5)
  let helper := stackAt start.sp (80 * 18)
  let saved := savedDriverFrame initial
  have owned : next.mem ⊨ (data ↦₆₄* output) ∗ helper ∗ saved ∗ frame := by
    rw [mem]
    exact part.memory
  have nsp : next.sp = start.sp := sp.trans part.sp
  have aligned : next.spAligned = true := by
    simpa only [State.spAligned, nsp] using ready.aligned
  have loaded : (program base).CodeLoaded next.mem := mem.symm ▸ part.loaded
  have magic := x22.trans part.reciprocal
  have outLen := part.outputLen
  have splitFits := part.fits
  have upper := part.upper
  have lower := part.lower
  by_cases hleft : k < split
  · rw [ite_eq_left hleft] at nextCase
    obtain ⟨rfl, npc, nlen, nidx, ndata⟩ := nextCase
    have before : split ≤ output.length := by omega
    have len : (output.take split).length = split := List.length_take_of_le before
    let leftOver := wordAddr data split ↦₆₄* output.drop split
    let frame' := leftOver ∗ frame
    have submem := word_array_take owned before
    rw [sepConj_left_comm leftOver helper, sepConj_left_comm leftOver saved] at submem
    have leftReady : DriverReady base initial next frame' (output.take split) k := by
      refine ⟨npc, running, loaded, nsp.trans ready.sp, aligned, by omega, by omega, ?_, nidx, magic, ?_, ?_⟩
      · rwa [len]
      · change next.readReg64 (.gpr 23#5) = next.readReg64 (.gpr 20#5) + 8#64
        rw [show next.readReg64 (.gpr 20#5) = partitioned.readReg64 (.gpr 20#5) from ndata, x23, part.restBase]
      · rw [show next.readReg64 (.gpr 20#5) = data from ndata.trans part.dataReg, nsp]
        exact submem
    refine ⟨output, p, split, count + 1, next, part.steps.append tail, part.choice, part.partition,
      part.fits, outLen, part.discardLeft, part.discardRight, by omega, by omega, ?_⟩
    rw [ite_eq_left hleft]
    exact ⟨frame', leftReady⟩
  · rw [ite_eq_right hleft] at nextCase
    by_cases hdone : k = split
    · rw [ite_eq_left hdone] at nextCase
      obtain ⟨rfl, npc⟩ := nextCase
      rw [sepConj_left_comm helper saved, sepConj_left_comm (data ↦₆₄* output) saved] at owned
      obtain ⟨_, final, P, ret, _, _, _, rfl, returned⟩ :=
        driver_restore_stack base initial next npc running aligned (nsp.trans ready.sp)
          ((data ↦₆₄* output) ∗ helper ∗ frame) owned loaded
      refine ⟨output, p, split, count + 2 + 5, final, (part.steps.append tail).append ret,
        part.choice, part.partition, part.fits, outLen, part.discardLeft, part.discardRight,
        by omega, by omega, ?_⟩
      rwa [ite_eq_right hleft, ite_eq_left hdone]
    · rw [ite_eq_right hdone] at nextCase
      obtain ⟨rfl, npc, nlen, nidx, ndata, _⟩ := nextCase
      let addr := wordAddr data (split + 1)
      let final := (next.writeReg64 (.gpr 23#5) (next.readReg64 (.gpr 20#5) + 8#64)).setPC (base + 0x1e4#64)
      have jump : CodeStepsN (program base) 1 next final := driver_right_header base next npc running loaded
      have skippedNat : (BitVec.ofNat 64 (split + 1)).toNat = split + 1 :=
        Nat.mod_eq_of_lt (by omega)
      have addrEq : next.readReg64 (.gpr 20#5) = addr := by
        change next.readReg64 (.gpr 20) = _
        rw [ndata, show partitioned.readReg64 (.gpr 20) = partitioned.readReg64 (.gpr 20#5) from rfl,
          part.dataReg, ← wordAddr_shift, skippedNat]
      have dropLen : (output.drop (split + 1)).length = xs.length - (split + 1) := by
        rw [List.length_drop, outLen]
      have before : split + 1 ≤ output.length := by omega
      let leftOver := data ↦₆₄* output.take (split + 1)
      let frame' := leftOver ∗ frame
      have submem := word_array_drop owned before
      rw [sepConj_left_comm leftOver helper, sepConj_left_comm leftOver saved] at submem
      have rightReady : DriverReady base initial final frame' (output.drop (split + 1)) (k - (split + 1)) := by
        refine ⟨rfl, running, loaded, nsp.trans ready.sp, aligned, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [final, wp_norm, arm64_norm, dropLen] using nlen
        · change final.readReg64 (.gpr 19#5) = _
          have nidx' : next.readReg64 (.gpr 19#5) = _ := nidx
          simpa [final, wp_norm, arm64_norm] using nidx'
        · simpa [final, wp_norm, arm64_norm] using magic
        · simp [final, wp_norm, arm64_norm]
        · have d : final.readReg64 (.gpr 20#5) = addr := by
            simpa [final, wp_norm, arm64_norm] using addrEq
          have s : final.sp = start.sp := nsp
          rw [d, s]
          exact submem
      refine ⟨output, p, split, count + 7 + 1, final, (part.steps.append tail).append jump,
        part.choice, part.partition, part.fits, outLen, part.discardLeft, part.discardRight,
        by omega, by omega, ?_⟩
      rw [ite_eq_right hleft, ite_eq_right hdone]
      exact ⟨frame', rightReady⟩

end Example04Rust
