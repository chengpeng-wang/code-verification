import QuickselectDriverStack
import QuickselectPartitionStart
import QuickselectMachineTail
import QuickselectSpec

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem cells_to_words {m : Memory} {data : BitVec 64} {n : Nat} {frame : SepProp}
    (memory : m ⊨ cells data n ∗ frame) :
    ∃ xs : List (BitVec 64), xs.length = n ∧ m ⊨ (data ↦₆₄* xs) ∗ frame := by
  induction n generalizing data frame with
  | zero => exact ⟨[], rfl, by simpa only [cells_zero, pointsToWords64_nil] using memory⟩
  | succ n ih =>
    rw [cells_succ, sepExists_sepConj_left, satisfies_sepExists] at memory
    obtain ⟨x, memory⟩ := memory
    rw [sepConj_assoc, sepConj_left_comm] at memory
    obtain ⟨xs, len, words⟩ := ih memory
    refine ⟨x :: xs, by simp [len], ?_⟩
    rw [pointsToWords64_cons, sepConj_assoc, sepConj_left_comm]
    exact words

/-- Convert the owned bytes in the public calling contract into the word
array used by the machine proof. This reads the same memory in 8-byte cells. -/
theorem valid_call_words {base : BitVec 64} {s : State} {frame : SepProp} {n k : Nat}
    (valid : ValidCall base s frame n k) :
    ∃ xs : List (BitVec 64), xs.length = n ∧
      s.mem ⊨ (s.readReg64 .x0 ↦₆₄* xs) ∗ stackAt s.sp stackBytes ∗ frame := by
  obtain ⟨bytes, length, mem⟩ := valid.memory
  have region := Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion_of_length length)) mem
  have size := valid.rustSliceSize
  rw [memRegion_cells _ _ (by omega)] at region
  exact cells_to_words region

/-- State at the active-slice loop header. The stack frame belonging to
the original caller stays disjoint from the active slice and helper stack. -/
structure DriverReady (base : BitVec 64) (initial s : State) (frame : SepProp)
    (xs : List (BitVec 64)) (k : Nat) : Prop where
  pc : s.pc = base + 0x1e4#64
  running : s.status = .Running
  loaded : (program base).CodeLoaded s.mem
  sp : s.sp = initial.sp - 64#64
  aligned : s.spAligned = true
  size : 8 * xs.length < 2 ^ 63
  index : k < xs.length
  lengthReg : s.readReg64 .x1 = BitVec.ofNat 64 xs.length
  indexReg : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 k
  reciprocal : s.readReg64 (.gpr 22#5) = 0xe38e38e38e38e38f#64
  restBase : s.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 20#5) + 8#64
  memory : s.mem ⊨ (s.readReg64 (.gpr 20#5) ↦₆₄* xs) ∗
    stackAt s.sp (80 * 18) ∗ savedDriverFrame initial ∗ frame

/-- The complete function prologue consumes 14 decoded instructions and
establishes the loop invariant for all valid entry states. -/
theorem driver_prologue_words (base : BitVec 64) (s : State) (frame : SepProp)
    (xs : List (BitVec 64)) (n k : Nat) (length : xs.length = n)
    (valid : ValidCall base s frame n k)
    (mem : s.mem ⊨ (s.readReg64 .x0 ↦₆₄* xs) ∗ stackAt s.sp stackBytes ∗ frame) :
    ∃ ready, CodeStepsN (program base) 14 s ready ∧ DriverReady base s ready frame xs k := by
  have hsize := valid.rustSliceSize
  have hRank := valid.rankInRange
  have rank : (s.readReg64 .x2).toNat < (s.readReg64 .x1).toNat := by
    rw [valid.rankReg, valid.lengthReg, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := valid.rankInRange; omega : k < 2^64),
      Nat.mod_eq_of_lt (by omega : n < 2^64)]
    exact valid.rankInRange
  let checked := (s.setPState (subsPState64 (s.readReg64 .x2) (s.readReg64 .x1))).setPC (base + 0x1b4#64)
  have check : CodeStepsN (program base) 2 s checked :=
    driver_check_rank base s valid.atEntry valid.running valid.loaded rank
  let top := s.sp - 64#64
  let array := s.readReg64 .x0 ↦₆₄* xs
  let helperStack := stackAt top (80 * 18)
  have splitStack : stackAt s.sp stackBytes = helperStack ∗ stackAt s.sp 64 :=
    stackAt_region s.sp (80 * 18) 64 (by decide)
  have forSave : checked.mem ⊨ stackAt checked.sp 64 ∗ array ∗ helperStack ∗ frame := by
    change s.mem ⊨ stackAt s.sp 64 ∗ array ∗ helperStack ∗ frame
    rw [splitStack, sepConj_assoc, sepConj_left_comm helperStack] at mem
    rw [sepConj_left_comm]
    exact mem
  obtain ⟨_, saved, P, save, savedPC, savedRun, savedMem, rfl, savedSP, x0, x1, x2, savedFrame⟩ :=
    driver_save_stack base checked rfl valid.running valid.stackAligned
      (array ∗ helperStack ∗ frame) forSave valid.loaded
  have savedLoaded := save.toStepsN.toSteps.codeLoaded valid.loaded
  have sframe : savedDriverFrame checked = savedDriverFrame s := rfl
  have owned : saved.mem ⊨ savedDriverFrame s ∗ (array ∗ helperStack ∗ frame) := by
    rw [← sframe]
    exact Satisfies.mono (sepConj_mono_left savedFrame) savedMem
  obtain ⟨_, ready, Q, init, readyPC, readyRun, readyMem, rfl,
      sameSP, sameMem, x19, x20, x22, x23, rlen, rfl⟩ :=
    driver_initialize base saved (savedDriverFrame s) savedPC savedRun
      (array ∗ helperStack ∗ frame) owned savedLoaded
  have spEq : ready.sp = s.sp - 64#64 := sameSP.trans savedSP
  have readyLoaded := init.toStepsN.toSteps.codeLoaded savedLoaded
  have align : ready.spAligned = true := by
    simpa only [State.spAligned, spEq] using s.spAligned_sub 64#64 valid.stackAligned
  have dataEq : ready.readReg64 (.gpr 20#5) = s.readReg64 .x0 := x20.trans x0
  refine ⟨ready, (check.append save).append init, ?_⟩
  refine ⟨readyPC, readyRun, readyLoaded, spEq, align, by omega, by omega, ?_, ?_, x22, ?_, ?_⟩
  · rw [rlen, x1, length]
    exact valid.lengthReg
  · exact x19.trans (x2.trans valid.rankReg)
  · rw [dataEq, x23, x0]
    rfl
  · rw [dataEq, spEq]
    change ready.mem ⊨ array ∗ helperStack ∗ savedDriverFrame s ∗ frame
    rw [sepConj_left_comm (savedDriverFrame s) array,
      sepConj_left_comm (savedDriverFrame s) helperStack] at readyMem
    exact readyMem

theorem driver_prologue (base : BitVec 64) (s : State) (frame : SepProp) (n k : Nat)
    (valid : ValidCall base s frame n k) :
    ∃ xs ready, xs.length = n ∧ CodeStepsN (program base) 14 s ready ∧
      DriverReady base s ready frame xs k := by
  obtain ⟨xs, length, mem⟩ := valid_call_words valid
  obtain ⟨ready, steps, readyInv⟩ := driver_prologue_words base s frame xs n k length valid mem
  exact ⟨xs, ready, length, steps, readyInv⟩

/-- Swap the pivot in slot zero with the final left cursor. The seven
instructions preserve the framed array ownership and set the flags used
to choose a continuation. -/
theorem partition_finish (base : BitVec 64) (s : State) (xs : List (BitVec 64))
    (split : Nat) (frame : SepProp)
    (pc : s.pc = base + 0x2d8#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (splitReg : s.readReg64 .x1 = BitVec.ofNat 64 split)
    (lenReg : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 xs.length)
    (bound : xs.length < 2 ^ 64) (fits : split < xs.length)
    (owned : s.mem ⊨ (s.readReg64 (.gpr 20#5) ↦₆₄* xs) ∗ frame) :
    ∃ t, CodeStepsN (program base) 7 s t ∧ t.pc = base + 0x2f4#64 ∧
      t.status = .Running ∧ t.sp = s.sp ∧ (program base).CodeLoaded t.mem ∧
      CalleeSavedPreserved s t ∧ t.readReg64 .x1 = s.readReg64 .x1 ∧
      t.pstate = subsPState64 (t.readReg64 (.gpr 19#5)) (t.readReg64 .x1) ∧
      t.mem ⊨ (s.readReg64 (.gpr 20#5) ↦₆₄* swapWords xs 0 split) ∗ frame := by
  let data := s.readReg64 (.gpr 20#5)
  let slot := data + (s.readReg64 .x1 <<< 3)
  have toNatSplit : (s.readReg64 .x1).toNat = split := by
    rw [splitReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have physical : wordAddr data split = slot := by
    rw [← toNatSplit, wordAddr_shift]
  have access0 := word_at owned (i := 0) (by omega)
  rw [wordAddr_zero] at access0
  have accessSplit := word_at owned fits
  rw [physical] at accessSplit
  have inBounds : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 21#5)).toNat := by
    rw [toNatSplit, lenReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact fits
  let loadFlags := subsPState64 (s.readReg64 .x1) (s.readReg64 (.gpr 21#5))
  let firstLoad := (s.setPState loadFlags).writeReg64 (.gpr 8#5) (s.mem.read64 slot)
  let loadedVals := (firstLoad.writeReg64 (.gpr 9#5) (s.mem.read64 data)).setPC (base + 0x2e8#64)
  have loads : CodeStepsN (program base) 4 s loadedVals :=
    quickselect_partition_loads base s pc running loaded inBounds access0.2.1 accessSplit.2.1
  have w0 : loadedVals.mem.canWrite (loadedVals.readReg64 (.gpr 20#5)) 8 = true := by
    simpa [loadedVals, firstLoad, wp_norm, arm64_norm] using access0.2.2
  have wp : loadedVals.mem.canWrite
      (loadedVals.readReg64 (.gpr 20#5) + (loadedVals.readReg64 .x1 <<< 3)) 8 = true := by
    simpa [loadedVals, firstLoad, slot, data, wp_norm, arm64_norm] using accessSplit.2.2
  let m := (s.mem.write64 data (s.mem.read64 slot)).write64 slot (s.mem.read64 data)
  let flags := subsPState64 (s.readReg64 (.gpr 19#5)) (s.readReg64 .x1)
  let final := ((loadedVals.setPState flags).setMem m).setPC (base + 0x2f4#64)
  have stores : CodeStepsN (program base) 3 loadedVals final ∧
      (program base).CodeLoaded final.mem := by
    have block := quickselect_partition_stores base loadedVals rfl running loaded w0 wp
    simpa [loadedVals, firstLoad, final, flags, m, data, slot, wp_norm, arm64_norm] using block
  refine ⟨final, loads.append stores.1, rfl, running, rfl, stores.2, ?_, ?_, ?_, ?_⟩
  · simp [final, loadedVals, firstLoad, wp_norm, arm64_norm, CalleeSavedPreserved]
  · simp [final, loadedVals, firstLoad, wp_norm, arm64_norm]
  · simp [final, loadedVals, firstLoad, flags, wp_norm, arm64_norm]
  · change m ⊨ (data ↦₆₄* swapWords xs 0 split) ∗ frame
    have swapped := swap_words (m := s.mem) (data := data) (xs := xs) (frame := frame)
      owned (i := 0) (j := split) (by omega) fits
    rw [wordAddr_zero, physical] at swapped
    exact swapped

end Example04Rust
