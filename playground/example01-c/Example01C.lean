import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Surface.IncludeBytes

namespace Example01C

open Arm64

def entryAddress : BitVec 64 := 0x1000#64
def destination : BitVec 64 := 0x2000#64
def returnAddress : BitVec 64 := 0x3000#64

/-- `check.sh` extracts this byte sequence from the compiled C object's function section. -/
def storeByteProgram : Program :=
  { base := entryAddress, code := include_bytes% "build/store_byte.bin" 0 8 }

/-- Lay out an executable code region and two writable bytes. AAPCS64 puts the
    pointer in X0, the byte argument in the low bits of X1, and the return address in LR. -/
def entryState (old value neighbor : BitVec 8) : State :=
  let data := (Memory.empty.mapZero destination 2).write8 destination old
  let data := data.write8 (destination + 1#64) neighbor
  let s : State :=
    { pc := entryAddress, sp := 0x4000#64, status := .Running
      mem := loadCodeMem storeByteProgram data }
  let s := s.writeReg64 .x0 destination
  let s := s.writeReg64 .x1 (value.zeroExtend 64)
  s.writeReg64 .lr returnAddress

private def afterStore (old value neighbor : BitVec 8) : State :=
  let s := entryState old value neighbor
  (s.setMem (s.mem.write8 destination value)).advancePC

/-- The two machine steps return to the caller, write the argument to `*dst`,
    and preserve the neighboring byte, for all input and initial byte values. -/
theorem store_byte_correct (old value neighbor : BitVec 8) :
    ∃ final : State,
      Steps storeByteProgram (entryState old value neighbor) final ∧
      final.status = .Running ∧ final.pc = returnAddress ∧
      final.mem.read8 destination = value ∧
      final.mem.read8 (destination + 1#64) = neighbor := by
  let stored := afterStore old value neighbor
  let final := stored.setPC returnAddress
  have storeStep : Step storeByteProgram (entryState old value neighbor) stored := by
    -- Instruction fetch reads only the code, so these three byte values are irrelevant.
    have fetched : storeByteProgram.fetchMem (entryState old value neighbor).mem entryAddress =
        some (.str .B8 .x1 (.Offset .x0 0#64)) := by
      change storeByteProgram.fetchMem (entryState 0#8 0#8 0#8).mem entryAddress = _
      decide +kernel
    have lowByte : (value.zeroExtend 64).truncate 8 = value := by
      simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend]
    have executed : storeByteProgram.evalInst (.str .B8 .x1 (.Offset .x0 0#64))
        (entryState old value neighbor) = stored := by
      let s := entryState old value neighbor
      have address : evalAddrMode s (.Offset .x0 0#64) = (destination, none) := by rfl
      have writable : s.mem.canWrite destination 1 = true := by
        change (entryState 0#8 0#8 0#8).mem.canWrite destination 1 = true
        decide +kernel
      change execStr .B8 .x1 (.Offset .x0 0#64) s = stored
      unfold execStr
      rw [address]
      simp only [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, MemWidth.bytes, writable]
      change (s.setMem (s.mem.write8 destination ((value.zeroExtend 64).truncate 8))).advancePC = stored
      rw [lowByte]
      rfl
    rw [← executed]
    exact Step.exec (by rfl) fetched
  have returnStep : Step storeByteProgram stored final := by
    -- After the write, the next instruction still fetches from the code region.
    have fetched : storeByteProgram.fetchMem (afterStore old value neighbor).mem
        (entryAddress + 4#64) = some (.ret .lr) := by
      change storeByteProgram.fetchMem (afterStore 0#8 0#8 0#8).mem (entryAddress + 4#64) = _
      decide +kernel
    exact Step.exec (prog := storeByteProgram) (s := stored) (by rfl) fetched
  exact ⟨final, .step storeStep (.step returnStep (.refl final)), by rfl, by rfl, by rfl, by rfl⟩

#print axioms store_byte_correct

end Example01C
