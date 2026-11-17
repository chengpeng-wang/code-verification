import QuickselectMachine
import ProofLib.Hoare.SafeReaches
import ProofLib.Simulation

open Arm64 ProofLib

namespace Example04Rust

private def inCode (off : Nat) : Bool := off % 4 == 0 && off < codeSize

/-- Check the static control-flow and PC-relative dependencies of one decoded instruction. -/
private def closedInstruction (off : Nat) (inst : Instr) : Bool :=
  let next := inCode (off + 4)
  let target (delta : BitVec 64) := (BitVec.ofNat 64 off + delta).toNat
  match inst with
  | .b delta => inCode (target delta)
  | .bl delta => target delta == 0 && next
  | .bCond _ delta | .cbz _ _ _ delta | .tbz _ _ _ _ delta => inCode (target delta) && next
  | .ret rn => rn == Reg.lr
  | .br _ | .blr _ | .system _ _ | .udf _ | .sysReg _ _ _ | .dcZva _ | .barrier _ _ | .hint _ => false
  | .adr _ _ _ | .ldrLit _ _ _ _ | .ldrSimdLit _ _ _ | .prfmLit _ _ => false
  | _ => next

private def checkWords (off : Nat) : List (BitVec 8) → Bool
  | [] => true
  | b0 :: b1 :: b2 :: b3 :: rest =>
    match Arm64.decode (b3 ++ b2 ++ b1 ++ b0) with
    | some inst => closedInstruction off inst && checkWords (off + 4) rest
    | none => false
  | _ => false

/-- Every word decodes, and the static edges stay in `.text`. Calls go to the local helper;
    return instructions use LR. The scan also rules out system instructions, indirect calls
    and branches, and PC-relative literal/data references. -/
def imageSanity : Bool :=
  codeBytes.length == codeSize && checkWords 0 codeBytes

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem imageSanity_checked : imageSanity = true := by decide +kernel

theorem program_hooks_keep_frozen (base : BitVec 64) : (program base).HooksKeepFrozen := by
  intro pc f s hook
  simp [program, Program.externAt?, Program.hookAtOff?] at hook

/-- Count transitions of `ProofLib.stepState` up to the first visit to the caller PC. A visit
    succeeds only if SP has been restored and the machine is still running. A return reached
    using the last unit of fuel is accepted. -/
def runUntilReturn (prog : Program) (callerPC initialSP : BitVec 64) (fuel : Nat)
    (s : State) : Option (Nat × State) :=
  if s.pc = callerPC then
    if s.sp = initialSP ∧ s.status = .Running then some (0, s) else none
  else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match stepState prog s with
      | none => none
      | some t => (runUntilReturn prog callerPC initialSP fuel t).map fun (n, sf) => (n + 1, sf)

theorem runUntilReturn_steps {prog : Program} (hooks : prog.HooksKeepFrozen)
    {callerPC initialSP : BitVec 64} {fuel count : Nat} {s final : State}
    (run : runUntilReturn prog callerPC initialSP fuel s = some (count, final)) :
    StepsN prog count s final ∧ final.pc = callerPC ∧ final.sp = initialSP ∧
      final.status = .Running ∧
      (∀ {m t}, m < count → StepsN prog m s t → t.pc ≠ callerPC) := by
  induction fuel generalizing s count with
  | zero =>
    simp only [runUntilReturn] at run
    split at run <;> try contradiction
    rename_i pc
    split at run <;> try contradiction
    rename_i stopped
    obtain ⟨rfl, rfl⟩ := Option.some.inj run
    exact ⟨.refl _, pc, stopped.1, stopped.2, fun lt _ => (Nat.not_lt_zero _ lt).elim⟩
  | succ fuel ih =>
    simp only [runUntilReturn] at run
    split at run
    · rename_i pc
      split at run <;> try contradiction
      rename_i stopped
      obtain ⟨rfl, rfl⟩ := Option.some.inj run
      exact ⟨.refl _, pc, stopped.1, stopped.2, fun lt _ => (Nat.not_lt_zero _ lt).elim⟩
    · rename_i before
      split at run <;> try contradiction
      rename_i next next_eq
      cases tail_eq : runUntilReturn prog callerPC initialSP fuel next with
      | none => simp [tail_eq] at run
      | some result =>
        obtain ⟨tail_count, sf⟩ := result
        simp only [tail_eq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨tail, pc, sp, running, first⟩ := ih tail_eq
        have first_step := stepState_sound hooks next_eq
        refine ⟨.step first_step tail, pc, sp, running, ?_⟩
        intro m t shorter earlier
        cases earlier with
        | refl => exact before
        | step prefix_step prefix_tail =>
          cases Step.deterministic first_step prefix_step
          exact first (Nat.lt_of_succ_lt_succ shorter) prefix_tail

theorem runUntilReturn_sound {base : BitVec 64} {fuel count : Nat} {initial final : State}
    (run : runUntilReturn (program base) (initial.readReg64 .lr) initial.sp fuel initial =
      some (count, final)) :
    StepsN (program base) count initial final ∧ Returned initial final ∧
      (∀ {m t}, m < count → StepsN (program base) m initial t → t.pc ≠ initial.readReg64 .lr) := by
  obtain ⟨steps, pc, sp, running, first⟩ := runUntilReturn_steps (program_hooks_keep_frozen base) run
  exact ⟨steps, ⟨pc, sp, running⟩, first⟩

def sampleCodeBase : BitVec 64 := 0x1000
def sampleProgram : Program := program sampleCodeBase
def sampleDataBase : BitVec 64 := 0x4000
def sampleReturnPC : BitVec 64 := 0x8000
def sampleStackTop : BitVec 64 := 0x11000

/-- A finite test state with disjoint code, array, and stack regions. -/
def sampleInitial (xs : List Int) (k : Nat) : State := Id.run do
  let mut mem := (Memory.empty.mapZero sampleDataBase (8 * xs.length)).mapZero 0x10000 4096
  for (x, i) in xs.zipIdx do
    mem := mem.write64 (sampleDataBase + BitVec.ofNat 64 (8 * i)) (BitVec.ofInt 64 x)
  let s : State := { pc := entry sampleCodeBase, sp := sampleStackTop, mem := sampleProgram.loadCode mem }
  return ((s.writeReg64 .x0 sampleDataBase).writeReg64 .x1 (BitVec.ofNat 64 xs.length))
    |>.writeReg64 .x2 (BitVec.ofNat 64 k)
    |>.writeReg64 .lr sampleReturnPC

end Example04Rust

open Example04Rust

/-- Smoke-test the finite fixtures with the actual ARM64 step evaluator. The binary comparison
    also catches a cached `.olean` compiled against different machine bytes. -/
def main : IO Unit := do
  let raw ← IO.FS.readBinFile "example04-rust/build/quickselect.bin"
  let linked := raw.data.toList.map (BitVec.ofNat 8 ∘ UInt8.toNat)
  if linked != codeBytes then
    throw (IO.userError "linked .text differs from the bytes embedded in QuickselectMachine")
  if !imageSanity then
    throw (IO.userError "ARM64 decoding or static control-flow check failed")
  IO.println s!"ARM64 decoding and static control-flow checks passed for {codeSize / 4} words"
  let samples : List (List Int × Nat) :=
    [([7], 0), ([9, -1, 4], 1), ([7, 2, 7, 4, 3, 9, 0, 5, 4, 4], 7),
      (List.replicate 16 4, 9), ((List.range 83).reverse.map Int.ofNat, 49)]
  for (xs, k) in samples do
    let s := sampleInitial xs k
    let some (count, final) := runUntilReturn sampleProgram sampleReturnPC sampleStackTop 15000 s
      | throw (IO.userError s!"no normal return within 15000 steps for length {xs.length}, k={k}")
    let output := (List.range xs.length).map fun i =>
      (final.mem.read64 (sampleDataBase + BitVec.ofNat 64 (8 * i))).toInt
    let some selected := output[k]?
      | throw (IO.userError s!"missing rank {k} for length {xs.length}")
    let leftOrdered := (output.take k).all (· ≤ selected)
    let rightOrdered := (output.drop (k + 1)).all (selected ≤ ·)
    if !output.isPerm xs || !leftOrdered || !rightOrdered then
      throw (IO.userError s!"incorrect rank or permutation for length {xs.length}, k={k}")
    IO.println s!"length={xs.length} k={k} result={selected} instructions={count}"
