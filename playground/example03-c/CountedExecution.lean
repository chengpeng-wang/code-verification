/- Portions of the instruction rules adapt Google LLC's ProofLib code.
Copyright 2026 Google LLC. Licensed under Apache-2.0. -/
import ProofLib
import ProofLib.Hoare.SafeReaches

open Arm64 ProofLib

namespace Example03C

/-- An execution of exactly `n` ARM64 steps, with a decoded instruction at
    each source PC in the linked code image. -/
inductive CodeStepsN (prog : Program) : Nat → State → State → Prop where
  | refl (s : State) : CodeStepsN prog 0 s s
  | step {n : Nat} {s u t : State} {inst : Instr}
      (fetch : prog.fetch s.pc = some inst) (step : Step prog s u)
      (tail : CodeStepsN prog n u t) : CodeStepsN prog (n + 1) s t

theorem CodeStepsN.toStepsN {prog : Program} {n : Nat} {s t : State}
    (run : CodeStepsN prog n s t) : StepsN prog n s t := by
  induction run with
  | refl s => exact .refl s
  | step _ h _ ih => exact .step h ih

theorem CodeStepsN.append {prog : Program} {n m : Nat} {s u t : State}
    (initialRun : CodeStepsN prog n s u) (suffix : CodeStepsN prog m u t) :
    CodeStepsN prog (n + m) s t := by
  induction initialRun with
  | refl => simpa using suffix
  | step fetch step _ ih =>
    simpa [Nat.succ_add] using CodeStepsN.step fetch step (ih suffix)

/-- A shorter execution cannot already be at a PC outside the code image. -/
theorem CodeStepsN.prefix_pc_ne {prog : Program} {n m : Nat} {s u t : State} {pc : BitVec 64}
    (run : CodeStepsN prog n s t) (initialRun : StepsN prog m s u)
    (shorter : m < n) (outside : prog.fetch pc = none) : u.pc ≠ pc := by
  induction run generalizing m u with
  | refl => omega
  | step fetch step _ ih =>
    cases initialRun with
    | refl =>
      intro atPC
      rw [atPC, outside] at fetch
      cases fetch
    | step first rest =>
      cases Step.deterministic step first
      exact ih rest (Nat.lt_of_succ_lt_succ shorter)

/-- A total-correctness weakest precondition with an exact execution count in
    its postcondition. Each counted transition is an ARM64 `Step`. -/
def CountedWP (prog : Program) (target : BitVec 64) (s : State) (P : SepProp)
    (post : Nat → State → SepProp → Prop) : Prop :=
  ∀ R : SepProp, (s.mem ⊨ P ∗ R) → prog.CodeLoaded s.mem →
    ∃ n sf Pf, CodeStepsN prog n s sf ∧ sf.pc = target ∧ sf.status = .Running ∧
      (sf.mem ⊨ Pf ∗ R) ∧ post n sf Pf

theorem CountedWP.done {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : Nat → State → SepProp → Prop}
    (hpc : s.pc = target) (hrun : s.status = .Running) (hpost : post 0 s P) :
    CountedWP prog target s P post := by
  intro _ hm _
  exact ⟨0, s, P, .refl s, hpc, hrun, hm, hpost⟩

theorem CountedWP.mono {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post post' : Nat → State → SepProp → Prop}
    (h : CountedWP prog target s P post)
    (himp : ∀ n sf Pf, post n sf Pf → post' n sf Pf) :
    CountedWP prog target s P post' := by
  intro R hm loaded
  obtain ⟨n, sf, Pf, steps, pc, run, mem, hp⟩ := h R hm loaded
  exact ⟨n, sf, Pf, steps, pc, run, mem, himp n sf Pf hp⟩

theorem CountedWP.exists_elim {α : Sort _} {prog : Program} {target : BitVec 64} {s : State}
    {P : α → SepProp} {post : Nat → State → SepProp → Prop}
    (h : ∀ a, CountedWP prog target s (P a) post) :
    CountedWP prog target s (∃∗ a, P a) post := by
  intro R hm loaded
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha loaded

private theorem prepend {prog : Program} {target : BitVec 64} {s : State}
    {inst : Instr} {R : SepProp} {post : Nat → State → SepProp → Prop}
    (hrun : s.status = .Running) (hfetch : prog.fetch s.pc = some inst)
    (hnext : prog.CodeLoaded (prog.evalInst inst s).mem →
      ∃ n sf Pf, CodeStepsN prog n (prog.evalInst inst s) sf ∧ sf.pc = target ∧
        sf.status = .Running ∧ (sf.mem ⊨ Pf ∗ R) ∧ post (n + 1) sf Pf) :
    prog.CodeLoaded s.mem →
      ∃ n sf Pf, CodeStepsN prog n s sf ∧ sf.pc = target ∧ sf.status = .Running ∧
        (sf.mem ⊨ Pf ∗ R) ∧ post n sf Pf := by
  intro loaded
  have step := Step.exec hrun (Program.fetchMem_of_fetch loaded hfetch)
  obtain ⟨n, sf, Pf, steps, pc, run, mem, hp⟩ := hnext (step.codeLoaded loaded)
  exact ⟨n + 1, sf, Pf, .step hfetch step steps, pc, run, mem, hp⟩

/-! The single-instruction rules below specialize the corresponding
    Apache-2.0-licensed Google LLC ProofLib rules. Their conclusion uses
    `prepend` to count the instruction while reusing the same memory and
    register side conditions. -/

theorem CountedWP.step_pure {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {inst : Instr}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = s')
    (hmem : s'.mem = s.mem)
    (hnext : CountedWP prog target_pc s' P (fun n => post (n + 1))) :
    CountedWP prog target_pc s P post := by
  intro R hm
  have hs_pc : s.setPC pc = s := by
    cases s
    simp [State.setPC] at hpc ⊢
    exact hpc.symm
  have hfetch' : prog.fetch s.pc = some inst := hpc.symm ▸ hfetch
  have hexec' : prog.evalInst inst s = s' := by rw [← hs_pc, hexec]
  apply prepend hrun hfetch'
  rw [hexec']
  apply hnext R
  rwa [hmem]

theorem CountedWP.step_pure_setPC {prog : Program} {target_pc : BitVec 64}
    {s0 s' : State} {P : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {inst : Instr}
    (hrun : (s0.setPC pc).status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s0.setPC pc) = s')
    (hmem : s'.mem = s0.mem)
    (hnext : CountedWP prog target_pc s' P (fun n => post (n + 1))) :
    CountedWP prog target_pc (s0.setPC pc) P post := by
  intro R hm
  apply prepend hrun hfetch
  rw [hexec]
  apply hnext R
  rwa [hmem, ← State.mem_setPC s0 pc]

theorem CountedWP.step_pure_setMem_setPC {prog : Program} {target_pc : BitVec 64}
    {s0 s' : State} {P : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {m : Memory} {inst : Instr}
    (hrun : ((s0.setPC pc).setMem m).status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst ((s0.setPC pc).setMem m) = s')
    (hmem : s'.mem = m)
    (hnext : CountedWP prog target_pc s' P (fun n => post (n + 1))) :
    CountedWP prog target_pc ((s0.setPC pc).setMem m) P post := by
  intro R hm
  have hfetch' : prog.fetch ((s0.setPC pc).setMem m).pc = some inst := by
    rw [State.pc_setMem, State.pc_setPC]
    exact hfetch
  apply prepend hrun hfetch'
  rw [hexec]
  apply hnext R
  rwa [hmem]

theorem CountedWP.step_ldr8 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad8 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : CountedWP prog target_pc s' P (fun n => post (n + 1))) :
    CountedWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .B8 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read8 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 1 = true := hload.readable hm
  apply prepend hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .B8 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem CountedWP.step_str8 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, CountedWP prog target_pc (s'.setMem m') P' (fun n => post (n + 1))) :
    CountedWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .B8 rt addr) := hpc.symm ▸ hfetch
  have htrunc : (s.readReg64 rt).truncate 8 = val := by
    rw [← bitvec_truncate8_truncate32]
    exact hval
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply prepend hrun hfetch'
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

theorem CountedWP.step_ldr64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .X64 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeReg64 rt v).setPC (pc + 4#64) = s')
    (hnext : CountedWP prog target_pc s' P (fun n => post (n + 1))) :
    CountedWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W64 .X64 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  apply prepend hrun hfetch'
  have hstep : prog.evalInst (.ldr .W64 .X64 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem CountedWP.step_str64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, CountedWP prog target_pc (s'.setMem m') P' (fun n => post (n + 1))) :
    CountedWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .X64 rt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply prepend hrun hfetch'
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

theorem CountedWP.step_stp64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1)
    (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, CountedWP prog target_pc (s'.setMem m') P2 (fun n => post (n + 1))) :
    CountedWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply prepend hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact hnext m2 R hm2

theorem CountedWP.step_ldp64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : Nat → State → SepProp → Prop}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldp .W64 false rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeReg64 rt1 v1).writeReg64 rt2 v2).setPC (pc + 4#64) = s')
    (hnext : CountedWP prog target_pc s' P (fun n => post (n + 1))) :
    CountedWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldp .W64 false rt1 rt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  apply prepend hrun hfetch'
  have hstep : prog.evalInst (.ldp .W64 false rt1 rt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdp, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hread1, hread2, hcan1, hcan2,
      MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem CountedWP.ite {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : Nat → State → SepProp → Prop}
    {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
    (hthen : c → CountedWP prog target_pc (s.setPC pc1) P post)
    (helse : ¬ c → CountedWP prog target_pc (s.setPC pc2) P post) :
    CountedWP prog target_pc s P post := by
  letI := inst
  by_cases hc : c
  · have hpc1 : s.pc = pc1 := by simp [hpc, hc]
    have hs1 : s.setPC pc1 = s := by cases s; simp [State.setPC] at hpc1 ⊢; exact hpc1.symm
    exact hs1 ▸ hthen hc
  · have hpc2 : s.pc = pc2 := by simp [hpc, hc]
    have hs2 : s.setPC pc2 = s := by cases s; simp [State.setPC] at hpc2 ⊢; exact hpc2.symm
    exact hs2 ▸ helse hc

open Lean Elab Tactic Meta

/-- Normalize the state in the current goal with the ARM64 library's rules. -/
macro "cost_norm_state" : tactic =>
  `(tactic| conv => arg 3; simp only [wp_norm, arm64_norm])

/-- Apply the same verified instruction rule selected by `wp_step`, with the
    counted continuation. The proof kernel checks the replacement rule. -/
private def countedStep : TacticM ProofLib.WpStepOutcome := do
  let originalGoals ← getGoals
  let original ← getMainGoal
  let (post, dummyPost, sandbox) ← original.withContext do
    let target := (← instantiateMVars (← original.getType)).consumeMData
    unless target.isAppOfArity ``CountedWP 5 do
      throwError "cost_step expects a CountedWP goal, got {target}"
    let dummyPost := mkLambda `s .default (mkConst ``Arm64.State)
      (mkLambda `P .default (mkConst ``SepProp) (mkConst ``True))
    let dummyOom := mkLambda `s .default (mkConst ``Arm64.State)
      (mkApp (mkConst ``SepProp.pure) (mkConst ``False))
    let args := target.getAppArgs
    let sandbox ← mkFreshExprMVar (mkAppN (mkConst ``SepWP)
      (args.pop ++ #[dummyPost, dummyOom]))
    pure (args.back!, dummyPost, sandbox)
  setGoals [sandbox.mvarId!]
  let outcome ← wpStepCoreWithOutcome (isSingleStep := true)
  let continuationGoals ← getGoals
  unless continuationGoals.length == 1 do
    throwError "cost_step expects exactly one continuation"
  let nextGoals ← original.withContext do
    let rule := (← instantiateMVars sandbox).consumeMData
    let .const name levels := rule.getAppFn
      | throwError "cost_step could not identify ProofLib's instruction rule"
    unless name.getPrefix == ``SepWP do
      throwError "cost_step expected a SepWP rule, got {name}"
    let countedName := Name.str ``CountedWP name.getString!
    unless (← getEnv).contains countedName do
      throwError "cost_step has no counted variant of {name}"
    let args := rule.getAppArgs
    let some postIndex := args.findIdx? (· == dummyPost)
      | throwError "cost_step could not identify ProofLib's postcondition"
    let fixedArgs := args.extract 0 postIndex ++ #[post] ++ args.extract (postIndex + 2) (args.size - 1)
    original.apply (mkAppN (mkConst countedName levels) fixedArgs)
  setGoals (nextGoals ++ originalGoals.tail)
  let continuation ← getMainGoal
  if (← continuation.getType).isForall then
    evalTactic (← `(tactic| (intro; try cost_norm_state)))
  pure outcome

/-- Execute one instruction, adding one to the counted postcondition. -/
elab "cost_step" : tactic => do
  let _ ← countedStep

/-- Execute a straight-line block, stopping after a call or return. -/
syntax "cost_steps" (ppSpace colGt num)? : tactic
elab_rules : tactic
  | `(tactic| cost_steps $[$n?:num]?) => do
    let bound := n?.map TSyntax.getNat |>.getD 128
    for _ in [:bound] do
      let outcome ← countedStep
      if outcome == .steppedCall || outcome == .steppedRet then return

/-- Split an already executed conditional branch. This changes no count. -/
syntax "cost_if" (ppSpace colGt ident)? : tactic
elab_rules : tactic
  | `(tactic| cost_if $[$h?:ident]?) => do
    let h ← h?.map pure |>.getD (freshIdent `hcond)
    evalTactic (← `(tactic| (
      apply CountedWP.ite
      wp_focus_close wp_norm_lhs)))
    let thenGoal :: elseGoal :: rest ← getGoals
      | throwError "cost_if expected two branch goals"
    let mut normalized := []
    for goal in [thenGoal, elseGoal] do
      setGoals [goal]
      evalTactic (← `(tactic| intro $h:ident))
      normWpIfHyp h
      evalTactic (← `(tactic| try cost_norm_state))
      normalized := normalized ++ (← getGoals)
    setGoals (normalized ++ rest)

end Example03C
