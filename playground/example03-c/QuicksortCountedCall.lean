import CountedExecution

namespace Example03C

open Arm64 ProofLib

set_option autoImplicit false

/-- A framed subroutine contract with a postcondition that can depend on the exact
instruction count. The count includes the final RET and excludes the caller's BL. -/
def CountedOk {α : Type} (prog : Program) (entry : BitVec 64) (spec : Arm64.Spec α)
    (postCost : Nat → α → State → State → SepProp) : Prop :=
  ∀ (x : α) (R : SepProp) (s : State), s.pc = entry → s.status = .Running →
    s.spAligned = true → (s.mem ⊨ spec.pre x s ∗ R) → prog.CodeLoaded s.mem →
    ∃ n sf, CodeStepsN prog n s sf ∧ Returned s sf ∧ CallingConventionPreserved s sf ∧
      (sf.mem ⊨ postCost n x s sf ∗ R)

/-- Start a counted subroutine proof by splitting its pure and spatial preconditions. -/
theorem CountedOk.of_wp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Arm64.Spec α} {postCost : Nat → α → State → State → SepProp}
    {prePure : α → State → Prop} {preMem : α → State → SepProp}
    (preEq : ∀ x s, spec.pre x s = ⌜prePure x s⌝ ∗ preMem x s)
    (h : ∀ (x : α) (R : SepProp) (s : State), s.pc = entry → s.status = .Running →
      s.spAligned = true → prePure x s →
      CountedWP prog (s.readReg64 .lr) s (preMem x s)
        (fun n sf Pf => (sf.mem ⊨ Pf ∗ R → sf.mem ⊨ postCost n x s sf ∗ R) ∧
          sf.sp = s.sp ∧ CalleeSavedPreserved s sf)) :
    CountedOk prog entry spec postCost := by
  intro x R s hpc hrun hsp hm loaded
  rw [preEq, sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨n, sf, Pf, steps, pc, running, memory, post⟩ :=
    h x R s hpc hrun hsp hm.1 R hm.2 loaded
  exact ⟨n, sf, steps, ⟨pc, post.2.1, running⟩, post.2, post.1 memory⟩

/-- Compose the callee's counted execution with the continuation, preserving the
caller's spatial frame. This rule starts after BL, which is counted separately. -/
theorem CountedWP.call {α : Type} {prog : Program} {entry target ret : BitVec 64}
    {spec : Arm64.Spec α} {postCost : Nat → α → State → State → SepProp}
    (callee : CountedOk prog entry spec postCost) (x : α)
    {s : State} {P F : SepProp} {post : Nat → State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret)
    (hpre : ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ n sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      CountedWP prog target sf (postCost n x s sf ∗ F) (fun m => post (n + m))) :
    CountedWP prog target s P post := by
  intro R hm loaded
  obtain ⟨n, sf, steps, returned, abi, memory⟩ :=
    callee x (F ∗ R) s hpc hrun halign (hpre R hm) loaded
  rw [← sepConj_assoc] at memory
  obtain ⟨m, final, Pf, rest, pc, running, result, hpost⟩ :=
    hnext n sf (returned.1.trans hlr) returned.2.2 abi.1 abi.2 R memory
      (steps.toStepsN.toSteps.codeLoaded loaded)
  exact ⟨n + m, final, Pf, steps.append rest, pc, running, result, hpost⟩

/-- Move a pure fact in the spatial context into the Lean proof context. -/
theorem CountedWP.pure_elim {prog : Program} {target : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : Nat → State → SepProp → Prop}
    (h : φ → CountedWP prog target s P post) :
    CountedWP prog target s (⌜φ⌝ ∗ P) post := by
  intro R hm loaded
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 loaded

end Example03C
