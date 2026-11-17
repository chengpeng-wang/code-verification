import QuickselectBounds
import QuickselectAdversaryPivot
import QuicksortCountedCall
import ProofLib.SepLogic.SliceArray

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false

/-- Read a Rust i64 array element at the byte address computed by a scaled
    ARM64 load, retaining the entire array in the separation-logic context. -/
theorem pivot_array_load (data : BitVec 64) (xs : List (BitVec 64))
    (i : Nat) (hi : i < xs.length) (R : SepProp) :
    SepLoad64 (data + (BitVec.ofNat 64 i <<< 3)) ((data ↦₆₄* xs) ∗ R) xs[i]! := by
  rw [pointsToWords64_eq_pointsToArray, pointsToArray_focus 8 (· ↦₆₄ ·) data xs i hi]
  simp only [sepConj_assoc]
  simp only [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  apply SepLoad64.of_eq_addr rfl
  congr 1
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofNat_mul, BitVec.mul_comm]
  rfl

/-- Register arguments for the recursive helper. The input slice and the helper
    stack are both returned to the caller. -/
def pivotHelperSpec (data : BitVec 64) (xs : List (BitVec 64))
    (a b c span frames : Nat) : Arm64.Spec Unit where
  pre := fun _ s =>
    ⌜s.readReg64 .x0 = data ∧ s.readReg64 .x1 = BitVec.ofNat 64 xs.length ∧
      s.readReg64 .x2 = BitVec.ofNat 64 a ∧ s.readReg64 .x3 = BitVec.ofNat 64 b ∧
      s.readReg64 (.gpr 4#5) = BitVec.ofNat 64 c ∧
      s.readReg64 (.gpr 5#5) = BitVec.ofNat 64 span⌝ ∗
      (data ↦₆₄* xs) ∗ stackAt s.sp (80 * frames)
  post := fun _ s t =>
    (∃∗ p : Nat, ⌜t.readReg64 .x0 = 1#64 ∧ t.readReg64 .x1 = BitVec.ofNat 64 p ∧
        Pivot.PivotChoice xs a b c span p⌝ ∗
      (data ↦₆₄* xs) ∗ stackAt s.sp (80 * frames))

/-- The recursive pivot helper returns a valid ranked pivot. Its exact cost is
    composed of at most ninety-six local instructions at each helper invocation. -/
def pivotHelperPost (data : BitVec 64) (xs : List (BitVec 64))
    (a b c span frames count : Nat) (_ : Unit) (s t : State) : SepProp :=
  ∃∗ p : Nat, ⌜t.readReg64 .x0 = 1#64 ∧ t.readReg64 .x1 = BitVec.ofNat 64 p ∧
    Pivot.PivotChoice xs a b c span p ∧ QuickselectCost.PivotCosts 96 span count⌝ ∗
      (data ↦₆₄* xs) ∗ stackAt s.sp (80 * frames)

private def pivotWords : List (BitVec 32) :=
  [
    0xa9bb7bfd#32, 0xa90167fa#32, 0xa9025ff8#32, 0xa90357f6#32, 0xa9044ff4#32, 0x910003fd#32,
    0xaa0403f5#32, 0xaa0303f7#32, 0xaa0203f3#32, 0xaa0103f6#32, 0xf10024bf#32, 0xaa0003f4#32,
    0x54000342#32, 0xeb16027f#32, 0xaa1f03e0#32, 0x54000aa2#32, 0xeb1602ff#32, 0x54000a62#32,
    0xeb1602bf#32, 0x54000a02#32, 0xf8737a89#32, 0xf8777a88#32, 0xf8757a8a#32, 0xeb08013f#32,
    0x1a9fa7eb#32, 0xeb0a013f#32, 0x1a9fa7ec#32, 0x4a0c016b#32, 0x3700010b#32, 0xeb08013f#32,
    0x1a9fa7e9#32, 0xeb0a011f#32, 0x1a9fb7e8#32, 0x4a080128#32, 0x7100011f#32, 0x9a9512f3#32,
    0x52800020#32, 0x1400003f#32, 0xd29c71e8#32, 0xaa1403e0#32, 0xaa1603e1#32, 0xf2b1c708#32,
    0xaa1303e2#32, 0xf2c71c68#32, 0xf2fc71c8#32, 0x9bc87ca8#32, 0xd343fd18#32, 0xd37ef719#32,
    0xd37df31a#32, 0xaa1803e5#32, 0x8b130323#32, 0x8b130344#32, 0x97ffffcc#32, 0x360005c0#32,
    0xaa0103f3#32, 0x8b170323#32, 0x8b170344#32, 0xaa1403e0#32, 0xaa1603e1#32, 0xaa1703e2#32,
    0xaa1803e5#32, 0x97ffffc3#32, 0xf100041f#32, 0x54000481#32, 0xaa0103f7#32, 0x8b150323#32,
    0x8b150344#32, 0xaa1403e0#32, 0xaa1603e1#32, 0xaa1503e2#32, 0xaa1803e5#32, 0x97ffffb9#32,
    0xf100041f#32, 0x54000341#32, 0xeb16027f#32, 0xaa1f03e0#32, 0x54000302#32, 0xeb1602ff#32,
    0x540002c2#32, 0xeb16003f#32, 0x54000262#32, 0xf8737a8a#32, 0xf8777a89#32, 0xaa1703e8#32,
    0xf8617a8b#32, 0xeb09015f#32, 0x1a9fa7ec#32, 0xeb0b015f#32, 0x1a9fa7ed#32, 0x4a0d018c#32,
    0x3707f94c#32, 0xeb09015f#32, 0x1a9fa7ea#32, 0xeb0b013f#32, 0x1a9fb7e9#32, 0x4a090149#32,
    0x7100013f#32, 0x9a811113#32, 0x17ffffc2#32, 0xaa1f03e0#32, 0xaa1303e1#32, 0xa9444ff4#32,
    0xa94357f6#32, 0xa9425ff8#32, 0xa94167fa#32, 0xa8c57bfd#32, 0xd65f03c0#32
  ]

private theorem pivotCode (base : BitVec 64) : (program base).hasWords base pivotWords := by
  rw [Program.hasWords, show (program base).base = base from rfl, BitVec.sub_self]
  change (program 0).hasWordsOff 0 pivotWords
  decide +kernel

private def pivotSaved (s : State) : SepProp :=
  ((s.sp - 80#64) ↦₆₄ s.readReg64 .fp) ∗
  ((s.sp - 72#64) ↦₆₄ s.readReg64 .lr) ∗
  ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
  ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
  ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
  ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
  ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗
  ((s.sp - 24#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
  ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
  ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5))

private def untouched (s t : State) : Prop :=
  t.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
  t.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs t = calleeSavedVRegs s

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

private theorem pivot_prologue (base : BitVec 64) (s : State) (frames : Nat) (A : SepProp)
    (hpc : s.pc = base) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hsize : 80 * (frames + 1) ≤ 2 ^ 64) :
    CountedWP (program base) (base + 0x30#64) s (A ∗ stackAt s.sp (80 * (frames + 1)))
      (fun n t P => n = 12 ∧
        P = A ∗ stackAt (s.sp - 80#64) (80 * frames) ∗ pivotSaved s ∧
        t.sp = s.sp - 80#64 ∧ untouched s t ∧
        t.readReg64 (.gpr 20#5) = s.readReg64 .x0 ∧
        t.readReg64 (.gpr 22#5) = s.readReg64 .x1 ∧
        t.readReg64 (.gpr 19#5) = s.readReg64 .x2 ∧
        t.readReg64 (.gpr 23#5) = s.readReg64 .x3 ∧
        t.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 4#5) ∧
        t.readReg64 (.gpr 5#5) = s.readReg64 (.gpr 5#5) ∧
        ConditionHolds .CS t.pstate = BitVec.ule 9#64 (s.readReg64 (.gpr 5#5))) := by
  have code := pivotCode base
  have hstack : stackAt s.sp (80 * (frames + 1)) =
      stackAt (s.sp - 80#64) (80 * frames) ∗ cells (s.sp - 80#64) 10 := by
    rw [show 80 * (frames + 1) = 80 * frames + 8 * 10 by omega]
    exact stackAt_split_cells s.sp (80 * frames) 10 (by omega)
  have hsp := s.spAligned_sub 80#64 halign (by decide)
  conv =>
    arg 4
    rw [hstack]
    simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 10 (apply CountedWP.exists_elim; intro)
  cost_steps 12
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  simp [pivotSaved, untouched, wp_norm, arm64_norm]


private theorem pivot_epilogue (base : BitVec 64) (original s : State) (frames : Nat) (A : SepProp)
    (hpc : s.pc = base + 0x190#64) (hrun : s.status = .Running)
    (hsp : s.sp = original.sp - 80#64) (halign : s.spAligned = true)
    (hsize : 80 * (frames + 1) ≤ 2 ^ 64) (huntouched : untouched original s) :
    CountedWP (program base) (original.readReg64 .lr) s
      (A ∗ stackAt (original.sp - 80#64) (80 * frames) ∗ pivotSaved original)
      (fun n t P => n = 7 ∧
        P ⊢ (A ∗ stackAt original.sp (80 * (frames + 1))) ∧
        CallingConventionPreserved original t ∧
        t.readReg64 .x0 = s.readReg64 .x0 ∧ t.readReg64 .x1 = s.readReg64 (.gpr 19#5)) := by
  have code := pivotCode base
  have frameAddr (off : BitVec 64) : original.sp - off = s.sp + (80#64 - off) := by
    rw [hsp]
    bv_arith
  conv =>
    arg 4
    rw [pivotSaved, frameAddr 80#64, frameAddr 72#64, frameAddr 64#64, frameAddr 56#64,
      frameAddr 48#64, frameAddr 40#64, frameAddr 32#64, frameAddr 24#64, frameAddr 16#64,
      frameAddr 8#64]
    simp only [bv_lin_norm]
  cost_steps 7
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · have hstack : stackAt original.sp (80 * (frames + 1)) =
        stackAt (original.sp - 80#64) (80 * frames) ∗ cells (original.sp - 80#64) 10 := by
      rw [show 80 * (frames + 1) = 80 * frames + 8 * 10 by omega]
      exact stackAt_split_cells original.sp (80 * frames) 10 (by omega)
    rw [hstack]
    simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
      sepConj_emp, sepExists_sepConj_right]
    simp only [hsp, wp_norm, arm64_norm, bv_lin_norm]
    apply Entails.sepExists_right (original.readReg64 .fp)
    apply Entails.sepExists_right (original.readReg64 .lr)
    apply Entails.sepExists_right (original.readReg64 (.gpr 26#5))
    apply Entails.sepExists_right (original.readReg64 (.gpr 25#5))
    apply Entails.sepExists_right (original.readReg64 (.gpr 24#5))
    apply Entails.sepExists_right (original.readReg64 (.gpr 23#5))
    apply Entails.sepExists_right (original.readReg64 (.gpr 22#5))
    apply Entails.sepExists_right (original.readReg64 (.gpr 21#5))
    apply Entails.sepExists_right (original.readReg64 (.gpr 20#5))
    apply Entails.sepExists_right (original.readReg64 (.gpr 19#5))
    sep_entail
  · obtain ⟨r27, r28, vregs⟩ := huntouched
    simp [CallingConventionPreserved, CalleeSavedPreserved, r27, r28, vregs, wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm]

private theorem nat_ofNat (x : Nat) (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp [Nat.mod_eq_of_lt hx]

private theorem bounded_unsigned {a b : Nat} (h : a < b) (hfit : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ule (BitVec.ofNat 64 a) = false := by
  cases hle : (BitVec.ofNat 64 b).ule (BitVec.ofNat 64 a)
  · rfl
  · have h := BitVec.ule_iff_toNat_le.mp hle
    rw [nat_ofNat b hfit, nat_ofNat a (by omega)] at h
    omega

private def medianIndex (xs : List (BitVec 64)) (a b c : Nat) : Nat :=
  if decide (xs[a]!.toInt < xs[b]!.toInt) != decide (xs[a]!.toInt < xs[c]!.toInt)
  then a else if decide (xs[b]!.toInt < xs[c]!.toInt) == decide (xs[a]!.toInt < xs[b]!.toInt)
  then b else c

set_option linter.unusedSimpArgs false in
private theorem pivot_leaf_median (base data : BitVec 64) (s : State)
    (xs : List (BitVec 64)) (a b c : Nat) (R : SepProp)
    (hpc : s.pc = base + 0x34#64) (hrun : s.status = .Running)
    (h20 : s.readReg64 (.gpr 20#5) = data)
    (h22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 xs.length)
    (h19 : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 a)
    (h23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 b)
    (h21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 c)
    (ha : a < xs.length) (hb : b < xs.length) (hc : c < xs.length) (hfit : xs.length < 2 ^ 64) :
    CountedWP (program base) (base + 0x90#64) s ((data ↦₆₄* xs) ∗ R)
      (fun count t P => count ≤ 23 ∧ P = (data ↦₆₄* xs) ∗ R ∧ t.sp = s.sp ∧
        untouched s t ∧ t.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (medianIndex xs a b c)) := by
  have code := pivotCode base
  have hA := bounded_unsigned ha hfit
  have hB := bounded_unsigned hb hfit
  have hC := bounded_unsigned hc hfit
  cost_steps 3
  cost_steps 2
  cost_steps 2
  have hfA : (program base).fetch (base + 0x50#64) =
      some (.ldr .W64 .X64 false (.gpr 9#5) (.RegOffset (.gpr 20#5) (.gpr 19#5) .UXTX 3)) := by
    rw [fetch_off]
    decide +kernel
  refine CountedWP.step_ldr64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) hfA rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, h20, h19]) (pivot_array_load data xs a ha R) rfl ?_
  cost_norm_state
  have hfB : (program base).fetch (base + 0x54#64) =
      some (.ldr .W64 .X64 false (.gpr 8#5) (.RegOffset (.gpr 20#5) (.gpr 23#5) .UXTX 3)) := by
    rw [fetch_off]
    decide +kernel
  refine CountedWP.step_ldr64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) hfB rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, h20, h23]) (pivot_array_load data xs b hb R) rfl ?_
  cost_norm_state
  have hfC : (program base).fetch (base + 0x58#64) =
      some (.ldr .W64 .X64 false (.gpr 10#5) (.RegOffset (.gpr 20#5) (.gpr 21#5) .UXTX 3)) := by
    rw [fetch_off]
    decide +kernel
  refine CountedWP.step_ldr64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) hfC rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, h20, h21]) (pivot_array_load data xs c hc R) rfl ?_
  cost_norm_state
  cost_steps 6
  cost_if chooseA
  · apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    by_cases ab : (xs[a]?.getD default).toInt < (xs[b]?.getD default).toInt <;>
      by_cases ac : (xs[a]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      by_cases bc : (xs[b]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      simp [medianIndex, untouched, wp_norm, arm64_norm, h19, h23, h21,
        BitVec.sle_iff_toInt_le, BitVec.slt_iff_toInt_lt, ← Int.not_lt, ab, ac, bc] at chooseA ⊢
  · cost_steps 7
    apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    by_cases ab : (xs[a]?.getD default).toInt < (xs[b]?.getD default).toInt <;>
      by_cases ac : (xs[a]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      by_cases bc : (xs[b]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      simp [medianIndex, untouched, wp_norm, arm64_norm, h19, h23, h21,
        BitVec.sle_iff_toInt_le, BitVec.slt_iff_toInt_lt, ← Int.not_lt, ab, ac, bc] at chooseA ⊢

set_option linter.unusedSimpArgs false in
private theorem pivot_first_call (base : BitVec 64) (s : State) (P : SepProp)
    (hpc : s.pc = base + 0x98#64) (hrun : s.status = .Running) :
    CountedWP (program base) base s P
      (fun count t P' => count = 15 ∧ P' = P ∧ t.sp = s.sp ∧ untouched s t ∧
        t.readReg64 .lr = base + 0xd4#64 ∧
        t.readReg64 .x0 = s.readReg64 (.gpr 20#5) ∧
        t.readReg64 .x1 = s.readReg64 (.gpr 22#5) ∧
        t.readReg64 .x2 = s.readReg64 (.gpr 19#5) ∧
        t.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        t.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        t.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        t.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        t.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        let len := BitVec.ofNat 64 ((s.readReg64 (.gpr 5#5)).toNat / 9)
        t.readReg64 .x3 = s.readReg64 (.gpr 19#5) + (len <<< 2) ∧
        t.readReg64 (.gpr 4#5) = s.readReg64 (.gpr 19#5) + (len <<< 3) ∧
        t.readReg64 (.gpr 5#5) = len ∧
        t.readReg64 (.gpr 24#5) = len ∧
        t.readReg64 (.gpr 25#5) = len <<< 2 ∧ t.readReg64 (.gpr 26#5) = len <<< 3) := by
  have code := pivotCode base
  cost_steps 15
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  have div := divideNine (s.readReg64 (.gpr 5#5))
  change mulHi64 (s.readReg64 (.gpr 5#5)) 0xe38e38e38e38e38f#64 >>> 3 = _ at div
  change BitVec.setWidth 64
    ((BitVec.setWidth 128 (s.readReg64 (.gpr 5#5)) * 0xe38e38e38e38e38f#128) >>> 64) >>> 3 = _ at div
  simp [untouched, wp_norm, arm64_norm, div, BitVec.add_comm]


private theorem pivot_branch (base : BitVec 64) (s : State) (P : SepProp)
    (hpc : s.pc = base + 0x30#64) (hrun : s.status = .Running)
    (hcond : ConditionHolds .CS s.pstate = BitVec.ule 9#64 (s.readReg64 (.gpr 5#5)))
    (large : Bool) (hl : BitVec.ule 9#64 (s.readReg64 (.gpr 5#5)) = large) :
    CountedWP (program base) (base + (if large then 0x98#64 else 0x34#64)) s P
      (fun count t P' => count = 1 ∧ P' = P ∧
        t = s.setPC (base + (if large then 0x98#64 else 0x34#64))) := by
  have code := pivotCode base
  have test : ConditionHolds .CS s.pstate = large := hcond.trans hl
  cases large <;> cost_steps 1 <;>
    apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs) <;>
    simp [wp_norm, arm64_norm]

private theorem pivot_second_call (base : BitVec 64) (s : State) (P : SepProp)
    (hpc : s.pc = base + 0xd4#64) (hrun : s.status = .Running)
    (some : s.readReg64 .x0 = 1#64) :
    CountedWP (program base) base s P
      (fun count t P' => count = 9 ∧ P' = P ∧ t.sp = s.sp ∧ untouched s t ∧
        t.readReg64 .lr = base + 0xf8#64 ∧
        t.readReg64 .x0 = s.readReg64 (.gpr 20#5) ∧
        t.readReg64 .x1 = s.readReg64 (.gpr 22#5) ∧
        t.readReg64 .x2 = s.readReg64 (.gpr 23#5) ∧
        t.readReg64 .x3 = s.readReg64 (.gpr 23#5) + s.readReg64 (.gpr 25#5) ∧
        t.readReg64 (.gpr 4#5) = s.readReg64 (.gpr 23#5) + s.readReg64 (.gpr 26#5) ∧
        t.readReg64 (.gpr 5#5) = s.readReg64 (.gpr 24#5) ∧
        t.readReg64 (.gpr 19#5) = s.readReg64 .x1 ∧
        t.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        t.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        t.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        t.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        t.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        t.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5)) := by
  have code := pivotCode base
  have test : (s.readReg64 .x0).getLsbD 0 = true := by rw [some]; decide
  cost_steps 9
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  simp [untouched, wp_norm, arm64_norm, BitVec.add_comm]

private theorem pivot_third_call (base : BitVec 64) (s : State) (P : SepProp)
    (hpc : s.pc = base + 0xf8#64) (hrun : s.status = .Running)
    (some : s.readReg64 .x0 = 1#64) :
    CountedWP (program base) base s P
      (fun count t P' => count = 10 ∧ P' = P ∧ t.sp = s.sp ∧ untouched s t ∧
        t.readReg64 .lr = base + 0x120#64 ∧
        t.readReg64 .x0 = s.readReg64 (.gpr 20#5) ∧
        t.readReg64 .x1 = s.readReg64 (.gpr 22#5) ∧
        t.readReg64 .x2 = s.readReg64 (.gpr 21#5) ∧
        t.readReg64 .x3 = s.readReg64 (.gpr 21#5) + s.readReg64 (.gpr 25#5) ∧
        t.readReg64 (.gpr 4#5) = s.readReg64 (.gpr 21#5) + s.readReg64 (.gpr 26#5) ∧
        t.readReg64 (.gpr 5#5) = s.readReg64 (.gpr 24#5) ∧
        t.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        t.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        t.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        t.readReg64 (.gpr 23#5) = s.readReg64 .x1) := by
  have code := pivotCode base
  cost_steps 10
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  simp [untouched, wp_norm, arm64_norm, BitVec.add_comm]

private theorem pivot_confirm_third (base : BitVec 64) (s : State) (P : SepProp)
    (hpc : s.pc = base + 0x120#64) (hrun : s.status = .Running)
    (some : s.readReg64 .x0 = 1#64) :
    CountedWP (program base) (base + 0x128#64) s P
      (fun count t P' => count = 2 ∧ P' = P ∧ t.sp = s.sp ∧ untouched s t ∧
        t.readReg64 .x1 = s.readReg64 .x1 ∧
        t.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        t.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        t.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        t.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5)) := by
  have code := pivotCode base
  cost_steps 2
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  simp [untouched, wp_norm, arm64_norm]

private theorem pivot_success (base : BitVec 64) (s : State) (P : SepProp)
    (hpc : s.pc = base + 0x90#64) (hrun : s.status = .Running) :
    CountedWP (program base) (base + 0x190#64) s P
      (fun count t P' => count = 2 ∧ P' = P ∧ t.sp = s.sp ∧ untouched s t ∧
        t.readReg64 .x0 = 1#64 ∧ t.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)) := by
  have code := pivotCode base
  cost_steps 2
  apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  simp [untouched, wp_norm, arm64_norm]

set_option linter.unusedSimpArgs false in
private theorem pivot_internal_median (base data : BitVec 64) (s : State)
    (xs : List (BitVec 64)) (a b c : Nat) (R : SepProp)
    (hpc : s.pc = base + 0x128#64) (hrun : s.status = .Running)
    (h20 : s.readReg64 (.gpr 20#5) = data)
    (h22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 xs.length)
    (h19 : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 a)
    (h23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 b)
    (h1 : s.readReg64 .x1 = BitVec.ofNat 64 c)
    (ha : a < xs.length) (hb : b < xs.length) (hc : c < xs.length) (hfit : xs.length < 2 ^ 64) :
    CountedWP (program base) (base + 0x90#64) s ((data ↦₆₄* xs) ∗ R)
      (fun count t P => count ≤ 25 ∧ P = (data ↦₆₄* xs) ∗ R ∧ t.sp = s.sp ∧
        untouched s t ∧ t.readReg64 (.gpr 19#5) = BitVec.ofNat 64 (medianIndex xs a b c)) := by
  have code := pivotCode base
  have hA := bounded_unsigned ha hfit
  have hB := bounded_unsigned hb hfit
  have hC := bounded_unsigned hc hfit
  cost_steps 3
  cost_steps 2
  cost_steps 2
  have hfA : (program base).fetch (base + 0x144#64) =
      some (.ldr .W64 .X64 false (.gpr 10#5) (.RegOffset (.gpr 20#5) (.gpr 19#5) .UXTX 3)) := by
    rw [fetch_off]
    decide +kernel
  refine CountedWP.step_ldr64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) hfA rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, h20, h19]) (pivot_array_load data xs a ha R) rfl ?_
  cost_norm_state
  have hfB : (program base).fetch (base + 0x148#64) =
      some (.ldr .W64 .X64 false (.gpr 9#5) (.RegOffset (.gpr 20#5) (.gpr 23#5) .UXTX 3)) := by
    rw [fetch_off]
    decide +kernel
  refine CountedWP.step_ldr64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) hfB rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, h20, h23]) (pivot_array_load data xs b hb R) rfl ?_
  cost_norm_state
  cost_steps 1
  have hfC : (program base).fetch (base + 0x150#64) =
      some (.ldr .W64 .X64 false (.gpr 11#5) (.RegOffset (.gpr 20#5) .x1 .UXTX 3)) := by
    rw [fetch_off]
    decide +kernel
  refine CountedWP.step_ldr64 (wb := none) (by wp_norm_lhs) (by wp_norm_lhs) hfC rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, h20, h1]) (pivot_array_load data xs c hc R) rfl ?_
  cost_norm_state
  cost_steps 6
  cost_if chooseA
  · apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    by_cases ab : (xs[a]?.getD default).toInt < (xs[b]?.getD default).toInt <;>
      by_cases ac : (xs[a]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      by_cases bc : (xs[b]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      simp [medianIndex, untouched, wp_norm, arm64_norm, h19, h23, h1,
        BitVec.sle_iff_toInt_le, BitVec.slt_iff_toInt_lt, ← Int.not_lt, ab, ac, bc] at chooseA ⊢
  · cost_steps 8
    apply CountedWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    by_cases ab : (xs[a]?.getD default).toInt < (xs[b]?.getD default).toInt <;>
      by_cases ac : (xs[a]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      by_cases bc : (xs[b]?.getD default).toInt < (xs[c]?.getD default).toInt <;>
      simp [medianIndex, untouched, wp_norm, arm64_norm, h19, h23, h1,
        BitVec.sle_iff_toInt_le, BitVec.slt_iff_toInt_lt, ← Int.not_lt, ab, ac, bc] at chooseA ⊢


private theorem untouched.trans {s t u : State} (first : untouched s t) (last : untouched t u) :
    untouched s u :=
  ⟨last.1.trans first.1, last.2.1.trans first.2.1, last.2.2.trans first.2.2⟩

private theorem untouched.of_abi {s t : State} (abi : CalleeSavedPreserved s t) :
    untouched s t :=
  ⟨abi.2.2.2.2.2.2.2.2.1, abi.2.2.2.2.2.2.2.2.2.1, abi.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem invoke_pivot {base data : BitVec 64} {xs : List (BitVec 64)}
    {a b c span frames : Nat} {s : State} {R : SepProp}
    (ok : CountedOk (program base) base (pivotHelperSpec data xs a b c span frames)
      (pivotHelperPost data xs a b c span frames))
    (pc : s.pc = base) (running : s.status = .Running) (align : s.spAligned = true)
    (loaded : (program base).CodeLoaded s.mem)
    (memory : s.mem ⊨ (data ↦₆₄* xs) ∗ stackAt s.sp (80 * frames) ∗ R)
    (x0 : s.readReg64 .x0 = data) (x1 : s.readReg64 .x1 = BitVec.ofNat 64 xs.length)
    (x2 : s.readReg64 .x2 = BitVec.ofNat 64 a) (x3 : s.readReg64 .x3 = BitVec.ofNat 64 b)
    (x4 : s.readReg64 (.gpr 4#5) = BitVec.ofNat 64 c)
    (x5 : s.readReg64 (.gpr 5#5) = BitVec.ofNat 64 span) :
    ∃ count t p, CodeStepsN (program base) count s t ∧ Returned s t ∧ CallingConventionPreserved s t ∧
      t.readReg64 .x0 = 1#64 ∧ t.readReg64 .x1 = BitVec.ofNat 64 p ∧
      Pivot.PivotChoice xs a b c span p ∧ QuickselectCost.PivotCosts 96 span count ∧
      t.mem ⊨ (data ↦₆₄* xs) ∗ stackAt s.sp (80 * frames) ∗ R := by
  have pre : s.mem ⊨ (pivotHelperSpec data xs a b c span frames).pre () s ∗ R := by
    simp only [pivotHelperSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨x0, x1, x2, x3, x4, x5⟩, by simpa only [sepConj_assoc] using memory⟩
  obtain ⟨count, t, steps, returned, abi, post⟩ := ok () R s pc running align pre loaded
  simp only [pivotHelperPost, sepExists_sepConj_left, sepConj_assoc, satisfies_sepExists,
    satisfies_pure_sepConj] at post
  obtain ⟨p, ⟨y0, y1, choice, budget⟩, mem⟩ := post
  exact ⟨count, t, p, steps, returned, abi, y0, y1, choice, budget,
    by simpa only [sepConj_assoc] using mem⟩

private theorem finish_pivot {base data : BitVec 64} {xs : List (BitVec 64)}
    {a b c span frames count p : Nat} {s t : State} {R : SepProp}
    (before : CodeStepsN (program base) count s t)
    (pc : t.pc = base + 0x90#64) (running : t.status = .Running)
    (sp : t.sp = s.sp - 80#64) (align : s.spAligned = true) (hu : untouched s t)
    (x19 : t.readReg64 (.gpr 19#5) = BitVec.ofNat 64 p)
    (size : 80 * (frames + 1) ≤ 2 ^ 64)
    (loaded : (program base).CodeLoaded s.mem)
    (memory : t.mem ⊨ ((data ↦₆₄* xs) ∗ stackAt (s.sp - 80#64) (80 * frames) ∗ pivotSaved s) ∗ R)
    (choice : Pivot.PivotChoice xs a b c span p)
    (budget : QuickselectCost.PivotCosts 96 span (count + 9)) :
    ∃ n f, CodeStepsN (program base) n s f ∧ Returned s f ∧ CallingConventionPreserved s f ∧
      f.mem ⊨ pivotHelperPost data xs a b c span (frames + 1) n () s f ∗ R := by
  obtain ⟨_, u, _, preRet, uPC, uRun, uMem, rfl, rfl, uSP, uUntouched, uTag, uP⟩ :=
    pivot_success base t _ pc running R memory (before.toStepsN.toSteps.codeLoaded loaded)
  have usp : u.sp = s.sp - 80#64 := uSP.trans sp
  have ualign : u.spAligned = true := by
    simpa only [State.spAligned, usp] using s.spAligned_sub 80#64 align
  obtain ⟨_, f, Pf, tail, fPC, fRun, fMem, rfl, entail, abi, fTag, fP⟩ :=
    pivot_epilogue base s u frames (data ↦₆₄* xs) uPC uRun usp ualign size (hu.trans uUntouched)
      R uMem ((before.append preRet).toStepsN.toSteps.codeLoaded loaded)
  refine ⟨count + 9, f, by simpa only [Nat.add_assoc] using (before.append preRet).append tail,
    ⟨fPC, abi.1, fRun⟩, abi, ?_⟩
  simp only [pivotHelperPost, sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨p, ⟨fTag.trans uTag, fP.trans (uP.trans x19), choice, budget⟩,
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left entail) fMem⟩

private theorem scale_index (n width : Nat) :
    BitVec.ofNat 64 n <<< width = BitVec.ofNat 64 (2 ^ width * n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofNat_mul, BitVec.mul_comm]
  congr 1
  rw [BitVec.twoPow_eq]
  change BitVec.ofNat 64 ((1 : Nat) <<< width) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

/-- Verify every recursive pseudo-median invocation against the linked ARM64
    instructions. Three disjoint sample blocks establish a valid pivot and
    the recorded instruction count satisfies the ternary cost recurrence. -/
theorem pivot_helper_correct (base data : BitVec 64) (xs : List (BitVec 64))
    (a b c span frames : Nat)
    (blocks : Pivot.ThreeBlocks xs a b c span) (arrayFit : xs.length < 2 ^ 64)
    (depth : span < 9 ^ frames) (size : 80 * frames ≤ 2 ^ 64) :
    CountedOk (program base) base (pivotHelperSpec data xs a b c span frames)
      (pivotHelperPost data xs a b c span frames) := by
  induction frames generalizing a b c span with
  | zero =>
    have hp := blocks.positive
    simp at depth
    omega
  | succ frames ih =>
    intro input R s pc running align pre loaded
    cases input
    simp only [pivotHelperSpec, sepConj_assoc, satisfies_pure_sepConj] at pre
    obtain ⟨⟨x0, x1, x2, x3, x4, x5⟩, memory⟩ := pre
    let A := data ↦₆₄* xs
    let stackRest := stackAt (s.sp - 80#64) (80 * frames)
    let body := A ∗ stackRest ∗ pivotSaved s
    have entryMem : s.mem ⊨ (A ∗ stackAt s.sp (80 * (frames + 1))) ∗ R := by
      simpa only [A, sepConj_assoc] using memory
    obtain ⟨_, init, _, initSteps, initPC, initRun, initMem, rfl, rfl, initSP,
      initU, dataReg, lengthReg, firstReg, secondReg, thirdReg, spanReg, flags⟩ :=
      pivot_prologue base s frames A pc running align size R entryMem loaded
    have initLoaded := initSteps.toStepsN.toSteps.codeLoaded loaded
    have hp := blocks.positive
    have hab := blocks.ab
    have hbc := blocks.bc
    have hfit := blocks.fits
    have spanFit : span < 2 ^ 64 := by omega
    by_cases short : span < 9
    · have test : (9#64).ule (init.readReg64 (.gpr 5#5)) = false := by
        rw [spanReg, x5]
        exact bounded_unsigned short (by decide)
      obtain ⟨_, start, _, branch, startPC, startRun, startMem, rfl, rfl, startEq⟩ :=
        pivot_branch base init body initPC initRun (by rw [spanReg]; exact flags) false test R initMem initLoaded
      have medMem : start.mem ⊨ (A ∗ (stackRest ∗ pivotSaved s)) ∗ R := by
        simpa only [body, sepConj_assoc] using startMem
      obtain ⟨n, m, _, medSteps, medPC, medRun, medMem, medCost, rfl, medSP, medU, medP⟩ :=
        pivot_leaf_median base data start xs a b c (stackRest ∗ pivotSaved s) startPC startRun
          (by simp only [startEq, wp_norm, arm64_norm, dataReg, x0])
          (by simp only [startEq, wp_norm, arm64_norm, lengthReg, x1])
          (by simp only [startEq, wp_norm, arm64_norm, firstReg, x2])
          (by simp only [startEq, wp_norm, arm64_norm, secondReg, x3])
          (by simp only [startEq, wp_norm, arm64_norm, thirdReg, x4])
          (by omega) (by omega) (by omega) arrayFit R medMem
            (branch.toStepsN.toSteps.codeLoaded initLoaded)
      refine finish_pivot ((initSteps.append branch).append medSteps) medPC medRun
        (medSP.trans (by simpa only [startEq, wp_norm, arm64_norm] using initSP)) align
        (initU.trans (by simpa only [startEq, untouched, wp_norm, arm64_norm] using medU)) medP size loaded
        (by simpa only [A, sepConj_assoc] using medMem)
        (.leaf short (Pivot.median_of_choice rfl)) (.leaf hp short (by omega))
    · have large : 9 ≤ span := by omega
      have test : (9#64).ule (init.readReg64 (.gpr 5#5)) = true := by
        rw [spanReg, x5]
        exact BitVec.ule_iff_toNat_le.mpr (by rw [nat_ofNat span spanFit]; exact large)
      obtain ⟨_, start, _, branch, startPC, startRun, startMem, rfl, rfl, startEq⟩ :=
        pivot_branch base init body initPC initRun (by rw [spanReg]; exact flags) true test R initMem initLoaded
      have startSP : start.sp = s.sp - 80#64 := by
        simpa only [startEq, wp_norm, arm64_norm] using initSP
      have startU : untouched s start := by
        simpa only [startEq, untouched, wp_norm, arm64_norm] using initU
      have start20 : start.readReg64 (.gpr 20#5) = data := by
        simp only [startEq, wp_norm, arm64_norm, dataReg, x0]
      have start22 : start.readReg64 (.gpr 22#5) = BitVec.ofNat 64 xs.length := by
        simp only [startEq, wp_norm, arm64_norm, lengthReg, x1]
      have start19 : start.readReg64 (.gpr 19#5) = BitVec.ofNat 64 a := by
        simp only [startEq, wp_norm, arm64_norm, firstReg, x2]
      have start23 : start.readReg64 (.gpr 23#5) = BitVec.ofNat 64 b := by
        simp only [startEq, wp_norm, arm64_norm, secondReg, x3]
      have start21 : start.readReg64 (.gpr 21#5) = BitVec.ofNat 64 c := by
        simp only [startEq, wp_norm, arm64_norm, thirdReg, x4]
      have start5 : (start.readReg64 (.gpr 5#5)).toNat = span := by
        simp only [startEq, wp_norm, arm64_norm, spanReg, x5, nat_ofNat span spanFit]
      have childAlign (t : State) (h : t.sp = s.sp - 80#64) : t.spAligned = true := by
        simpa only [State.spAligned, h] using s.spAligned_sub 80#64 align
      have childDepth : span / 9 < 9 ^ frames := by
        rw [Nat.pow_succ] at depth
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 9)).2 depth
      have childSize : 80 * frames ≤ 2 ^ 64 := by omega
      have validA := Pivot.child_blocks (xs := xs) (a := a) large (by omega)
      have validB := Pivot.child_blocks (xs := xs) (a := b) large (by omega)
      have validC := Pivot.child_blocks (xs := xs) (a := c) large (by omega)
      have arg4 (i : Nat) : BitVec.ofNat 64 i + (BitVec.ofNat 64 (span / 9) <<< 2) =
          BitVec.ofNat 64 (i + 4 * (span / 9)) := by
        rw [scale_index, BitVec.ofNat_add]
      have arg8 (i : Nat) : BitVec.ofNat 64 i + (BitVec.ofNat 64 (span / 9) <<< 3) =
          BitVec.ofNat 64 (i + 8 * (span / 9)) := by
        rw [scale_index, BitVec.ofNat_add]

      -- First child, under the saved registers of this invocation.
      let throughBranch := initSteps.append branch
      have startLoaded := throughBranch.toStepsN.toSteps.codeLoaded loaded
      obtain ⟨_, sa, _, callA, pcA, runA, memA, rfl, rfl, spA, uA, linkA, x0a, x1a, x2a,
        a19, a20, a21, a22, a23, x3a, x4a, x5a, a24, a25, a26⟩ :=
        pivot_first_call base start body startPC startRun R startMem startLoaded
      have spAS : sa.sp = s.sp - 80#64 := spA.trans startSP
      have saMem : sa.mem ⊨ A ∗ stackAt sa.sp (80 * frames) ∗ (pivotSaved s ∗ R) := by
        simpa only [body, stackRest, spAS, sepConj_assoc] using memA
      obtain ⟨na, ra, pa, childA, retA, abiA, someA, pA, choiceA, costA, retMemA⟩ :=
        invoke_pivot (ih _ _ _ _ validA childDepth childSize) pcA runA (childAlign sa spAS)
          (callA.toStepsN.toSteps.codeLoaded startLoaded) saMem
          (x0a.trans start20) (x1a.trans start22) (x2a.trans start19)
          (by simpa only [start19, start5, arg4] using x3a)
          (by simpa only [start19, start5, arg8] using x4a)
          (by simpa only [start5] using x5a)
      have prefA := (throughBranch.append callA).append childA
      have raMem : ra.mem ⊨ body ∗ R := by
        simpa only [body, stackRest, spAS, sepConj_assoc] using retMemA
      have raSP : ra.sp = s.sp - 80#64 := abiA.1.trans spAS
      have raU : untouched s ra := (startU.trans uA).trans (untouched.of_abi abiA.2)
      obtain ⟨rA19, rA20, rA21, rA22, rA23, rA24, rA25, rA26, _⟩ := abiA.2

      -- Second child. The first index is saved in x19 across the call.
      obtain ⟨_, sb, _, callB, pcB, runB, memB, rfl, rfl, spB, uB, linkB, x0b, x1b, x2b,
        x3b, x4b, x5b, b19, b20, b21, b22, b24, b25, b26⟩ :=
        pivot_second_call base ra body (retA.1.trans linkA) retA.2.2 someA R raMem
          (prefA.toStepsN.toSteps.codeLoaded loaded)
      have spBS : sb.sp = s.sp - 80#64 := spB.trans raSP
      have sbMem : sb.mem ⊨ A ∗ stackAt sb.sp (80 * frames) ∗ (pivotSaved s ∗ R) := by
        simpa only [body, stackRest, spBS, sepConj_assoc] using memB
      have mid23 : ra.readReg64 (.gpr 23#5) = BitVec.ofNat 64 b := (rA23.trans a23).trans start23
      have mid24 : ra.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (span / 9) := by
        simpa only [start5] using rA24.trans a24
      have mid25 : ra.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (span / 9) <<< 2 := by
        simpa only [start5] using rA25.trans a25
      have mid26 : ra.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (span / 9) <<< 3 := by
        simpa only [start5] using rA26.trans a26
      obtain ⟨nb, rb, pb, childB, retB, abiB, someB, pB, choiceB, costB, retMemB⟩ :=
        invoke_pivot (ih _ _ _ _ validB childDepth childSize) pcB runB (childAlign sb spBS)
          ((prefA.append callB).toStepsN.toSteps.codeLoaded loaded) sbMem
          ((x0b.trans (rA20.trans a20)).trans start20)
          ((x1b.trans (rA22.trans a22)).trans start22) (x2b.trans mid23)
          (by simpa only [mid23, mid25, arg4] using x3b)
          (by simpa only [mid23, mid26, arg8] using x4b)
          (x5b.trans mid24)
      have prefB := (prefA.append callB).append childB
      have rbMem : rb.mem ⊨ body ∗ R := by
        simpa only [body, stackRest, spBS, sepConj_assoc] using retMemB
      have rbSP : rb.sp = s.sp - 80#64 := abiB.1.trans spBS
      have rbU : untouched s rb := (raU.trans uB).trans (untouched.of_abi abiB.2)
      obtain ⟨rB19, rB20, rB21, rB22, _, rB24, rB25, rB26, _⟩ := abiB.2

      -- Third child. The first two indices are saved in x19 and x23.
      obtain ⟨_, sc, _, callC, pcC, runC, memC, rfl, rfl, spC, uC, linkC, x0c, x1c, x2c,
        x3c, x4c, x5c, c19, c20, c22, c23⟩ :=
        pivot_third_call base rb body (retB.1.trans linkB) retB.2.2 someB R rbMem
          (prefB.toStepsN.toSteps.codeLoaded loaded)
      have spCS : sc.sp = s.sp - 80#64 := spC.trans rbSP
      have scMem : sc.mem ⊨ A ∗ stackAt sc.sp (80 * frames) ∗ (pivotSaved s ∗ R) := by
        simpa only [body, stackRest, spCS, sepConj_assoc] using memC
      have end21 : rb.readReg64 (.gpr 21#5) = BitVec.ofNat 64 c :=
        ((rB21.trans b21).trans (rA21.trans a21)).trans start21
      have end24 := (rB24.trans b24).trans mid24
      have end25 := (rB25.trans b25).trans mid25
      have end26 := (rB26.trans b26).trans mid26
      have end20 := ((rB20.trans b20).trans (rA20.trans a20)).trans start20
      have end22 := ((rB22.trans b22).trans (rA22.trans a22)).trans start22
      obtain ⟨nc, rc, pC, childC, retC, abiC, someC, pCReg, choiceC, costC, retMemC⟩ :=
        invoke_pivot (ih _ _ _ _ validC childDepth childSize) pcC runC (childAlign sc spCS)
          ((prefB.append callC).toStepsN.toSteps.codeLoaded loaded) scMem
          (x0c.trans end20) (x1c.trans end22) (x2c.trans end21)
          (by simpa only [end21, end25, arg4] using x3c)
          (by simpa only [end21, end26, arg8] using x4c)
          (x5c.trans end24)
      have prefC := (prefB.append callC).append childC
      have rcMem : rc.mem ⊨ body ∗ R := by
        simpa only [body, stackRest, spCS, sepConj_assoc] using retMemC
      have rcSP : rc.sp = s.sp - 80#64 := abiC.1.trans spCS
      have rcU : untouched s rc := (rbU.trans uC).trans (untouched.of_abi abiC.2)
      obtain ⟨rC19, rC20, _, rC22, rC23, _⟩ := abiC.2

      -- Median of the three returned indices, followed by the shared return.
      obtain ⟨_, ms, _, confirm, mpc, mrun, mMem, rfl, rfl, mSP, mU, m1, m19, m20, m22, m23⟩ :=
        pivot_confirm_third base rc body (retC.1.trans linkC) retC.2.2 someC R rcMem
          (prefC.toStepsN.toSteps.codeLoaded loaded)
      have prefixMed := prefC.append confirm
      have medMem : ms.mem ⊨ (A ∗ (stackRest ∗ pivotSaved s)) ∗ R := by
        simpa only [body, sepConj_assoc] using mMem
      have paFit := (choiceA.ranked validA).last
      have pbFit := (choiceB.ranked validB).last
      have pcFit := (choiceC.ranked validC).last
      obtain ⟨nm, m, _, median, medPC, medRun, medMem, medCost, rfl, medSP, medU, medP⟩ :=
        pivot_internal_median base data ms xs pa pb pC (stackRest ∗ pivotSaved s) mpc mrun
          ((m20.trans (rC20.trans c20)).trans end20)
          ((m22.trans (rC22.trans c22)).trans end22)
          ((m19.trans (rC19.trans c19)).trans ((rB19.trans b19).trans pA))
          ((m23.trans (rC23.trans c23)).trans pB)
          (m1.trans pCReg) (by omega) (by omega) (by omega) arrayFit R medMem
          (prefixMed.toStepsN.toSteps.codeLoaded loaded)
      have cost : QuickselectCost.PivotCosts 96 span
          ((((((12 + 1) + 15 + na) + 9 + nb) + 10 + nc) + 2) + nm + 9) := by
        let localCost := 12 + 1 + 15 + 9 + 10 + 2 + nm + 9
        have localFit : localCost ≤ 96 := by dsimp [localCost]; omega
        have sum := QuickselectCost.PivotCosts.branch large localFit costA costB costC
        exact (show localCost + na + nb + nc =
          ((((((12 + 1) + 15 + na) + 9 + nb) + 10 + nc) + 2) + nm + 9) by
          dsimp [localCost]; omega) ▸ sum
      exact finish_pivot (prefixMed.append median) medPC medRun
        (medSP.trans (mSP.trans rcSP)) align ((rcU.trans mU).trans medU) medP size loaded
        (by simpa only [A, sepConj_assoc] using medMem)
        (.branch large choiceA choiceB choiceC (Pivot.median_of_choice rfl)) cost

end Example04Rust
