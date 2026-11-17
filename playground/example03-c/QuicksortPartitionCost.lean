import QuicksortCountedCall
import QuicksortPartition

namespace Example03C.PartitionCost

open Arm64 ProofLib Example02C

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

private abbrev Byte := BitVec 8
private abbrev Addr := BitVec 64
private abbrev words := Example02C.Partition.words

/-- Instruction count for a partition with `tailLength` elements after the pivot
    and `leftLength` elements strictly smaller than the pivot. -/
def instructionCount (tailLength leftLength : Nat) : Nat :=
  if tailLength = 0 then 9 else 12 + 6 * tailLength + 5 * leftLength

private abbrev postFor (base : Addr) (pivot : Byte) (tail : List Byte)
    (indexProp : Nat → Prop) (sf : State) : SepProp :=
  ∃∗ left : List Byte, ∃∗ right : List Byte,
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 left.length ∧ (left ++ pivot :: right).Perm (pivot :: tail) ∧
      (∀ a ∈ left, a < pivot) ∧ (∀ a ∈ right, pivot ≤ a) ∧ indexProp left.length⌝ ∗
      (base ↦ₛ (left ++ pivot :: right))

/-- Partition result and exact cost, paired with the ordinary partition precondition. -/
def post (base : Addr) (pivot : Byte) (tail : List Byte) (steps : Nat)
    (_ : Unit) (_ sf : State) : SepProp :=
  postFor base pivot tail (fun index => steps = instructionCount tail.length index) sf

private abbrev ResultPost (base : Addr) (pivot : Byte) (tail : List Byte) (initial : State)
    (indexProp : Nat → Nat → Prop) (steps : Nat) (sf : State) (P : SepProp) : Prop :=
  CallingConventionPreserved initial sf ∧ P ⊢ postFor base pivot tail (indexProp steps) sf

/-- One suffix of the scan costs six instructions per remaining element,
    five extra instructions per newly moved element, and four final instructions. -/
private abbrev scanPost (base : Addr) (pivot : Byte) (tail : List Byte) (initial : State)
    (alreadyMoved fixedCost : Nat) :=
  ResultPost base pivot tail initial (fun steps index =>
    steps + 5 * alreadyMoved = fixedCost + 5 * index)

private theorem map_index {prog : Program} {target : Addr} {s initial : State} {P : SepProp}
    {base : Addr} {pivot : Byte} {tail : List Byte} {p q : Nat → Nat → Prop}
    (h : CountedWP prog target s P (ResultPost base pivot tail initial p))
    (imp : ∀ steps index, index ≤ tail.length → p steps index → q steps index) :
    CountedWP prog target s P (ResultPost base pivot tail initial q) := by
  apply CountedWP.mono h
  intro steps sf Pf ⟨abi, post⟩
  refine ⟨abi, Entails.trans post ?_⟩
  unfold postFor
  apply Entails.sepExists_elim
  intro left
  apply Entails.sepExists_elim
  intro right
  apply Entails.pure_left
  rintro ⟨index, perm, leftBound, rightBound, cost⟩
  apply Entails.sepExists_right left
  apply Entails.sepExists_right right
  have lengths := perm.length_eq
  simp only [List.length_append, List.length_cons] at lengths
  exact Entails.pure_right ⟨index, perm, leftBound, rightBound,
    imp steps left.length (by omega) cost⟩ (Entails.refl _)

private theorem write8_eq_set (arr : List Byte) (k : Nat) (v : Byte) (hk : k < arr.length) :
    ByteSlice.write8 arr k v = arr.set k v := by
  simp [ByteSlice.write8, ByteSlice.write, List.set_eq_take_append_cons_drop, hk]

private theorem getD_eq_getElem! (arr : List Byte) (k : Nat) :
    arr.getD k 0#8 = arr[k]! := by
  change arr.getD k (default : Byte) = arr[k]!
  rw [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]

/-- Move the pivot to its final index and return that index in X0. -/
private theorem finish_scan (prog : Program) (entry base : Addr) (pivot : Byte) (tail arr : List Byte)
    (k : Nat) (hwords : prog.hasWords entry words) (initial st : State)
    (hpc : st.pc = entry + 0x50#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = BitVec.ofNat 64 k) (hx8 : st.readReg64 .x8 = base)
    (hx9 : st.readReg64 .x9 = pivot.zeroExtend 64)
    (hlr : st.readReg64 .lr = initial.readReg64 .lr)
    (habi : CallingConventionPreserved initial st)
    (hbound : arr.length < 2 ^ 64)
    (hscan : Spec.PartitionScan (pivot :: tail) arr pivot k arr.length) :
    CountedWP prog (initial.readReg64 .lr) st (base ↦ₛ arr)
      (scanPost base pivot tail initial k 4) := by
  let out := Spec.swap arr 0 k
  let left := out.take k
  let right := out.drop (k + 1)
  have result := hscan.finish
  have hk := hscan.splitBound
  have hkb : k < 2 ^ 64 := by omega
  have hlen : left.length = k := by
    simp [left, out, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hswap : (arr.set 0 arr[k]!).set k pivot = left ++ pivot :: right := by
    simpa only [left, right, out, Spec.swap, List.getElem!_of_getElem? hscan.pivotAtZero] using result.split
  have hperm : (left ++ pivot :: right).Perm (pivot :: tail) := result.split ▸ result.permutation
  have hf20 := Program.fetch_of_hasWords hwords 20 (by decide)
  have hf21 := Program.fetch_of_hasWords hwords 21 (by decide)
  have hf22 := Program.fetch_of_hasWords hwords 22 (by decide)
  have hf23 := Program.fetch_of_hasWords hwords 23 (by decide)
  cost_steps 4
  apply CountedWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  constructor
  · exact ⟨by simpa [wp_norm, arm64_norm] using habi.1,
      habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩
  · simp only [postFor]
    apply Entails.sepExists_right left
    apply Entails.sepExists_right right
    apply Entails.pure_right
    · exact ⟨by simpa [wp_norm, arm64_norm, hlen] using hx0, hperm,
        result.leftBound, result.rightBound, by rw [hlen]⟩
    · have hzero : 0 < arr.length := by omega
      rw [write8_eq_set arr 0 _ hzero, write8_eq_set _ k _ (by simpa using hk)]
      rw [getD_eq_getElem!, hswap]
      exact Entails.refl _

/-- Advance the cursor after handling one element. Exit when the count reaches zero. -/
private theorem scan_bump (prog : Program) (entry base : Addr) (pivot : Byte) (tail arr : List Byte)
    (k i : Nat) (hwords : prog.hasWords entry words) (initial st : State)
    (hpc : st.pc = entry + 0x20#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = BitVec.ofNat 64 k) (hx8 : st.readReg64 .x8 = base)
    (hx9 : st.readReg64 .x9 = pivot.zeroExtend 64)
    (hx10 : st.readReg64 .x10 = BitVec.ofNat 64 (arr.length - (i - 1)))
    (hx11 : st.readReg64 .x11 = base + BitVec.ofNat 64 (i - 1))
    (hlr : st.readReg64 .lr = initial.readReg64 .lr)
    (habi : CallingConventionPreserved initial st)
    (hbound : arr.length < 2 ^ 64)
    (hscan : Spec.PartitionScan (pivot :: tail) arr pivot k i)
    (next : ∀ s : State, s.pc = entry + 0x2c#64 → s.status = .Running →
      s.readReg64 .x0 = BitVec.ofNat 64 k → s.readReg64 .x8 = base →
      s.readReg64 .x9 = pivot.zeroExtend 64 →
      s.readReg64 .x10 = BitVec.ofNat 64 (arr.length - i) →
      s.readReg64 .x11 = base + BitVec.ofNat 64 i →
      s.readReg64 .lr = initial.readReg64 .lr → CallingConventionPreserved initial s → i < arr.length →
      CountedWP prog (initial.readReg64 .lr) s (base ↦ₛ arr)
        (scanPost base pivot tail initial k (4 + 6 * (arr.length - i)))) :
    CountedWP prog (initial.readReg64 .lr) st (base ↦ₛ arr)
      (scanPost base pivot tail initial k (7 + 6 * (arr.length - i))) := by
  have hf8 := Program.fetch_of_hasWords hwords 8 (by decide)
  have hf9 := Program.fetch_of_hasWords hwords 9 (by decide)
  have hf10 := Program.fetch_of_hasWords hwords 10 (by decide)
  have hki := hscan.splitBound
  have hi := hscan.scanBound
  have hcount : arr.length - (i - 1) < 2 ^ 64 := by omega
  cost_steps 3
  cost_if hcond
  · have heq : arr.length - (i - 1) = 1 := by
      have hn := congrArg BitVec.toNat hcond
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount] using hn
    have hil : i = arr.length := by omega
    refine map_index (finish_scan prog entry base pivot tail arr k hwords initial _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hx0)
      (by simpa [wp_norm, arm64_norm] using hx8)
      (by simpa [wp_norm, arm64_norm] using hx9)
      (by simpa [wp_norm, arm64_norm] using hlr)
      ⟨by simpa [wp_norm, arm64_norm] using habi.1,
       habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩
      hbound (hil ▸ hscan)) ?_
    intro steps index _ heq
    simp only at heq ⊢
    omega
  · have hne : arr.length - (i - 1) ≠ 1 := by
      intro hn
      exact hcond (by rw [hn])
    have hi' : i < arr.length := by omega
    have hsub : BitVec.ofNat 64 (arr.length - (i - 1)) - 1#64 = BitVec.ofNat 64 (arr.length - i) := by
      change BitVec.ofNat 64 (arr.length - (i - 1)) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
        show arr.length - (i - 1) - 1 = arr.length - i by omega]
    have hadd : base + BitVec.ofNat 64 (i - 1) + 1#64 = base + BitVec.ofNat 64 i := by
      change _ + BitVec.ofNat 64 1 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show i - 1 + 1 = i by omega]
    refine map_index (next _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hx0)
      (by simpa [wp_norm, arm64_norm] using hx8)
      (by simpa [wp_norm, arm64_norm] using hx9)
      (by simpa [wp_norm, arm64_norm] using hsub)
      (by simpa [wp_norm, arm64_norm] using hadd)
      (by simpa [wp_norm, arm64_norm] using hlr)
      ⟨by simpa [wp_norm, arm64_norm] using habi.1,
       habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩ hi') ?_
    intro steps index _ heq
    simp only at heq ⊢
    omega

/-- The scan loop terminates as the number of unprocessed elements decreases. -/
private theorem scan (prog : Program) (entry base : Addr) (pivot : Byte) (tail : List Byte)
    (hwords : prog.hasWords entry words) (initial : State) (hbound : (pivot :: tail).length < 2 ^ 64)
    (arr : List Byte) (k i : Nat) (st : State)
    (hpc : st.pc = entry + 0x2c#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = BitVec.ofNat 64 k) (hx8 : st.readReg64 .x8 = base)
    (hx9 : st.readReg64 .x9 = pivot.zeroExtend 64)
    (hx10 : st.readReg64 .x10 = BitVec.ofNat 64 (arr.length - i))
    (hx11 : st.readReg64 .x11 = base + BitVec.ofNat 64 i)
    (hlr : st.readReg64 .lr = initial.readReg64 .lr)
    (habi : CallingConventionPreserved initial st)
    (hscan : Spec.PartitionScan (pivot :: tail) arr pivot k i) (hi : i < arr.length) :
    CountedWP prog (initial.readReg64 .lr) st (base ↦ₛ arr)
      (scanPost base pivot tail initial k (4 + 6 * (arr.length - i))) := by
  suffices go : ∀ (remaining : Nat) (arr : List Byte) (k i : Nat) (st : State),
      remaining = arr.length - i →
      st.pc = entry + 0x2c#64 → st.status = .Running →
      st.readReg64 .x0 = BitVec.ofNat 64 k → st.readReg64 .x8 = base →
      st.readReg64 .x9 = pivot.zeroExtend 64 →
      st.readReg64 .x10 = BitVec.ofNat 64 (arr.length - i) →
      st.readReg64 .x11 = base + BitVec.ofNat 64 i →
      st.readReg64 .lr = initial.readReg64 .lr → CallingConventionPreserved initial st →
      Spec.PartitionScan (pivot :: tail) arr pivot k i → i < arr.length →
      CountedWP prog (initial.readReg64 .lr) st (base ↦ₛ arr)
      (scanPost base pivot tail initial k (4 + 6 * (arr.length - i))) from
    go (arr.length - i) arr k i st rfl hpc hrun hx0 hx8 hx9 hx10 hx11 hlr habi hscan hi
  intro remaining
  induction remaining using Nat.strongRecOn
  rename_i remaining recur
  intro arr k i st hremaining hpc hrun hx0 hx8 hx9 hx10 hx11 hlr habi hscan hi
  have hf11 := Program.fetch_of_hasWords hwords 11 (by decide)
  have hf12 := Program.fetch_of_hasWords hwords 12 (by decide)
  have hf13 := Program.fetch_of_hasWords hwords 13 (by decide)
  have hf14 := Program.fetch_of_hasWords hwords 14 (by decide)
  have hf15 := Program.fetch_of_hasWords hwords 15 (by decide)
  have hf16 := Program.fetch_of_hasWords hwords 16 (by decide)
  have hf17 := Program.fetch_of_hasWords hwords 17 (by decide)
  have hf18 := Program.fetch_of_hasWords hwords 18 (by decide)
  have hlen := hscan.permutation.length_eq
  have hki := hscan.splitBound
  have hi' : i < 2 ^ 64 := by omega
  have hk' : k + 1 < arr.length := by omega
  have hka : k < 2 ^ 64 := by omega
  have hcompare : (pivot.zeroExtend 64).ule ((arr.getD i 0#8).zeroExtend 64) = true ↔ pivot ≤ arr[i]! := by
    simp only [BitVec.ule_eq_decide, BitVec.zeroExtend,
      BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64), decide_eq_true_eq,
      getD_eq_getElem!, ← BitVec.le_def]
  cost_steps 3
  cost_if hcond
  · have hle : pivot ≤ arr[i]! := hcond
    have hscan' := hscan.advance_high hi hle
    refine map_index (scan_bump prog entry base pivot tail arr k (i + 1) hwords initial _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hx0)
      (by simpa [wp_norm, arm64_norm] using hx8)
      (by simpa [wp_norm, arm64_norm] using hx9)
      (by simpa [wp_norm, arm64_norm] using hx10)
      (by simpa [wp_norm, arm64_norm] using hx11)
      (by simpa [wp_norm, arm64_norm] using hlr)
      ⟨by simpa [wp_norm, arm64_norm] using habi.1,
       habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩
      (by omega) hscan' ?_) ?_
    · intro s hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hi''
      exact recur (arr.length - (i + 1)) (by omega) arr k (i + 1) s rfl
        hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hscan' hi''
    · intro steps index _ heq
      simp only at heq ⊢
      omega
  · have hlt : arr[i]! < pivot := BitVec.not_le.mp hcond
    have hscan' := hscan.advance_low hi hlt
    cost_steps 5
    have hswap : ByteSlice.write8 (ByteSlice.write8 arr (k + 1) (arr.getD i 0#8)) i (arr.getD (k + 1) 0#8) =
        Spec.swap arr (k + 1) i := by
      rw [write8_eq_set _ _ _ hk', write8_eq_set _ _ _ (by simpa using hi)]
      simp only [Spec.swap, getD_eq_getElem!]
    rw [hswap]
    refine map_index (scan_bump prog entry base pivot tail (Spec.swap arr (k + 1) i)
      (k + 1) (i + 1) hwords initial _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, BitVec.ofNat_add])
      (by simpa [wp_norm, arm64_norm] using hx8)
      (by simpa [wp_norm, arm64_norm] using hx9)
      (by simpa [wp_norm, arm64_norm] using hx10)
      (by simpa [wp_norm, arm64_norm] using hx11)
      (by simpa [wp_norm, arm64_norm] using hlr)
      ⟨by simpa [wp_norm, arm64_norm] using habi.1,
       habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩
      (by simpa using (show arr.length < 2 ^ 64 from hlen.symm ▸ hbound)) hscan' ?_) ?_
    · intro s hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hi''
      refine recur ((Spec.swap arr (k + 1) i).length - (i + 1)) ?_
        (Spec.swap arr (k + 1) i) (k + 1) (i + 1) s rfl
        hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hscan' hi''
      simp only [Spec.swap_length]
      omega
    · intro steps index _ heq
      simp only [Spec.swap_length] at heq ⊢
      omega

/-- Count the actual linked partition instructions and verify the pivot split. -/
theorem of_words (prog : Program) (entry base : Addr) (pivot : Byte) (tail : List Byte)
    (hwords : prog.hasWords entry words) :
    CountedOk prog entry (Example02C.Partition.spec base pivot tail) (post base pivot tail) := by
  intro _ frame s0 hpc hrun _ hpre loaded
  rw [Example02C.Partition.spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hbound⟩, memory⟩
  have hw : CountedWP prog (s0.readReg64 .lr) s0 (base ↦ₛ (pivot :: tail))
      (ResultPost base pivot tail s0 (fun steps index =>
        steps = instructionCount tail.length index)) := by
    have hf0 := Program.fetch_of_hasWords hwords 0 (by decide)
    have hf1 := Program.fetch_of_hasWords hwords 1 (by decide)
    have hf2 := Program.fetch_of_hasWords hwords 2 (by decide)
    have hf3 := Program.fetch_of_hasWords hwords 3 (by decide)
    have hf4 := Program.fetch_of_hasWords hwords 4 (by decide)
    have hf5 := Program.fetch_of_hasWords hwords 5 (by decide)
    have hf6 := Program.fetch_of_hasWords hwords 6 (by decide)
    have hf7 := Program.fetch_of_hasWords hwords 7 (by decide)
    have hf19 := Program.fetch_of_hasWords hwords 19 (by decide)
    have hinvariant := Spec.partitionScan_start (arr := pivot :: tail) (pivot := pivot) rfl
    rw [pointsToBytes_cons]
    cost_steps 4
    cost_if hshort
    · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound] at hshort
      have hone : (pivot :: tail).length = 1 := by
        simp only [List.length_cons] at hshort ⊢
        omega
      have hzero : tail.length = 0 := by simpa using hone
      cost_step
      rw [← pointsToBytes_cons]
      refine map_index (finish_scan prog entry base pivot tail (pivot :: tail) 0 hwords s0 _
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hbound ?_) ?_
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hrun]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [CallingConventionPreserved, CalleeSavedPreserved, wp_norm, arm64_norm]
      · rw [hone]
        exact hinvariant
      · intro steps index bound heq
        simp [instructionCount, hzero]
        omega
    · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound] at hshort
      have hlong : 1 < (pivot :: tail).length := by omega
      cost_steps 4
      rw [← pointsToBytes_cons]
      refine map_index (scan prog entry base pivot tail hwords s0 hbound (pivot :: tail) 0 1 _
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hinvariant hlong) ?_
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hrun]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simpa [wp_norm, arm64_norm] using BitVec.ofNat_sub_ofNat_of_le (w := 64)
          (pivot :: tail).length 1 (by decide) (by omega)
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [CallingConventionPreserved, CalleeSavedPreserved, wp_norm, arm64_norm]
      · intro steps index _ heq
        simp only [List.length_cons, Nat.add_sub_cancel] at heq
        have hne : tail.length ≠ 0 := by simp only [List.length_cons] at hlong; omega
        simp [instructionCount, hne]
        omega
  obtain ⟨steps, sf, Pf, run, pc, running, mem, abi, result⟩ := hw frame memory loaded
  exact ⟨steps, sf, run, ⟨pc, abi.1, running⟩, abi, Satisfies.mono (sepConj_mono_left result) mem⟩

end Example03C.PartitionCost
