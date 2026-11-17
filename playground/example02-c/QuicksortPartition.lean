import ProofLib
import QuicksortSpec

namespace Example02C.Partition

open Arm64 ProofLib

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

private abbrev Byte := BitVec 8
private abbrev Addr := BitVec 64

/-- AArch64 instruction words for the compiled partition function. -/
def words : List (BitVec 32) :=
  [0x39400009#32, 0xaa0003e8#32, 0xf100083f#32, 0x54000203#32,
   0xaa1f03e0#32, 0xd100042a#32, 0x9100050b#32, 0x14000004#32,
   0xf100054a#32, 0x9100056b#32, 0x54000140#32, 0x3940016c#32,
   0x6b09019f#32, 0x54ffff62#32, 0x91000400#32, 0x3860690d#32,
   0x3820690c#32, 0x3900016d#32, 0x17fffff6#32, 0xaa1f03e0#32,
   0x3860690a#32, 0x3900010a#32, 0x38206909#32, 0xd65f03c0#32]

/-- Partition contract for a nonempty writable input array whose first byte is
`pivot`. On return, X0 gives the pivot's index in the same array. The preceding
bytes are strictly less than the pivot, the following bytes are greater than or
equal to it, and the whole array is a permutation of the input. -/
def spec (base : Addr) (pivot : Byte) (tail : List Byte) : Arm64.Spec Unit where
  pre := fun _ s =>
    ⌜s.readReg64 .x0 = base ∧ s.readReg64 .x1 = BitVec.ofNat 64 (pivot :: tail).length ∧
      (pivot :: tail).length < 2 ^ 64⌝ ∗ (base ↦ₛ (pivot :: tail))
  post := fun _ _ s =>
    ∃∗ left : List Byte, ∃∗ right : List Byte,
      ⌜s.readReg64 .x0 = BitVec.ofNat 64 left.length ∧ (left ++ pivot :: right).Perm (pivot :: tail) ∧
        (∀ a ∈ left, a < pivot) ∧ (∀ a ∈ right, pivot ≤ a)⌝ ∗ (base ↦ₛ (left ++ pivot :: right))

private abbrev ResultPost (base : Addr) (pivot : Byte) (tail : List Byte) (initial : State)
    (sf : State) (P : SepProp) : Prop :=
  CallingConventionPreserved initial sf ∧ P ⊢ (spec base pivot tail).post () initial sf

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
    SepWP prog (initial.readReg64 .lr) st (base ↦ₛ arr) (ResultPost base pivot tail initial) := by
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
  wp_steps 4
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  constructor
  · exact ⟨by simpa [wp_norm, arm64_norm] using habi.1,
      habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩
  · simp only [spec]
    apply Entails.sepExists_right left
    apply Entails.sepExists_right right
    apply Entails.pure_right
    · exact ⟨by simpa [wp_norm, arm64_norm, hlen] using hx0, hperm, result.leftBound, result.rightBound⟩
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
      SepWP prog (initial.readReg64 .lr) s (base ↦ₛ arr) (ResultPost base pivot tail initial)) :
    SepWP prog (initial.readReg64 .lr) st (base ↦ₛ arr) (ResultPost base pivot tail initial) := by
  have hf8 := Program.fetch_of_hasWords hwords 8 (by decide)
  have hf9 := Program.fetch_of_hasWords hwords 9 (by decide)
  have hf10 := Program.fetch_of_hasWords hwords 10 (by decide)
  have hki := hscan.splitBound
  have hi := hscan.scanBound
  have hcount : arr.length - (i - 1) < 2 ^ 64 := by omega
  wp_steps 3
  wp_if hcond
  · have heq : arr.length - (i - 1) = 1 := by
      have hn := congrArg BitVec.toNat hcond
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount] using hn
    have hil : i = arr.length := by omega
    exact finish_scan prog entry base pivot tail arr k hwords initial _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hx0)
      (by simpa [wp_norm, arm64_norm] using hx8)
      (by simpa [wp_norm, arm64_norm] using hx9)
      (by simpa [wp_norm, arm64_norm] using hlr)
      ⟨by simpa [wp_norm, arm64_norm] using habi.1,
       habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩
      hbound (hil ▸ hscan)
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
    exact next _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hx0)
      (by simpa [wp_norm, arm64_norm] using hx8)
      (by simpa [wp_norm, arm64_norm] using hx9)
      (by simpa [wp_norm, arm64_norm] using hsub)
      (by simpa [wp_norm, arm64_norm] using hadd)
      (by simpa [wp_norm, arm64_norm] using hlr)
      ⟨by simpa [wp_norm, arm64_norm] using habi.1,
       habi.2.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm])⟩ hi'

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
    SepWP prog (initial.readReg64 .lr) st (base ↦ₛ arr) (ResultPost base pivot tail initial) := by
  suffices go : ∀ (remaining : Nat) (arr : List Byte) (k i : Nat) (st : State),
      remaining = arr.length - i →
      st.pc = entry + 0x2c#64 → st.status = .Running →
      st.readReg64 .x0 = BitVec.ofNat 64 k → st.readReg64 .x8 = base →
      st.readReg64 .x9 = pivot.zeroExtend 64 →
      st.readReg64 .x10 = BitVec.ofNat 64 (arr.length - i) →
      st.readReg64 .x11 = base + BitVec.ofNat 64 i →
      st.readReg64 .lr = initial.readReg64 .lr → CallingConventionPreserved initial st →
      Spec.PartitionScan (pivot :: tail) arr pivot k i → i < arr.length →
      SepWP prog (initial.readReg64 .lr) st (base ↦ₛ arr) (ResultPost base pivot tail initial) from
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
  wp_steps 3
  wp_if hcond
  · have hle : pivot ≤ arr[i]! := hcond
    have hscan' := hscan.advance_high hi hle
    refine scan_bump prog entry base pivot tail arr k (i + 1) hwords initial _
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
      (by omega) hscan' ?_
    intro s hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hi''
    exact recur (arr.length - (i + 1)) (by omega) arr k (i + 1) s rfl
      hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hscan' hi''
  · have hlt : arr[i]! < pivot := BitVec.not_le.mp hcond
    have hscan' := hscan.advance_low hi hlt
    wp_steps 5
    have hswap : ByteSlice.write8 (ByteSlice.write8 arr (k + 1) (arr.getD i 0#8)) i (arr.getD (k + 1) 0#8) =
        Spec.swap arr (k + 1) i := by
      rw [write8_eq_set _ _ _ hk', write8_eq_set _ _ _ (by simpa using hi)]
      simp only [Spec.swap, getD_eq_getElem!]
    rw [hswap]
    refine scan_bump prog entry base pivot tail (Spec.swap arr (k + 1) i) (k + 1) (i + 1) hwords initial _
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
      (by simpa using (show arr.length < 2 ^ 64 from hlen.symm ▸ hbound)) hscan' ?_
    intro s hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hi''
    refine recur ((Spec.swap arr (k + 1) i).length - (i + 1)) ?_ (Spec.swap arr (k + 1) i) (k + 1) (i + 1) s rfl
      hpc' hrun' hx0' hx8' hx9' hx10' hx11' hlr' habi' hscan' hi''
    simp only [Spec.swap_length]
    omega

/-- The partition's compiled instruction sequence implements its contract. -/
theorem of_words (prog : Program) (entry base : Addr) (pivot : Byte) (tail : List Byte)
    (hwords : prog.hasWords entry words) :
    subroutine_ok prog entry (spec base pivot tail) := by
  have hf0 := Program.fetch_of_hasWords hwords 0 (by decide)
  have hf1 := Program.fetch_of_hasWords hwords 1 (by decide)
  have hf2 := Program.fetch_of_hasWords hwords 2 (by decide)
  have hf3 := Program.fetch_of_hasWords hwords 3 (by decide)
  have hf4 := Program.fetch_of_hasWords hwords 4 (by decide)
  have hf5 := Program.fetch_of_hasWords hwords 5 (by decide)
  have hf6 := Program.fetch_of_hasWords hwords 6 (by decide)
  have hf7 := Program.fetch_of_hasWords hwords 7 (by decide)
  have hf19 := Program.fetch_of_hasWords hwords 19 (by decide)
  wp_init u s0
  have hbound : (pivot :: tail).length < 2 ^ 64 := by assumption
  have hinvariant := Spec.partitionScan_start (arr := pivot :: tail) (pivot := pivot) rfl
  wp_steps 4
  wp_if hshort
  · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hbound] at hshort
    have hone : (pivot :: tail).length = 1 := by simp only [List.length_cons] at hshort ⊢; omega
    wp_step
    rw [← pointsToBytes_cons]
    refine SepWP.mono (finish_scan prog entry base pivot tail (pivot :: tail) 0 hwords s0 _
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
    · intro sf P _ _ ⟨abi, mem⟩
      exact ⟨fun h => Satisfies.mono (sepConj_mono_left mem) h, abi.1, abi.2⟩
  · simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hbound] at hshort
    have hlong : 1 < (pivot :: tail).length := by omega
    wp_steps 4
    rw [← pointsToBytes_cons]
    refine SepWP.mono (scan prog entry base pivot tail hwords s0 hbound (pivot :: tail) 0 1 _
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
    · intro sf P _ _ ⟨abi, mem⟩
      exact ⟨fun h => Satisfies.mono (sepConj_mono_left mem) h, abi.1, abi.2⟩

end Example02C.Partition
