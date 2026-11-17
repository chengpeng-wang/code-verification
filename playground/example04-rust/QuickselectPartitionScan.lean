import QuickselectLeftScan
import QuickselectRightScan
import QuickselectSwap

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false

/-- At the left loop header the current left cursor is below the last
    permissible cursor. The compiler's CMP/CSEL establishes X10 as the limit. -/
private theorem left_limit (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x258#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (below : (s.readReg64 (.gpr 1#5)).toNat < (s.readReg64 (.gpr 8#5)).toNat) :
    ∃ final, CodeStepsN (program base) 2 s final ∧ final.pc = base + 0x260#64 ∧
      final.status = .Running ∧ final.mem = s.mem ∧ final.sp = s.sp ∧ PartitionRegs s final ∧
      final.readReg64 .x1 = s.readReg64 .x1 ∧
      final.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      final.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) ∧
      final.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 8#5) ∧
      final.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      final.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
  let cmp : Instr := .addSubShift .W64 .SUBS .xzr .x1 (.gpr 8#5) .LSL 0
  let limit : Instr := .condSelect .W64 .CSEL (.gpr 10#5) .x1 (.gpr 8#5) .HI
  let s1 := (program base).evalInst cmp s
  let s2 := (program base).evalInst limit s1
  have pc1 : s1.pc = base + 0x25c#64 := by
    simp [s1, cmp, pc, wp_norm, arm64_norm, BitVec.add_assoc]
  have run1 : s1.status = .Running := by simp [s1, cmp, running, wp_norm, arm64_norm]
  have loaded1 : (program base).CodeLoaded s1.mem := by
    simpa [s1, cmp, wp_norm, arm64_norm] using loaded
  have lt : (s.readReg64 (.gpr 8#5)).ult (s.readReg64 (.gpr 1#5)) = false := by
    rw [BitVec.ult_eq_decide]
    exact decide_eq_false (by omega)
  refine ⟨s2, linked_step pc (by decide +kernel)
    (execute_at base _ cmp s pc running loaded (by decide +kernel))
    (linked_step pc1 (by decide +kernel) (execute_at base _ limit s1 pc1 run1 loaded1 (by decide +kernel))
      (.refl _)), ?_⟩
  simp [s2, s1, cmp, limit, pc, running, wp_norm, arm64_norm, BitVec.add_assoc, lt,
    PartitionRegs, CalleeSavedPreserved]

/-- A complete visit to the two scans, starting at the left header and ending
    before either exchange. The count is charged to the cursor movement
    rather than to the size of the entire active slice. -/
theorem partition_scan_pair (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x258#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (openInterval : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 9#5)).toNat)
    (bounded : (s.readReg64 (.gpr 9#5)).toNat ≤ (s.readReg64 (.gpr 8#5)).toNat)
    (readable : ∀ k : BitVec 64, k.toNat ≤ (s.readReg64 (.gpr 8#5)).toNat →
      s.mem.canRead (s.readReg64 (.gpr 20#5) + (k <<< 3)) 8 = true) :
    ∃ count final, CodeStepsN (program base) count s final ∧
      final.status = .Running ∧ final.mem = s.mem ∧ final.sp = s.sp ∧ PartitionRegs s final ∧
      final.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      final.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      final.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      let i := (final.readReg64 .x1).toNat
      let j := (final.readReg64 (.gpr 9#5)).toNat
      let startI := (s.readReg64 .x1).toNat
      let startJ := (s.readReg64 (.gpr 9#5)).toNat
      startI ≤ i ∧ i ≤ j ∧ j ≤ startJ ∧
      count ≤ 10 * ((i - startI) + (startJ - j)) + 11 ∧
      (i - startI) + (startJ - j) ≤ count ∧
      (∀ k, startI ≤ k → k < i →
        (s.mem.read64 (wordAddr (s.readReg64 (.gpr 20#5)) (k + 1))).toInt <
          (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt) ∧
      (i < startJ → (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt ≤
        (s.mem.read64 (wordAddr (s.readReg64 (.gpr 20#5)) (i + 1))).toInt) ∧
      (∀ k, j ≤ k → k < startJ → (final.pc = base + 0x2d8#64 ∨ j < k) →
        (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt <
          (s.mem.read64 (wordAddr (s.readReg64 (.gpr 20#5)) (k + 1))).toInt) ∧
      ((final.pc = base + 0x2d8#64 ∧ i = j) ∨
        (final.pc = base + 0x2b4#64 ∧ final.readReg64 (.gpr 10#5) = final.readReg64 (.gpr 9#5) ∧
          j < startJ ∧ final.readReg64 (.gpr 11#5) =
            s.mem.read64 (s.readReg64 (.gpr 20#5) + ((final.readReg64 (.gpr 9#5) + 1#64) <<< 3)) ∧
          (final.readReg64 (.gpr 11#5)).toInt ≤ (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt)) := by
  obtain ⟨init, prep, ipc, irun, imem, isp, iregs, ii, i8, ij, i10, idata, irest⟩ :=
    left_limit base s pc running loaded (Nat.lt_of_lt_of_le openInterval bounded)
  have initCursors : (init.readReg64 .x1).toNat < (init.readReg64 (.gpr 9#5)).toNat := by
    rwa [ii, ij]
  have initLimit : (init.readReg64 (.gpr 9#5)).toNat ≤ (init.readReg64 (.gpr 10#5)).toNat := by
    rwa [ij, i10]
  have initPivot : init.mem.canRead (init.readReg64 (.gpr 20#5)) 8 = true := by
    simpa [imem, idata] using readable 0 (Nat.zero_le _)
  have initRead (i : BitVec 64) (fit : i.toNat < (init.readReg64 (.gpr 10#5)).toNat) :
      init.mem.canRead (init.readReg64 (.gpr 20#5) + ((i <<< 3) + 8#64)) 8 = true := by
    rw [imem, idata, show (i <<< 3) + 8#64 = (i + 1#64) <<< 3 by
      rw [BitVec.shiftLeft_add_distrib]; rfl]
    apply readable
    rw [i10] at fit
    have bound := (s.readReg64 (.gpr 8#5)).isLt
    rw [BitVec.toNat_add]
    change (i.toNat + 1) % 2^64 ≤ _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨leftCount, mid, leftSteps, mpc, mrun, mmem, msp, mregs, mj, mdata, m8, mrest, mlo, mhi, _, lcost, llower, lstrict, lend⟩ :=
    partition_left_scan base init ipc irun (imem.symm ▸ loaded) initCursors initLimit initPivot initRead
  have fits : (mid.readReg64 (.gpr 9#5)).toNat ≤ (mid.readReg64 (.gpr 8#5)).toNat := by
    rwa [mj, m8, ij, i8]
  have midRead (k : BitVec 64) (fit : k.toNat ≤ (mid.readReg64 (.gpr 8#5)).toNat) :
      mid.mem.canRead (mid.readReg64 (.gpr 20#5) + (k <<< 3)) 8 = true := by
    rw [m8, i8] at fit
    simpa only [mmem, imem, mdata, idata] using readable k fit
  have midOrdered : (mid.readReg64 .x1).toNat ≤ (mid.readReg64 (.gpr 9#5)).toNat := by
    rwa [mj]
  obtain ⟨rightCount, final, right⟩ :=
    partition_right_scan base mid mpc mrun ((mmem.trans imem).symm ▸ loaded) midOrdered fits midRead
  refine ⟨2 + leftCount + rightCount, final, (prep.append leftSteps).append right.steps,
    right.running, right.memory.trans (mmem.trans imem), right.stackPointer.trans (msp.trans isp),
    (iregs.trans mregs).trans right.regs,
    right.length.trans (m8.trans i8), right.array.trans (mdata.trans idata),
    right.rest.trans (mrest.trans irest), ?_⟩
  dsimp only
  have flo := right.lower
  have fhi := right.upper
  rw [right.left]
  rw [ii] at mlo lcost llower lstrict
  rw [ij] at lend
  rw [mj, ij] at fhi
  refine ⟨mlo, flo, fhi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases right.stopped with ⟨_, _, cost⟩ | ⟨_, _, cost, _, _⟩ <;>
      rw [mj, ij] at cost <;> omega
  · rcases right.stopped with ⟨_, _, cost⟩ | ⟨_, _, cost, _, _⟩ <;>
      rw [mj, ij] at cost <;> omega
  · simpa only [imem, idata] using lstrict
  · simpa only [imem, idata] using lend
  · intro k klo khi kind
    simpa only [mmem, imem, mdata, idata] using right.strict k klo (by rwa [mj, ij]) kind
  · rcases right.stopped with ⟨pc, eq, _⟩ | ⟨pc, x10, cost, value, order⟩
    · exact .inl ⟨pc, (congrArg BitVec.toNat eq).symm⟩
    · have positive : 0 < rightCount := by
        -- This exit is reached only after a probe. Its PC differs from the guard.
        by_cases zero : rightCount = 0
        · have zeroSteps : CodeStepsN (program base) 0 mid final := zero ▸ right.steps
          cases zeroSteps
          rw [mpc] at pc
          have neq : (0x28c#64 : BitVec 64) ≠ 0x2b4#64 := by decide
          exact (neq ((BitVec.add_right_inj base).mp pc)).elim
        · omega
      rw [mj, ij] at cost
      exact .inr ⟨pc, x10, by omega,
        by simpa only [mmem, imem, mdata, idata] using value,
        by simpa only [mmem, imem, mdata, idata] using order⟩


/-- Scan indices count the slots after the pivot at element zero. -/
def partitionWord (m : Memory) (data : BitVec 64) (i : Nat) : BitVec 64 :=
  m.read64 (wordAddr data (i + 1))

/-- The exchange between two scans writes the two original values. -/
def partitionSwap (m : Memory) (data : BitVec 64) (i j : Nat) : Memory :=
  (m.write64 (wordAddr data (i + 1)) (partitionWord m data j)).write64
    (wordAddr data (j + 1)) (partitionWord m data i)

/-- Array effects of the linked partition scan. The right scan decrements
    before testing its word. Its last examined index is therefore retained
    as the exchange position if the comparison fails. -/
inductive PartitionTrace (data : BitVec 64) : Memory → Nat → Nat → Memory → Nat → Nat → Prop where
  | crossed {m i j} (crossed : j ≤ i) (overlap : i ≤ j + 1) :
      PartitionTrace data m i j m i j
  | finish {m i j k}
      (leftBound : i ≤ k) (rightBound : k ≤ j)
      (leftStrict : ∀ x, i ≤ x → x < k →
        (partitionWord m data x).toInt < (m.read64 data).toInt)
      (rightStrict : ∀ x, k ≤ x → x < j →
        (m.read64 data).toInt < (partitionWord m data x).toInt) :
      PartitionTrace data m i j m k k
  | exchange {m i j l r out fi fj}
      (leftBound : i ≤ l) (ordered : l ≤ r) (rightBound : r < j)
      (leftStrict : ∀ x, i ≤ x → x < l →
        (partitionWord m data x).toInt < (m.read64 data).toInt)
      (rightStrict : ∀ x, r < x → x < j →
        (m.read64 data).toInt < (partitionWord m data x).toInt)
      (leftStop : (m.read64 data).toInt ≤ (partitionWord m data l).toInt)
      (rightStop : (partitionWord m data r).toInt ≤ (m.read64 data).toInt)
      (tail : PartitionTrace data (partitionSwap m data l r) (l + 1) r out fi fj) :
      PartitionTrace data m i j out fi fj

/-- All array words addressed by a partition are readable and writable. -/
def ScanBuffer (s : State) : Prop :=
  ∀ k : BitVec 64, k.toNat ≤ (s.readReg64 (.gpr 8#5)).toNat →
    let addr := s.readReg64 (.gpr 20#5) + (k <<< 3)
    s.mem.canRead addr 8 = true ∧ s.mem.canWrite addr 8 = true

/-- The machine's complete scan-and-exchange loop reaches the final pivot
    exchange. The bound charges each scan probe and swap to cursor movement.
    The cost excludes the pivot exchanges before and after this loop. -/
theorem partition_scan_loop (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x258#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (openInterval : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 9#5)).toNat)
    (bounded : (s.readReg64 (.gpr 9#5)).toNat ≤ (s.readReg64 (.gpr 8#5)).toNat)
    (restBase : s.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 20#5) + 8#64)
    (buffer : ScanBuffer s) :
    ∃ count final, CodeStepsN (program base) count s final ∧
      final.pc = base + 0x2d8#64 ∧ final.status = .Running ∧ final.sp = s.sp ∧
      (program base).CodeLoaded final.mem ∧ ScanBuffer final ∧
      final.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      final.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      (final.readReg64 .x1).toNat ≤ (s.readReg64 (.gpr 8#5)).toNat ∧
      count ≤ 24 * ((s.readReg64 (.gpr 9#5)).toNat - (s.readReg64 .x1).toNat) + 12 ∧
      (s.readReg64 (.gpr 9#5)).toNat - (s.readReg64 .x1).toNat ≤ count ∧
      PartitionRegs s final ∧
      PartitionTrace (s.readReg64 (.gpr 20#5)) s.mem
        (s.readReg64 .x1).toNat (s.readReg64 (.gpr 9#5)).toNat final.mem
        (final.readReg64 .x1).toNat (final.readReg64 (.gpr 9#5)).toNat := by
  generalize hd : (s.readReg64 (.gpr 9#5)).toNat - (s.readReg64 .x1).toNat = d
  induction d using Nat.strongRecOn generalizing s with
  | ind d ih =>
    obtain ⟨c, mid, steps, mrun, mmem, msp, mregs, m8, mbase, mrest, ilo, ordered, jhi, cost, lower, lstrict, lend, rstrict, exit⟩ :=
      partition_scan_pair base s pc running loaded openInterval bounded (fun k fit => (buffer k fit).1)
    have mloaded : (program base).CodeLoaded mid.mem := mmem.symm ▸ loaded
    rcases exit with ⟨mpc, meet⟩ | ⟨mpc, m10, jstrict, value, valOrder⟩
    · have bufferMid : ScanBuffer mid := by
        intro k fit
        rw [m8] at fit
        simpa only [mmem, mbase] using buffer k fit
      refine ⟨c, mid, steps, mpc, mrun, msp, mloaded, bufferMid, m8, mbase,
        by omega, by omega, by omega, mregs, ?_⟩
      rw [mmem, meet]
      exact .finish (meet ▸ ilo) jhi (meet ▸ lstrict) (fun k lo hi => rstrict k lo hi (.inl mpc))
    · let l := mid.readReg64 .x1
      let r := mid.readReg64 (.gpr 9#5)
      let left := mid.readReg64 (.gpr 20#5) + ((l + 1#64) <<< 3)
      let right := mid.readReg64 (.gpr 20#5) + ((r + 1#64) <<< 3)
      have lbound : (l + 1#64).toNat ≤ (s.readReg64 (.gpr 8#5)).toNat := by
        have fit := (s.readReg64 (.gpr 8#5)).isLt
        change l.toNat ≤ r.toNat at ordered
        change r.toNat < _ at jstrict
        rw [BitVec.toNat_add]
        change (l.toNat + 1) % 2^64 ≤ _
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have rbound : (r + 1#64).toNat ≤ (s.readReg64 (.gpr 8#5)).toNat := by
        have fit := (s.readReg64 (.gpr 8#5)).isLt
        change r.toNat < _ at jstrict
        rw [BitVec.toNat_add]
        change (r.toNat + 1) % 2^64 ≤ _
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have leftAddr : left = mid.readReg64 (.gpr 23) + (mid.readReg64 .x1 <<< 3) := by
        change _ = mid.readReg64 (.gpr 23#5) + (l <<< 3)
        have mrestBase : mid.readReg64 (.gpr 23#5) = mid.readReg64 (.gpr 20#5) + 8#64 := by
          rw [mrest, restBase, mbase]
        dsimp [left]
        rw [mrestBase, BitVec.shiftLeft_add_distrib, BitVec.add_assoc, BitVec.add_comm 8#64]
        rfl
      have rightAddr : right = mid.readReg64 (.gpr 20) + (mid.readReg64 (.gpr 10) <<< 3) + 8#64 := by
        change _ = mid.readReg64 (.gpr 20#5) + (mid.readReg64 (.gpr 10#5) <<< 3) + 8#64
        dsimp [right, r]
        rw [m10, BitVec.shiftLeft_add_distrib, BitVec.add_assoc]
        rfl
      have readLeft : mid.mem.canRead left 8 = true := by
        simpa only [left, mmem, mbase] using (buffer (l + 1#64) lbound).1
      have writeLeft : mid.mem.canWrite left 8 = true := by
        simpa only [left, mmem, mbase] using (buffer (l + 1#64) lbound).2
      have writeRight : mid.mem.canWrite right 8 = true := by
        simpa only [right, mmem, mbase] using (buffer (r + 1#64) rbound).2
      have rightValue : mid.readReg64 (.gpr 11#5) = mid.mem.read64 right := by
        change mid.readReg64 (.gpr 11#5) = _
        simpa only [right, r, mmem, mbase] using value
      obtain ⟨swapCount, next, swapSteps, nrun, nsp, nregs, nloaded, nmem, ni, nj, _, n8, nbase, nrest, resume⟩ :=
        quickselect_swap base mid left right mpc mrun mloaded leftAddr rightAddr readLeft
          writeLeft writeRight rightValue
      change next.readReg64 (.gpr 9#5) = mid.readReg64 (.gpr 10#5) at nj
      rw [m10] at nj
      have niNat : (next.readReg64 .x1).toNat = (mid.readReg64 .x1).toNat + 1 := by
        rw [ni, BitVec.toNat_add]
        change (l.toNat + 1) % 2^64 = l.toNat + 1
        have fit := (s.readReg64 (.gpr 8#5)).isLt
        change l.toNat ≤ r.toNat at ordered
        change r.toNat < _ at jstrict
        exact Nat.mod_eq_of_lt (by omega)
      have leftWordAddr : left = wordAddr (s.readReg64 (.gpr 20#5)) (l.toNat + 1) := by
        rw [wordAddr_succ_shift, ← mbase]
        simp [left, BitVec.shiftLeft_add_distrib]
      have rightWordAddr : right = wordAddr (s.readReg64 (.gpr 20#5)) (r.toNat + 1) := by
        rw [wordAddr_succ_shift, ← mbase]
        simp [right, BitVec.shiftLeft_add_distrib]
      have swapMem : next.mem = partitionSwap s.mem (s.readReg64 (.gpr 20#5)) l.toNat r.toNat := by
        rw [nmem, leftWordAddr, rightWordAddr, mmem]
        rfl
      have rightStop : (partitionWord s.mem (s.readReg64 (.gpr 20#5)) r.toNat).toInt ≤
          (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt := by
        rw [rightValue, rightWordAddr, mmem] at valOrder
        exact valOrder
      have prepend {out : Memory} {fi fj : Nat}
          (tail : PartitionTrace (s.readReg64 (.gpr 20#5)) next.mem
            (next.readReg64 .x1).toNat (next.readReg64 (.gpr 9#5)).toNat out fi fj) :
          PartitionTrace (s.readReg64 (.gpr 20#5)) s.mem
            (s.readReg64 .x1).toNat (s.readReg64 (.gpr 9#5)).toNat out fi fj := by
        rw [swapMem, niNat, nj] at tail
        exact .exchange ilo ordered jstrict lstrict
          (fun k hlo hhi => rstrict k (Nat.le_of_lt hlo) hhi (.inr hlo))
          (lend (Nat.lt_of_le_of_lt ordered jstrict)) rightStop tail
      have toNext := steps.append swapSteps
      have n8' : next.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) := n8.trans m8
      have nbase' : next.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := nbase.trans mbase
      have nextBuffer : ScanBuffer next := by
        intro k fit
        rw [n8'] at fit
        dsimp only
        rw [nbase', nmem]
        have h := buffer k fit
        exact ⟨Memory.canRead_write64_of_canRead _ _
          (Memory.canRead_write64_of_canRead _ _ (mmem.symm ▸ h.1)), by
            rw [Memory.canWrite_congr (Memory.perm_write64 ..) _ _,
              Memory.canWrite_congr (Memory.perm_write64 ..) _ _, mmem]
            exact h.2⟩
      split at resume
      · rename_i crossed
        obtain ⟨rfl, npc⟩ := resume
        have ge := BitVec.ule_iff_toNat_le.mp crossed
        change (mid.readReg64 (.gpr 10#5)).toNat ≤ (mid.readReg64 .x1 + 1#64).toNat at ge
        rw [m10, ← ni, ← nj] at ge
        obtain ⟨final, stop, frun, fmem, fsp, fregs, fi, f8, fj, fbase, _, fpc⟩ :=
          partition_right_guard base next npc nrun nloaded
        rw [ite_eq_right (Nat.not_lt_of_ge ge)] at fpc
        have finalBuffer : ScanBuffer final := by
          intro k fit
          rw [f8] at fit
          simpa only [fmem, fbase] using nextBuffer k fit
        have close := ge
        rw [nj, niNat] at close
        refine ⟨c + 8 + 2, final, toNext.append stop, fpc, frun, fsp.trans (nsp.trans msp),
          fmem.symm ▸ nloaded, finalBuffer, f8.trans n8', fbase.trans nbase',
          by rw [fi, niNat]; omega, by omega, by omega, (mregs.trans nregs).trans fregs, ?_⟩
        rw [fmem, fi, fj]
        apply prepend
        refine .crossed ge ?_
        rw [niNat, nj]
        omega
      · rename_i notCrossed
        obtain ⟨rfl, npc⟩ := resume
        have lt : (next.readReg64 .x1).toNat < (next.readReg64 (.gpr 9#5)).toNat := by
          apply Nat.lt_of_not_ge
          intro ge
          apply notCrossed
          apply BitVec.ule_iff_toNat_le.mpr
          rw [show mid.readReg64 (.gpr 10) = mid.readReg64 (.gpr 10#5) from rfl, m10, ← ni, ← nj]
          exact ge
        have small : (next.readReg64 (.gpr 9#5)).toNat - (next.readReg64 .x1).toNat < d := by
          rw [nj, niNat]
          omega
        have nextBounded : (next.readReg64 (.gpr 9#5)).toNat ≤ (next.readReg64 (.gpr 8#5)).toNat := by
          rw [nj, show next.readReg64 (.gpr 8#5) = mid.readReg64 (.gpr 8#5) from n8, m8]
          omega
        have nextRest : next.readReg64 (.gpr 23#5) = next.readReg64 (.gpr 20#5) + 8#64 := by
          rw [show next.readReg64 (.gpr 23#5) = mid.readReg64 (.gpr 23#5) from nrest, mrest, restBase,
            show next.readReg64 (.gpr 20#5) = mid.readReg64 (.gpr 20#5) from nbase, mbase]
        obtain ⟨tail, final, rest, fpc, frun, fsp, floaded, fbuffer, f8, fbase, finRange, budget,
            tailLower, tailRegs, trace⟩ :=
          ih _ small next npc nrun nloaded lt nextBounded nextRest nextBuffer rfl
        refine ⟨c + 9 + tail, final, toNext.append rest, fpc, frun,
          fsp.trans (nsp.trans msp), floaded, fbuffer, f8.trans n8', fbase.trans nbase',
          by simpa only [n8'] using finRange, ?_, ?_, (mregs.trans nregs).trans tailRegs,
          prepend (nbase' ▸ trace)⟩
        · rw [nj, niNat] at budget
          omega
        · rw [nj, niNat] at tailLower
          omega

end Example04Rust
