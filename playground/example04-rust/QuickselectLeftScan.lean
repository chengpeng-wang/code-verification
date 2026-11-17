import QuickselectBounds
import QuickselectArray

namespace Example04Rust

open Arm64 ProofLib Example03C

set_option autoImplicit false

private theorem left_finish (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x288#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem) :
    ∃ final, CodeStepsN (program base) 1 s final ∧ final.pc = base + 0x28c#64 ∧
      final.status = .Running ∧ final.mem = s.mem ∧ final.sp = s.sp ∧ PartitionRegs s final ∧
      final.readReg64 .x1 = s.readReg64 (.gpr 9#5) ∧
      final.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) ∧
      final.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      final.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      final.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
  let copy : Instr := .logicalShift .W64 .ORR .x1 .xzr (.gpr 9#5) .LSL 0
  let final := (program base).evalInst copy s
  refine ⟨final, linked_step pc (by decide +kernel) (execute_at base _ copy s pc running loaded (by decide +kernel))
    (.refl _), ?_⟩
  simp [final, copy, pc, running, wp_norm, arm64_norm, BitVec.add_assoc,
    PartitionRegs, CalleeSavedPreserved]

/-- The left-scan loop beginning at the comparison against its array limit.
    X1 is the left cursor, X9 is the right cursor and X10 is the limit.
    Each iteration that advances X1 costs 10 instructions. A final
    non-advancing probe costs seven, or one instruction closes the gap
    after the last advance. In either case the budget is `10*(j-i)+1`. -/
theorem partition_left_scan (base : BitVec 64) (s : State)
    (pc : s.pc = base + 0x260#64) (running : s.status = .Running)
    (loaded : (program base).CodeLoaded s.mem)
    (cursors : (s.readReg64 .x1).toNat < (s.readReg64 (.gpr 9#5)).toNat)
    (limit : (s.readReg64 (.gpr 9#5)).toNat ≤ (s.readReg64 (.gpr 10#5)).toNat)
    (pivotReadable : s.mem.canRead (s.readReg64 (.gpr 20#5)) 8 = true)
    (readable : ∀ i : BitVec 64, i.toNat < (s.readReg64 (.gpr 10#5)).toNat →
      s.mem.canRead (s.readReg64 (.gpr 20#5) + ((i <<< 3) + 8#64)) 8 = true) :
    ∃ count final, CodeStepsN (program base) count s final ∧
      final.pc = base + 0x28c#64 ∧ final.status = .Running ∧ final.mem = s.mem ∧ final.sp = s.sp ∧ PartitionRegs s final ∧
      final.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) ∧
      final.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      final.readReg64 (.gpr 8#5) = s.readReg64 (.gpr 8#5) ∧
      final.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      (s.readReg64 .x1).toNat ≤ (final.readReg64 .x1).toNat ∧
      (final.readReg64 .x1).toNat ≤ (s.readReg64 (.gpr 9#5)).toNat ∧
      count ≤ 10 * ((s.readReg64 (.gpr 9#5)).toNat - (s.readReg64 .x1).toNat) + 1 ∧
      count ≤ 10 * ((final.readReg64 .x1).toNat - (s.readReg64 .x1).toNat) + 7 ∧
      (final.readReg64 .x1).toNat - (s.readReg64 .x1).toNat ≤ count ∧
      (∀ k, (s.readReg64 .x1).toNat ≤ k → k < (final.readReg64 .x1).toNat →
        (s.mem.read64 (wordAddr (s.readReg64 (.gpr 20#5)) (k + 1))).toInt <
          (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt) ∧
      ((final.readReg64 .x1).toNat < (s.readReg64 (.gpr 9#5)).toNat →
        (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt ≤
          (s.mem.read64 (wordAddr (s.readReg64 (.gpr 20#5)) ((final.readReg64 .x1).toNat + 1))).toInt) := by
  let d := (s.readReg64 (.gpr 9#5)).toNat - (s.readReg64 .x1).toNat
  generalize hd : d = dist
  induction dist using Nat.strongRecOn generalizing s with
  | ind dist ih =>
    have hlt : (s.readReg64 (.gpr 1#5)).toNat < (s.readReg64 (.gpr 10#5)).toNat :=
      Nat.lt_of_lt_of_le cursors limit
    obtain ⟨probe, steps, prun, pmem, psp, preg, pi, p8, pj, pdata, p10, p23, ppc⟩ :=
      partition_left_probe base s pc running loaded hlt pivotReadable (readable _ hlt)
    change probe.readReg64 .x1 = s.readReg64 .x1 at pi
    split at ppc
    · rename_i below
      obtain ⟨next, adv, nrun, nmem, nsp, nreg, ni, nj, n10, ndata, n8, n23, npc⟩ :=
        partition_left_advance base probe ppc prun (pmem.symm ▸ loaded)
      have nmem' := nmem.trans pmem
      have nj' : next.readReg64 (.gpr 9#5) = s.readReg64 (.gpr 9#5) := nj.trans pj
      have n10' : next.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := n10.trans p10
      have ndata' : next.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := ndata.trans pdata
      have ni' := ni.trans (congrArg (· + 1#64) pi)
      have niNat : (next.readReg64 .x1).toNat = (s.readReg64 .x1).toNat + 1 := by
        rw [ni', BitVec.toNat_add]
        change ((s.readReg64 .x1).toNat + 1) % 2^64 = _
        have bound := (s.readReg64 (.gpr 9#5)).isLt
        exact Nat.mod_eq_of_lt (by omega)
      have advance := steps.append adv
      have startStrict :
          (s.mem.read64 (wordAddr (s.readReg64 (.gpr 20#5)) ((s.readReg64 .x1).toNat + 1))).toInt <
            (s.mem.read64 (s.readReg64 (.gpr 20#5))).toInt := by
        simpa only [wordAddr_succ_shift] using below
      split at npc
      · rename_i closed
        obtain ⟨final, finish, fpc, frun, fmem, fsp, freg, fi, fj, fdata, f8, f23⟩ :=
          left_finish base next npc nrun (nmem'.symm ▸ loaded)
        have finalLeft : (final.readReg64 .x1).toNat = (s.readReg64 .x1).toNat + 1 := by
          have eq : next.readReg64 (.gpr 9#5) = next.readReg64 .x1 := nj.trans (closed.trans ni.symm)
          rw [fi, eq, niNat]
        refine ⟨11, final, advance.append finish, fpc, frun, fmem.trans nmem',
          fsp.trans (nsp.trans psp), (preg.trans nreg).trans freg, fj.trans nj', fdata.trans ndata',
          f8.trans (n8.trans p8), f23.trans (n23.trans p23), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [fi, nj']
          exact Nat.le_of_lt cursors
        · simp [fi, nj']
        · omega
        · rw [fi, nj']
          omega
        · omega
        · intro k hk hlt
          have eq : k = (s.readReg64 .x1).toNat := by omega
          simpa only [eq] using startStrict
        · rw [fi, nj']
          omega
      · rename_i notClosed
        have stillOpen : (next.readReg64 .x1).toNat < (next.readReg64 (.gpr 9#5)).toNat := by
          rw [niNat, nj']
          have hne : (s.readReg64 .x1).toNat + 1 ≠ (s.readReg64 (.gpr 9#5)).toNat := by
            intro eq
            apply notClosed
            apply BitVec.eq_of_toNat_eq
            have heq : next.readReg64 (.gpr 9#5) = next.readReg64 .x1 :=
              BitVec.eq_of_toNat_eq (by rw [nj', niNat, eq])
            rw [← nj, ← ni]
            exact congrArg BitVec.toNat heq
          omega
        have ndist : (next.readReg64 (.gpr 9#5)).toNat - (next.readReg64 .x1).toNat < dist := by
          dsimp [d] at hd
          rw [niNat, nj']
          omega
        have nlimit : (next.readReg64 (.gpr 9#5)).toNat ≤ (next.readReg64 (.gpr 10#5)).toNat := by
          rwa [nj', n10']
        have npivot : next.mem.canRead (next.readReg64 (.gpr 20#5)) 8 = true := by
          rwa [nmem', ndata']
        have nreadable : ∀ i : BitVec 64, i.toNat < (next.readReg64 (.gpr 10#5)).toNat →
            next.mem.canRead (next.readReg64 (.gpr 20#5) + ((i <<< 3) + 8#64)) 8 = true := by
          simpa only [nmem', ndata', n10'] using readable
        obtain ⟨count, final, rest, fpc, frun, fmem, fsp, freg, fj, fdata, f8, f23, flo, fhi, budget, charged, lower, strict, endpoint⟩ :=
          ih _ ndist next npc nrun (nmem'.symm ▸ loaded) stillOpen nlimit npivot nreadable rfl
        refine ⟨10 + count, final, advance.append rest, fpc, frun, fmem.trans nmem',
          fsp.trans (nsp.trans psp), (preg.trans nreg).trans freg, fj.trans nj', fdata.trans ndata',
          f8.trans (n8.trans p8), f23.trans (n23.trans p23), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · rwa [nj'] at fhi
        · rw [niNat, nj'] at budget
          omega
        · rw [niNat] at charged
          omega
        · omega
        · intro k hk hlt
          by_cases eq : k = (s.readReg64 .x1).toNat
          · simpa only [eq] using startStrict
          · simpa only [nmem', ndata'] using strict k (by omega) hlt
        · intro hlt
          simpa only [nmem', ndata'] using endpoint (by simpa only [nj'] using hlt)
    · rename_i notBelow
      refine ⟨7, probe, steps, ppc, prun, pmem, psp, preg, pj, pdata, p8, p23,
        by simp [pi], by rw [pi]; exact Nat.le_of_lt cursors, by omega, by omega, by simp [pi],
        ?_, ?_⟩
      · intro k hle hlt
        rw [pi] at hlt
        omega
      · intro _
        rw [pi, wordAddr_succ_shift]
        exact Int.not_lt.mp notBelow

end Example04Rust
