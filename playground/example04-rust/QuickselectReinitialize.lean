import QuickselectSpec
import ProofLib

namespace Example04Rust

open Arm64 ProofLib

set_option autoImplicit false

/-- Replace the array of a feasible call with words of the same length, and
    request the last rank. The byte write uses exactly the owned array region,
    preserving the surrounding frame and the loaded executable. -/
theorem ValidCall.reinitialize {base : BitVec 64} {s : State} {frame : SepProp}
    {n k : Nat} (valid : ValidCall base s frame n k)
    (xs : List (BitVec 64)) (length : xs.length = n) :
    let initial := (s.setMem (s.mem.writeBytes (s.readReg64 .x0) (unpackL xs))).writeReg64
      .x2 (BitVec.ofNat 64 (n - 1))
    ValidCall base initial frame n (n - 1) ∧
      initial.mem ⊨ (initial.readReg64 .x0 ↦₆₄* xs) ∗ stackAt initial.sp stackBytes ∗ frame := by
  obtain ⟨bytes, oldLen, owned⟩ := valid.memory
  have newLen : (unpackL xs).length = 8 * n := by rw [unpackL_length, length]
  have newOwned := writeBytes_satisfies (oldLen.trans newLen.symm) owned
  have region := Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion_of_length
    (oldLen.trans newLen.symm))) owned
  have keeps := keepsFrozen_writeBytes_of_memRegion (unpackL xs)
    (by have := valid.rustSliceSize; omega) region
  dsimp only
  refine ⟨?_, ?_⟩
  · refine ⟨valid.atEntry, valid.running, valid.loaded.of_keepsFrozen keeps, ?_, ?_, ?_, ?_,
      by have := valid.rankInRange; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [arm64_norm, wp_norm] using valid.returnOutside
    · simpa only [arm64_norm, wp_norm] using valid.returnAligned
    · simpa only [State.spAligned, arm64_norm, wp_norm] using valid.stackAligned
    · simpa only [arm64_norm, wp_norm] using valid.stackNoWrap
    · exact valid.rustSliceSize
    · simpa only [arm64_norm, wp_norm] using valid.lengthReg
    · simp only [arm64_norm, wp_norm]
    · simpa only [arm64_norm, wp_norm] using valid.arrayAligned
    · simpa only [arm64_norm, wp_norm] using valid.arrayNoWrap
    · exact ⟨unpackL xs, newLen, by simpa only [arm64_norm, wp_norm] using newOwned⟩
  · simpa only [pointsToWords64_eq_pointsToBytes, arm64_norm, wp_norm] using newOwned

end Example04Rust
