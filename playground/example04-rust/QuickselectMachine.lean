import Arm64.Trusted.ISA.Semantics
import Arm64.Trusted.Surface.FileBytes

open Arm64 Arm64.Process

namespace Example04Rust

def codeSize : Nat := 804
def entryOffset : Nat := 0x1ac

/-- Linked `.text`, including `pseudo_median3` at offset zero and the exported entry at
    `entryOffset`. `check.sh` regenerates this file from the Rust source. -/
def codeBytes : List (BitVec 8) :=
  file_bytes% "build/quickselect.bin" sha256
    "f198f37314c19a1ad2f9c03e535e8e6b53f74d19e74c26f13b398835f9d12486"

/-- The linked relative branch offsets also work when the whole image is moved together. -/
def program (base : BitVec 64) : Program :=
  { base := base, code := codeBytes }

def entry (base : BitVec 64) : BitVec 64 := base + BitVec.ofNat 64 entryOffset

end Example04Rust
