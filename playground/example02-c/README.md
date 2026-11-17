# Example 02 — ARM64 Proof of C Quicksort

## Review the Proof Goal

Start with `quicksort_returns_sorted` in [`QuicksortBinary.lean`](QuicksortBinary.lean). Read the theorem statement before `:= by` and check its assumptions, the code it executes, and its guarantees.

| Review item | What to check in the main theorem |
| --- | --- |
| Code under verification | `Steps (program initial.pc) initial final` runs the actual ARM64 bytes compiled and linked from C. |
| Input and output | `input` describes the array at the initial `X0`, and `X1` supplies its length `n`. `output` reads `n` bytes from the original array address in the final memory. |
| Sorting correctness | `Spec.Sorts input output` requires the output to be in ascending order by unsigned byte value and to preserve the multiplicity of each input value. |
| Normal return | `Steps` and `Returned` guarantee a return to the initial `LR` in finitely many steps, with the machine still `.Running`. |
| Calling convention and memory | `CallingConventionPreserved` guarantees that `SP` is restored and callee-saved registers are preserved. In the final memory, the output occupies the original array address, the stack region is writable, and the caller's `frame` assertion still holds. |

[`QuicksortSpec.lean`](QuicksortSpec.lean) defines the sorting property.

```lean
def Sorts (input output : List (BitVec width)) : Prop :=
  output.Pairwise (· ≤ ·) ∧ output.Perm input
```

For input `[7, 2, 7]`, the output `[2, 7, 7]` satisfies both conditions. The output `[2, 2, 7]` is sorted and has different multiplicities. `quicksort_returns_sorted` establishes both conditions for the array the machine actually writes.

## Call Assumptions

- The initial machine state is `.Running`. `CodeLoaded` requires the full program to be loaded into executable memory starting at the initial `PC`, with a 4-byte-aligned entry point.
- The initial `X0` points to contiguous readable and writable memory containing `input`, and `X1` equals `input.length`. The theorem covers every input that satisfies the assumptions, including empty arrays and arrays with repeated values.
- The initial `SP` is 16-byte aligned and has `48 * n` bytes of writable stack space below it, with `48 * n ≤ 2^64`. This budget suffices because each call that takes the recursive branch uses 48 bytes. The region is writable again on return, and its bytes may be used for temporary storage during execution.
- Separating conjunction `∗` combines the array, stack, and caller's `frame`, requiring their writable regions to be disjoint.

## From C to the Machine-Code Proof

[`quicksort.c`](quicksort.c) defines the entry point `quicksort_u8(a, n)`, which returns immediately for lengths 0 and 1. [`quicksort_partition.c`](quicksort_partition.c) uses the first element as the pivot, placing smaller elements on the left and elements greater than or equal to the pivot on the right.

1. [`QuicksortPartition.lean`](QuicksortPartition.lean) proves that the actual partition instructions return in finitely many steps. The array remains a permutation of the input, the returned `X0` contains the pivot index, and the two partitions satisfy their comparison conditions.
2. [`QuicksortMachine.lean`](QuicksortMachine.lean) uses induction on the array length to verify the two recursive calls, each on a shorter subarray. It combines the subarrays written by those calls with the pivot to show that the full array satisfies `Sorts`.
3. [`QuicksortBinary.lean`](QuicksortBinary.lean) checks that both instruction sequences match the 184 linked bytes, then derives a theorem about actual execution and memory readback from the machine-code contract.

If another example specifies that the program must produce the same output as a reference implementation, also locate the theorem showing that the reference implementation satisfies the intended property. The two proofs together establish the property for the program under verification.

## Recheck the Proof

Run the following command from the repository root.

```bash
./playground/example02-c/check.sh
```

The script requires Clang, `llvm-objcopy`, `llvm-objdump`, Lean/Lake, and an `ld.lld` that supports AArch64. If `ld.lld` is unavailable, the script tries `rust-lld` from the local stable Rust toolchain. This example was developed with Clang 18.1.3 targeting ARMv8-A at `-O1`.

The script recompiles and links the program, resolves the `bl` targets for the partition call and the two recursive calls, and checks the bytes before running Lean. It writes the disassembly to `build/quicksort_u8.asm`, the linked ELF to `build/quicksort_u8.elf`, and the raw `.text` bytes that Lean reads to `build/quicksort_u8.bin`. If changes to the C source or compiler flags change the machine code, the length or instruction-word check reports the mismatch.
