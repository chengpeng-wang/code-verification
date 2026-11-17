# Example 04 · Rust Hoare Quickselect

## Review the Proof Goal

The main theorem, [`quickselect_worst_case`](QuickselectWorstCase.lean), gives matching upper and lower bounds for actual ARM64 execution. Let `r = 2^⌊log₉ n⌋`. Every valid call returns normally within `floor(960 * n² / r)` instructions. For each feasible length `n ≥ 9`, there is an input whose first normal return takes `count` instructions with `n² ≤ 2 * count * r`. The bounds give a worst-case growth rate of `Θ(n^(2−log₉ 2))`, with upper and lower constants of 960 and 1/2.

[`QuickselectSpec.lean`](QuickselectSpec.lean) defines the call assumptions and return guarantees. The call state supplies the code address, array address, stack pointer, and return address. The sample runs use fixed addresses for reproducibility.

| Lean definition | What to review |
| --- | --- |
| `ValidCall` | `X0` points to a readable, writable, aligned `i64` array whose address range does not wrap. `X1 = n` and `X2 = k < n`. The array occupies fewer than `2^63` bytes. Separation logic requires the array, stack, and caller's reserved memory to be disjoint. |
| `FirstReturn` | Every ARM64 instruction from entry to the first visit to the caller's address counts as one step, including the final `RET`. On return, the processor is still running and the stack pointer is restored. |
| `WorstCaseUpper` | Every valid call has a first normal return within the instruction budget. |
| `WorstCaseLower` | For each feasible length of at least 9, some input and target rank attain the lower bound at the first normal return. |
| `Selects` | Specifies the property of the selected position. The output is a permutation of the input. Under signed comparison, values to the left of the target position are at most the selected value, and values to the right are at least the selected value. |

## Rust Adaptation

[`quickselect.rs`](quickselect.rs) comes from `PV-playground/src/experiments/EXP-006-complexity/source/original.rs` in the same workspace. It uses the Hoare variant with signed `i64` values and `<` comparisons. It retains the original pivot sample positions, median-of-three selection, scans from both ends, swap order, and search interval updates.

The Rust code uses explicit `Option` checks for slice indexing, swaps, and splitting. For a valid call, the sample blocks lie in the active slice, cursor bounds are checked before partition reads and writes, and each round keeps the target rank in the next active range. These checks add constant work per operation while preserving the number of comparisons and swaps and the sequence of active ranges. The asymptotic complexity therefore stays the same. Differential testing covered 84,444 calls and compared the entire array after in-place selection along with the selected element. The exported function's safety contract specifies the requirements on the input slice and target rank. An out-of-range rank may cause an early return.

## Connecting the Proof to the Machine Code

1. [`QuickselectMachine.lean`](QuickselectMachine.lean) embeds the 804 bytes of the linked `.text` section directly and pins the byte sequence with SHA-256. [`QuickselectSanity.lean`](QuickselectSanity.lean) checks decoding and static control flow for all 201 instructions and runs five sample cases under the ARM64 semantics.
2. [`QuickselectPivotMachine.lean`](QuickselectPivotMachine.lean) verifies recursive pivot selection in the binary. Each recursive call accounts for its own instructions and preserves the calling convention and memory outside its stack frame. [`QuickselectPivot.lean`](QuickselectPivot.lean) turns the selected pivot into rank bounds on both sides.
3. [`QuickselectPartitionScan.lean`](QuickselectPartitionScan.lean) and [`QuickselectPartitionInvariant.lean`](QuickselectPartitionInvariant.lean) verify the scans and swaps and bound the number of scan steps. They count duplicate values to prove that partitioning shortens the active range for the next round.
4. [`QuickselectRounds.lean`](QuickselectRounds.lean) combines pivot selection, partitioning, range updates, and return into rounds of machine execution. [`QuickselectUpper.lean`](QuickselectUpper.lean) proves by induction on the active range length that every valid call returns, then uses the potential recurrence in [`QuickselectCost.lean`](QuickselectCost.lean) to derive the total upper bound.
5. [`QuickselectAdversary.lean`](QuickselectAdversary.lean) constructs the input backward, round by round, so that each pivot eliminates exactly `r` elements and the retained suffix feeds into the construction for the next round. [`QuickselectAdversaryMachine.lean`](QuickselectAdversaryMachine.lean) relates the actual scans to this partition relation. [`QuickselectLower.lean`](QuickselectLower.lean) places the constructed array in any feasible layout and uses the counted execution trace of the same binary to prove the lower bound.

## Reproduce the Results

Run the following command from the repository root. The example has been reproduced on x86-64 Linux. It requires Rust 1.98.1, the `aarch64-unknown-linux-gnu` target, LLVM binary tools, and the Lean/Lake version pinned in the repository.

```bash
./playground/example04-rust/check.sh
```

Pass `--sanity-only` to cross-compile, check the machine code, and run the sample cases. The script writes the linked ELF to `build/quickselect.elf`, the disassembly to `build/quickselect.asm`, and the raw `.text` bytes that Lean reads to `build/quickselect.bin`.
