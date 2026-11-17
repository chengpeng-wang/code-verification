# Example 03 — Worst-Case Instruction Count of C Quicksort

## Review the Proof Goal

Read the statement of [`quicksort_worst_case_quadratic`](QuicksortCost.lean) before `:= by`. For every positive length `n` that admits a valid call, it proves both bounds below.

| Quantifier to check | Machine-code guarantee |
| --- | --- |
| **Every** valid call of length `n` | The first normal return takes at most `43 * n²` instructions. |
| **Some** valid call of length `n` | The first normal return takes at least `n²` instructions. The proof fills the array of a valid initial state with equal bytes and shows that the resulting state is still valid. |

Together these bounds give quadratic worst-case growth for feasible lengths in the 64-bit model. The proof establishes an upper bound of `40 * n² + 3`, which also covers `n = 0`. `valid_calls_exist` provides a concrete memory layout that admits a valid call for every `0 ≤ n ≤ 2^56`.

**Cost model.** `ReturnsIn prog k initial final` uses the ARM64 library's `StepsN` to count exactly `k` steps from function entry through the call's `ret`. The theorem rules out an earlier normal return. The three `bl` instructions in the function, the partition loop, and both recursive executions contribute to the cost. Each instruction counts as one step. Elapsed time also depends on the processor and memory.

**Call assumptions.** `ValidCall` requires the actual linked bytes to be loaded at the initial `PC`, the array to be readable and writable, and `X1` to hold its length. The initial `SP` is 16-byte aligned and has `48 * n` bytes of writable stack space below it. The initial `LR` lies outside the extracted function code and identifies where the call ends. Separation logic combines the array, the stack, and the caller's `frame`.

[`quicksort_instruction_count`](QuicksortCost.lean) also proves that execution returns normally, the result at the original array address is sorted and preserves multiplicities, and the calling convention and `frame` are preserved. The complexity theorem uses the step count of this execution.

## Deriving the Recurrence from Instruction Counts

This example reuses the [entry point](../example02-c/quicksort.c) and [partition function](../example02-c/quicksort_partition.c) from Example 02. For lengths 0 and 1, the entry point takes the immediate return path and executes 3 instructions.

Let `A` be the input to a call of length `n ≥ 2`. Partitioning yields two subarrays, `A_left` and `A_right`, of lengths `L` and `R` with `L + R = n - 1`. The partition function executes 8 instructions at entry and 4 at exit. It executes 6 instructions per scanned element and 5 more for each element moved to the left partition. The Quicksort function executes 22 instructions at this level, plus the instructions executed by the three calls it makes.

```text
P(n, L) = 12 + 6 * (n - 1) + 5 * L
T(A)    = 22 + P(n, L) + T(A_left) + T(A_right)
```

Every partition satisfies `L² + R² ≤ (n - 1)²`. Combine this inequality with the induction hypotheses for the two shorter calls and the linear cost of partitioning to obtain the upper bound.

On an all-equal input, every partition yields `L = 0` and `R = n - 1`. The exact cost follows the recurrence below, and induction gives the closed form for positive lengths.

```text
E(0) = E(1) = 3
E(n) = E(n - 1) + 31 + 6 * n       n ≥ 2
E(n) = 3 * n² + 34 * n - 34        n ≥ 1
```

[`QuicksortPartitionCost.lean`](QuicksortPartitionCost.lean) proves the exact partition count. [`QuicksortDriverCost.lean`](QuicksortDriverCost.lean) counts the two recursive calls and proves the upper bound by induction. [`QuicksortCostInput.lean`](QuicksortCostInput.lean) constructs the valid entry state for the lower bound. The counting rules in [`CountedExecution.lean`](CountedExecution.lean) build the evidence of ARM64 execution one transition at a time.

## Recheck the Proof

Run the following command from the repository root.

```bash
./playground/example03-c/check.sh
```

The script uses the Example 02 build to recompile, link, and check the same C code, then checks this example's counting theorems in Lean. The machine code and disassembly are in `example02-c/build/`. This example's theorems also check the machine-code bytes.
