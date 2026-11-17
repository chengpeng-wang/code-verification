# AlphaProof Code Playground

When adding a verification example, document the property being proved next to the specification and main theorem. In the example's README, list the main theorem, its input assumptions, the program's actual output, and the guarantees to review. When submitting proof results, point reviewers to these locations so they can check the goal before reading the proof.

## Example 1 — C

Use the ARM64 machine semantics to prove that the function compiled from [`store_byte.c`](example01-c/store_byte.c) writes its `value` argument to `*dst`, preserves the adjacent byte, and returns to the caller.

Run the following command from the repository root. It requires Clang, `llvm-objcopy`, `llvm-objdump`, and the Lean/Lake version pinned in `lean-toolchain`. The example was cross-compiled on x86-64 Linux.

```bash
./playground/example01-c/check.sh
```

The script recompiles the C source and checks the Lean proof on every run. On the first run, Lake builds the required local ARM64 library.

```text
store_byte.c ── Clang ──▶ AArch64 ELF object file (.o)
                                  │ Extract .text.store_byte
                                  ▼
                         8 bytes of machine code
                                  │ Lean's include_bytes%
                                  ▼
                 Load executable memory, then fetch and execute at PC
                                  │ Arm64.Step + Arm64.Steps
                                  ▼
                 Verify the target byte, adjacent byte, and return address
```

1. [`check.sh`](example01-c/check.sh) uses `clang --target=aarch64-linux-gnu -O2 -c` to compile the function into its own `.text.store_byte` section. `llvm-objcopy` extracts the section bytes, which encode `strb w1, [x0]` and `ret`.
2. [`Example01C.lean`](example01-c/Example01C.lean) reads the extracted bytes and loads them with the library's `loadCodeMem` function. In the initial machine state, `X0` holds the destination pointer, the low byte of `X1` holds the value to write, and `LR` holds the return address. The example fixes the code, data, and return addresses. The theorem quantifies over the original destination byte, the value to write, and the adjacent byte.
3. `store_byte_correct` constructs two `Arm64.Step` transitions and combines them with `Arm64.Steps`. The model must successfully fetch each instruction from memory. In the fetch proofs, Lean checks through `change` that the fetch is independent of the data bytes, so it can compute the fetch with concrete values while the theorem covers arbitrary input bytes. The final state has `value` at the destination, the original value at the adjacent byte, the return address in `PC`, and processor status `.Running`.

On success, the final output shows that `Example01C.store_byte_correct` depends only on Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

To see the proof catch a change in the program, temporarily replace `*dst = value` with `*dst = 0` and rerun the script. The compiler changes the store instruction, and Lean fails at the first instruction-fetch proof. Restore the original assignment to pass the check again.

## Example 02 — C Quicksort

The proof shows that the ARM64 binary for `quicksort_u8(a, n)` returns normally and writes a sorted permutation of the input back to the original array. Start with `output` and `Spec.Sorts input output` in the main theorem. The example README lists the call assumptions, return guarantees, and roles of the proof files. [Example 02 proof goal](example02-c/README.md#review-the-proof-goal)

Run the following command from the repository root.

```bash
./playground/example02-c/check.sh
```

## Example 03 — Worst-Case Complexity of C Quicksort

The proof gives a quadratic worst-case bound on the number of instructions through the first return for the same Quicksort ARM64 binary. Review the upper bound for every valid call and the lower bound attained on an all-equal input. [Example 03 proof goal](example03-c/README.md#review-the-proof-goal)

```bash
./playground/example03-c/check.sh
```

## Example 04 — Rust Hoare Quickselect

The original Hoare Quickselect is adapted to Rust code that can be linked and run under the ARM64 model. The proof establishes matching upper and lower bounds on the order of growth of the binary's worst-case instruction count. [Example 04 proof goal](example04-rust/README.md#review-the-proof-goal)

```bash
./playground/example04-rust/check.sh
```
