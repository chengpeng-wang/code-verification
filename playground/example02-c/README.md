# Example 02 — C 快速排序的 ARM64 证明

## 先审阅证明目标

从 [`QuicksortBinary.lean`](QuicksortBinary.lean) 的 `quicksort_returns_sorted` 开始。先看 `:= by` 前面的定理声明，核对它的前提、执行对象和保证是否符合你想验证的性质。

| 审阅项 | 在主定理中核对什么 |
| --- | --- |
| 验证对象 | `Steps (program initial.pc) initial final` 使用从 C 编译、链接出的实际 ARM64 字节。 |
| 输入与输出 | `input` 描述初始 `X0` 指向的数组，`X1` 提供长度 `n`。`output` 从最终内存的原数组地址读回 `n` 个字节。 |
| 排序正确性 | `Spec.Sorts input output` 同时要求输出按无符号字节值升序排列，并保留输入中每个值的出现次数。 |
| 正常返回 | `Steps` 和 `Returned` 一起保证有限步内返回到初始 `LR`，机器状态为 `.Running`。 |
| 调用约定与内存 | `CallingConventionPreserved` 保证恢复 `SP` 和被调用者保存的寄存器。最终内存满足原地址存有输出、栈区域可用以及调用者的 `frame` 断言。 |

排序性质写在 [`QuicksortSpec.lean`](QuicksortSpec.lean) 中。

```lean
def Sorts (input output : List (BitVec width)) : Prop :=
  output.Pairwise (· ≤ ·) ∧ output.Perm input
```

例如 `[7, 2, 7]` 排成 `[2, 7, 7]` 同时满足两项。`[2, 2, 7]` 满足升序要求，但改变了值的出现次数。`quicksort_returns_sorted` 对机器实际写出的数组直接证明这两项。

## 调用前提

- 初始机器状态为 `.Running`。`CodeLoaded` 要求代码从初始 `PC` 起完整装载在可执行内存中，入口按 4 字节对齐。
- 初始 `X0` 指向存有 `input` 的连续可读写内存，`X1` 等于 `input.length`。定理量化任意满足这些前提的输入，包括空数组和含重复值的数组。
- 初始 `SP` 按 16 字节对齐，且其下方有 `48 * n` 字节的可写栈空间，满足 `48 * n ≤ 2^64`。这是证明采用的充分预算，每次进入递归分支的调用使用 48 字节。调用结束时归还该可写区域，执行期间栈内字节可以用作临时存储。
- 数组、栈和调用者的 `frame` 通过 `∗` 组合，要求它们占用的可写内存彼此分离。

## 从 C 到机器码证明

[`quicksort.c`](quicksort.c) 的入口是 `quicksort_u8(a, n)`。长度为 0 或 1 时直接返回。[`quicksort_partition.c`](quicksort_partition.c) 取首元素作枢轴，将小于它的元素分到左边，大于或等于它的元素分到右边。

1. [`QuicksortPartition.lean`](QuicksortPartition.lean) 证明实际分区指令有限步内返回，数组仍是输入的一个排列，返回的 `X0` 是枢轴索引，且左右两段满足各自的比较条件。
2. [`QuicksortMachine.lean`](QuicksortMachine.lean) 用长度归纳验证两次递归调用。两个子数组都更短。证明用这两次调用写回的左右段和枢轴，直接推出整个数组满足 `Sorts`。
3. [`QuicksortBinary.lean`](QuicksortBinary.lean) 核对这两段指令与链接出的 184 个字节相符，再把机器码契约展开为对实际执行及内存读回的定理。

如果别的例子采用「程序输出等于参考实现输出」的规格，审阅时还要找参考实现满足目标性质的定理。两份证据合起来才能把性质传给被验证的程序。

## 复查证明

在 `DeepMindDemo` 目录运行以下命令。

```bash
./playground/example02-c/check.sh
```

需要 Clang、`llvm-objcopy`、`llvm-objdump`、Lean/Lake 和支持 AArch64 的 `ld.lld`。找不到 `ld.lld` 时，脚本尝试使用本机 Rust stable 工具链中的 `rust-lld`。本例使用 Clang 18.1.3 的 ARMv8-A、`-O1` 产物开发。

脚本重新编译和链接，解析一次分区调用和两次递归调用的 `bl` 目标，核对字节后运行 Lean。生成的 `build/quicksort_u8.asm` 是反汇编，`build/quicksort_u8.elf` 是链接产物，`build/quicksort_u8.bin` 是 Lean 读取的 `.text` 原始字节。修改 C 或编译选项改变了机器码时，脚本会在长度或指令字核对时指出差异。
