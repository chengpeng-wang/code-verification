# Example 03 — C 快速排序的最坏指令数

## 先审阅证明目标

先读 [`quicksort_worst_case_quadratic`](QuicksortCost.lean) 中 `:= by` 之前的声明。对每个存在合法调用的正长度 `n`，它证明两件事。

| 要核对的量词 | 机器码保证 |
| --- | --- |
| **所有**合法的长度为 `n` 的调用 | 首次正常返回的指令数至多为 `43 * n²`。 |
| **存在**一个合法的长度为 `n` 的调用 | 首次正常返回的指令数至少为 `n²`。证明把一个合法状态中的数组改填为全相等的字节，并证明改填后的状态仍然合法。 |

合起来就是 64 位模型中可实现长度的最坏情况二次界。实际的统一上界是 `40 * n² + 3`，也覆盖 `n = 0`。`valid_calls_exist` 给出一套具体内存布局，证明每个 `0 ≤ n ≤ 2^56` 都确实存在合法调用。

**时间单位。** `ReturnsIn prog k initial final` 用 ARM64 库的 `StepsN` 表示恰好 `k` 步，从函数入口开始，计到本次调用的 `ret` 为止。定理排除了更早的正常返回。函数内部三条 `bl`、分区循环和两次递归执行都计入成本。每条指令记一单位，因此这里刻画的是机器指令数。实际耗时还取决于处理器和内存。

**调用前提。** `ValidCall` 要求实际链接字节装载在初始 `PC`，数组可读写，`X1` 等于长度，初始 `SP` 按 16 字节对齐，并提供 `48 * n` 字节的可写栈。初始 `LR` 位于提取的函数代码范围之外，用于确定此次调用结束的位置。数组、栈和调用者的 `frame` 通过分离逻辑组合。

[`quicksort_instruction_count`](QuicksortCost.lean) 同时证明执行会正常返回、原数组地址上的结果有序且保留元素的出现次数、调用约定和 `frame` 成立。复杂度定理用的是这次执行的步数。

## 从指令数得到递推式

复用 Example 02 的 [主函数](../example02-c/quicksort.c) 和 [分区函数](../example02-c/quicksort_partition.c)。主函数对长度 0 和 1 走直接返回路径，执行 3 条指令。

设某次调用的输入为 `A`，长度 `n ≥ 2`。分区得到左右子数组 `A_left` 和 `A_right`，它们的长度分别是 `L` 和 `R`，满足 `L + R = n - 1`。分区执行 8 条入口指令、4 条收尾指令。每个扫描元素花 6 条指令，移到左区的元素各多花 5 条。主函数这一层执行 22 条指令，再加上三个子调用的指令数。

```text
P(n, L) = 12 + 6 * (n - 1) + 5 * L
T(A)    = 22 + P(n, L) + T(A_left) + T(A_right)
```

任意分区满足 `L² + R² ≤ (n - 1)²`。由两个更短调用的归纳假设和分区的线性成本，得到统一上界。

全相等输入使每次分区都产生 `L = 0` 和 `R = n - 1`。于是精确成本满足下面的递推，并由归纳得出对正长度的闭式。

```text
E(0) = E(1) = 3
E(n) = E(n - 1) + 31 + 6 * n       n ≥ 2
E(n) = 3 * n² + 34 * n - 34        n ≥ 1
```

分区的精确计数在 [`QuicksortPartitionCost.lean`](QuicksortPartitionCost.lean)，两次递归调用的计数和上界归纳在 [`QuicksortDriverCost.lean`](QuicksortDriverCost.lean)，下界的合法入口状态在 [`QuicksortCostInput.lean`](QuicksortCostInput.lean)。[`CountedExecution.lean`](CountedExecution.lean) 的计数规则逐步构造 ARM64 的执行证据。

## 复查证明

在 `DeepMindDemo` 目录运行以下命令。

```bash
./playground/example03-c/check.sh
```

脚本先用 Example 02 的构建流程重新编译、链接和检查同一份 C 代码，再用 Lean 检查本例的计数定理。机器码和反汇编在 `example02-c/build/`，其字节仍由本例的定理核对。
