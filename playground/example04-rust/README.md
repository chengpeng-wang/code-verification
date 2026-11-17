# Example 04 · Rust Hoare Quickselect

## 先审阅证明目标

主定理 [`quickselect_worst_case`](QuickselectWorstCase.lean) 同时给出实际 ARM64 执行的上界和同阶下界。令 `r = 2^⌊log₉ n⌋`。对每个合法调用，函数在至多 `floor(960 * n² / r)` 条指令后正常返回。对每个可合法调用且至少为 9 的长度 `n`，存在一个输入，其首次正常返回的指令数 `count` 满足 `n² ≤ 2 * count * r`。两条不等式给出的最坏阶是 `Θ(n^(2−log₉ 2))`，常数 960 和 1/2 是本证明采用的界。

[QuickselectSpec.lean](QuickselectSpec.lean) 定义了定理的输入前提和输出保证。代码地址、数组地址、栈顶和返回地址由调用状态给出。样例为了复现才选定具体地址。

| Lean 定义 | 审阅内容 |
| --- | --- |
| `ValidCall` | `X0` 指向可读写、对齐且不回绕的 `i64` 数组，`X1 = n`，`X2 = k < n`。整个数组字节数小于 `2^63`。分离逻辑要求数组、栈和调用者保留的内存互不重叠。 |
| `FirstReturn` | 从入口到第一次到达调用者地址，每条执行的 ARM64 指令计一步，包括最后的 `RET`。返回时处理器仍在运行，栈指针恢复。 |
| `WorstCaseUpper` | 对每个合法调用，存在满足预算的首次正常返回。 |
| `WorstCaseLower` | 对每个可合法调用且至少为 9 的长度，存在输入和目标秩，使首次正常返回达到下界。 |
| `Selects` | 描述所选位置的功能性质。输出是输入的排列，按有符号比较，目标位置左侧的值不大于选中值，右侧的值不小于选中值。 |

## Rust 改写

[quickselect.rs](quickselect.rs) 来自同一工作区的 `PV-playground/src/experiments/EXP-006-complexity/source/original.rs`，选用 Hoare 版本并实例化为有符号 `i64` 和 `<`。枢轴抽样位置、三数取中、两端扫描、交换顺序和搜索区间的更新沿用原程序。

源码把切片索引、交换和切片分割改为带 `Option` 的显式检查。合法调用下，抽样块始终位于活跃切片内，分区读写前有游标界，每轮把目标秩留在下一段内。检查只给这些操作增加常数工作，保留比较次数、交换次数及区间序列，因而保留渐近复杂度。差分检查覆盖了 84,444 个调用，比较了整个原地数组和所选元素。输入切片和目标秩的要求见导出函数的安全契约。域外的目标秩可能提前返回。

## 证明如何接到机器码

1. [QuickselectMachine.lean](QuickselectMachine.lean) 从链接后 `.text` 直接嵌入 804 个字节，并用 SHA-256 固定字节序列。[QuickselectSanity.lean](QuickselectSanity.lean) 检查全部 201 条指令的解码和静态控制流，并用 ARM64 语义跑五组样例。
2. [QuickselectPivotMachine.lean](QuickselectPivotMachine.lean) 证明机器码的递归枢轴选择。每次递归调用计入自己的指令数，并保留调用约定和不属于其栈帧的内存。[QuickselectPivot.lean](QuickselectPivot.lean) 将选中的枢轴转换为两侧秩界。
3. [QuickselectPartitionScan.lean](QuickselectPartitionScan.lean) 和 [QuickselectPartitionInvariant.lean](QuickselectPartitionInvariant.lean) 证明机器码的两端扫描和交换，给出扫描步数界，并用重复值计数证明分区足以缩短下一轮的活跃区间。
4. [QuickselectRounds.lean](QuickselectRounds.lean) 将枢轴选择、分区、区间更新和返回接成实际指令轮次。[QuickselectUpper.lean](QuickselectUpper.lean) 用区间长度归纳证明所有合法调用都会返回，再用 [QuickselectCost.lean](QuickselectCost.lean) 的势函数递推得到总上界。
5. [QuickselectAdversary.lean](QuickselectAdversary.lean) 逐轮逆向构造输入，使枢轴恰好淘汰 `r` 个元素，并让保留的后缀进入下一轮的构造。[QuickselectAdversaryMachine.lean](QuickselectAdversaryMachine.lean) 将实际扫描接到这个分区关系。[QuickselectLower.lean](QuickselectLower.lean) 将构造的数组放进任意可行布局，并用同一份机器码的计步轨迹证明下界。

## 复现

在 `DeepMindDemo` 目录运行以下命令。已在 x86-64 Linux 上复现。需要 Rust 1.98.1、目标 `aarch64-unknown-linux-gnu`、LLVM 二进制工具和仓库指定的 Lean/Lake。

```bash
./playground/example04-rust/check.sh
```

只运行交叉编译、机器码检查及样例时加 `--sanity-only`。脚本把 ELF、反汇编和 Lean 读取的原始 `.text` 字节分别写到 `build/quickselect.elf`、`build/quickselect.asm` 和 `build/quickselect.bin`。
