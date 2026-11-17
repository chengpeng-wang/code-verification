# AlphaProof Code Playground

新增验证例子时，先在规格和主定理旁注释要证明的性质，再在该例子的 README 中列出供审阅的主定理、输入前提、实际输出和保证。提交证明结果时指出这些位置，方便先核对目标，再检查证明。

## Example 1 — C

用 ARM64 机器语义证明 [`store_byte.c`](example01-c/store_byte.c) 编译出来的函数会把参数 `value` 写到 `*dst`，保留相邻的一个字节，然后返回调用者。

在 `DeepMindDemo` 目录运行。需要 Clang、`llvm-objcopy`、`llvm-objdump` 和由仓库 `lean-toolchain` 指定的 Lean/Lake。当前实验在 x86_64 Linux 上交叉编译。

```bash
./playground/example01-c/check.sh
```

脚本每次都会重新编译 C，然后重查 Lean 证明。第一次运行时，Lake 会先构建所需的本地 ARM64 库。

```text
store_byte.c  ── Clang ──▶  AArch64 ELF 对象文件 (.o)
                               │ 提取 .text.store_byte
                               ▼
                         函数的 8 个机器码字节
                               │ Lean 的 include_bytes%
                               ▼
                    装入可执行内存，按 PC 取指并执行
                               │ Arm64.Step + Arm64.Steps
                               ▼
                     验证目标字节、相邻字节和返回地址
```

1. [`check.sh`](example01-c/check.sh) 使用 `clang --target=aarch64-linux-gnu -O2 -c` 生成对象文件，并将函数单独放进 `.text.store_byte` 节。`llvm-objcopy` 提取该节的真实字节。当前产物是 `strb w1, [x0]` 和 `ret`。
2. [`Example01C.lean`](example01-c/Example01C.lean) 直接读入提取的字节，调用库里的 `loadCodeMem` 装载程序。初始机器状态把目标指针放在 `X0`，待写字节放在 `X1` 的低位，返回地址放在 `LR`。实验固定代码、数据和返回地址，旧字节、待写字节以及相邻字节都由定理任意量化。
3. `store_byte_correct` 构造两个 `Arm64.Step`，并用 `Arm64.Steps` 把它们接起来。每一步都必须由模型从内存中成功取指。取指证明里的 `change` 由 Lean 检查数据字节是否与取指无关，因此取指可以用具体值计算，整个定理仍适用于任意输入字节。最后证明目标字节等于 `value`，相邻字节等于原值，`PC` 等于返回地址，处理器状态仍为 `.Running`。

通过时，输出末尾会显示 `Example01C.store_byte_correct` 只依赖 Lean 的标准公理 `propext`、`Classical.choice`、`Quot.sound`。

可以把 C 函数里的 `*dst = value` 临时改成 `*dst = 0`，再运行脚本。编译器会改写存储指令，Lean 会在第一步取指的证明处报错。把赋值恢复后可以重新通过检查。

## Example 02 — C 快速排序

证明 `quicksort_u8(a, n)` 的 ARM64 机器码会正常返回，并在原数组地址写回输入的升序排列。审阅时先检查主定理中的 `output` 和 `Spec.Sorts input output`。例子目录里的 README 列出了调用前提、返回保证和各证明文件的用途。 [Example 02 的证明目标](example02-c/README.md#先审阅证明目标)

在 `DeepMindDemo` 目录运行以下命令。

```bash
./playground/example02-c/check.sh
```

## Example 03 — C 快速排序的最坏复杂度

对同一份快排 ARM64 机器码证明首次返回的指令数具有最坏情况二次界。先核对通用上界与全相等输入的下界是否符合要验证的目标。 [Example 03 的证明目标](example03-c/README.md#先审阅证明目标)

```bash
./playground/example03-c/check.sh
```

## Example 04 — Rust Hoare Quickselect

将原 Hoare Quickselect 改写为可链接、可由 ARM64 模型执行的 Rust 程序。证明这份机器码的最坏指令数具有同阶上下界。 [Example 04 的证明目标](example04-rust/README.md#先审阅证明目标)

```bash
./playground/example04-rust/check.sh
```
