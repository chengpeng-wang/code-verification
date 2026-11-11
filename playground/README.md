# AlphaProof Code Playground

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

[`quicksort.c`](example02-c/quicksort.c) 的入口是 `quicksort_u8(a, n)`，对 `n` 个 `uint8_t` 原地排序。`n` 由调用者传入，长度为 0 或 1 时直接返回。[分区函数](example02-c/quicksort_partition.c) 取首元素作为枢轴，将小于它的元素移到左边，将大于或等于它的元素留在右边，然后把枢轴放在中间。快速排序递归处理这两个子数组。

在 `DeepMindDemo` 目录运行以下命令。

```bash
./playground/example02-c/check.sh
```

此例还需要支持 AArch64 的 `ld.lld`。如果找不到 `ld.lld`，脚本会尝试本机 Rust stable 工具链里的 `rust-lld`。脚本用 Clang 18.1.3 的 ARMv8-A、`-O1` 产物开发，保留两次递归调用以便对照反汇编读证明。链接会解析三条 `bl` 指令的目标，包括一次调用分区函数和两次递归调用。

| 文件 | 验证内容 |
| --- | --- |
| [`QuicksortSpec.lean`](example02-c/QuicksortSpec.lean) | 定义升序且保留元素及其出现次数的规格，证明递归参考算法满足它，并提供分区循环不变量。 |
| [`QuicksortPartition.lean`](example02-c/QuicksortPartition.lean) | 在 ARM64 模型里证明分区函数的循环会结束，写回输入的一个排列，并在 `X0` 返回正确的枢轴位置。 |
| [`QuicksortMachine.lean`](example02-c/QuicksortMachine.lean) | 证明主函数指令流。分区后的两个子数组都更短，证明通过对长度归纳得到两个递归调用的契约。 |
| [`QuicksortBinary.lean`](example02-c/QuicksortBinary.lean) | 读取本次链接出的 184 个机器码字节，由 Lean 内核核对两段指令序列，再将指令证明应用到这份二进制。 |

从 `quicksort_returns_sorted` 可以直接读出机器定理。入口状态的 `X0` 是数组指针，`X1` 是输入长度，`PC` 是代码入口，`LR` 是返回地址。代码需完整装载在可执行内存中，数组字节可读写，初始栈指针满足 16 字节对齐。证明采用 `48 * n` 字节的充分栈空间预算，每个实际进入递归分支的调用使用 48 字节。栈和数组的分离断言要求它们不重叠。结论是程序返回到初始 `LR`，栈指针和被调用者保存寄存器恢复，数组内容为原输入的无符号升序排列，并保留调用者通过 `frame` 描述的分离内存。

运行后，`example02-c/build/quicksort_u8.asm` 是反汇编，`quicksort_u8.elf` 是链接结果，`quicksort_u8.bin` 是从 ELF 提取的 `.text` 原始字节。Lean 每次重新读取 `.bin`。修改 C 或编译选项后，如果机器码发生变化，脚本会在长度或指令字核对时指出差异。
