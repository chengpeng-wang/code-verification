#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p build

flags=(--target=aarch64-linux-gnu -march=armv8-a -O1 -ffreestanding
    -fno-stack-protector -fno-unwind-tables -fno-asynchronous-unwind-tables
    -fno-optimize-sibling-calls -fno-omit-frame-pointer)
clang "${flags[@]}" -c quicksort.c -o build/quicksort.o
clang "${flags[@]}" -c quicksort_partition.c -o build/quicksort_partition.o

# Resolve the three BL instructions before extracting the executable code.
if command -v ld.lld >/dev/null; then
    linker=(ld.lld)
elif command -v rustc >/dev/null &&
     rust_lld="$(rustc +stable --print target-libdir)/../bin/rust-lld" &&
     [[ -x "$rust_lld" ]]; then
    linker=("$rust_lld" -flavor gnu)
else
    echo 'Install ld.lld or use a Rust toolchain that includes rust-lld.' >&2
    exit 1
fi
"${linker[@]}" -m aarch64elf --entry=quicksort_u8 --no-relax \
    build/quicksort.o build/quicksort_partition.o -o build/quicksort_u8.elf

llvm-objcopy -O binary --only-section=.text build/quicksort_u8.elf build/quicksort_u8.bin
llvm-objdump -d --section=.text build/quicksort_u8.elf | tee build/quicksort_u8.asm

# include_bytes% reads exactly this many bytes. Guard against extra instructions.
if [[ $(wc -c < build/quicksort_u8.bin) -ne 184 ]]; then
    echo 'Expected 184 bytes in the linked quicksort .text.' >&2
    exit 1
fi

cd ..
lake build +QuicksortMachine
# Re-elaborate the theorem against the freshly linked bytes.
lake lean example02-c/QuicksortBinary.lean
