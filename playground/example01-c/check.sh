#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p build

clang --target=aarch64-linux-gnu -march=armv8-a -O2 -ffreestanding \
    -ffunction-sections -fno-stack-protector -fno-unwind-tables \
    -fno-asynchronous-unwind-tables -c store_byte.c -o build/store_byte.o

llvm-objcopy --dump-section .text.store_byte=build/store_byte.bin build/store_byte.o

# The proof imports exactly two instructions, so reject a longer or shorter section.
if [[ $(wc -c < build/store_byte.bin) -ne 8 ]]; then
    echo 'Expected two AArch64 instructions in .text.store_byte.' >&2
    exit 1
fi

llvm-objdump -dr --section=.text.store_byte build/store_byte.o

# Re-elaborate the proof on every run so Lean reads the freshly compiled bytes.
cd ..
lake lean example01-c/Example01C.lean
