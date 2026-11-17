#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

fail() {
    echo "$1" >&2
    exit 1
}

case "${1-}" in
    ''|--sanity-only) ;;
    *) fail 'Usage: check.sh [--sanity-only]' ;;
esac

mkdir -p build

rust=(rustc +1.98.1)
"${rust[@]}" --edition=2021 --crate-type=lib --emit=obj \
    --target=aarch64-unknown-linux-gnu -C target-cpu=generic -C opt-level=3 \
    -C panic=abort -C relocation-model=static -C codegen-units=1 \
    quickselect.rs -o build/quickselect.o
rust_lld="$("${rust[@]}" --print target-libdir)/../bin/rust-lld"
"$rust_lld" -flavor gnu -m aarch64elf --gc-sections \
    --entry=quickselect_hoare_i64 build/quickselect.o -o build/quickselect.elf

# All executable bytes must come from .text and all references must be linked.
elf_header=$(llvm-readelf -h build/quickselect.elf)
machine=$(awk '/Machine:/ { print $NF }' <<< "$elf_header")
[[ $machine == AArch64 ]] || fail 'Expected an AArch64 ELF image.'
undefined_symbols=$(llvm-nm --undefined-only build/quickselect.elf)
[[ -z $undefined_symbols ]] || fail "Unresolved symbols: $undefined_symbols"
relocations=$(llvm-readelf -r build/quickselect.elf | awk 'NF')
[[ $relocations == 'There are no relocations in this file.' ]] || fail "$relocations"
sections=$(llvm-objdump -h build/quickselect.elf)
exec_sections=$(awk '$NF == "TEXT" { print $2 }' <<< "$sections")
[[ $exec_sections == .text ]] || fail "Unexpected executable sections: $exec_sections"

# Match the executable's entry point and relative entry offset to the Lean model.
text_base=$(awk '$2 == ".text" { print $4 }' <<< "$sections")
elf_entry=$(awk '/Entry point address:/ { print $NF }' <<< "$elf_header")
symbols=$(llvm-nm --defined-only --format=posix build/quickselect.elf)
entry_symbol=$(awk '$1 == "quickselect_hoare_i64" { print $3 }' <<< "$symbols")
[[ -n $text_base && -n $elf_entry && -n $entry_symbol ]] || fail 'Missing entry or .text address.'
(( elf_entry == 16#$entry_symbol && elf_entry - 16#$text_base == 0x1ac )) \
    || fail 'ELF entry differs from the Lean entry offset 0x1ac.'

llvm-objcopy -O binary --only-section=.text build/quickselect.elf build/quickselect.bin
llvm-objdump -d --section=.text build/quickselect.elf > build/quickselect.asm

cd ..
lake build +QuickselectSanity
lake env lean --run example04-rust/QuickselectSanity.lean
if [[ ${1-} != --sanity-only ]]; then
    lake build Example04Rust
fi
