#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Rebuild the very same C functions and validate the linked instruction words.
./example02-c/check.sh
lake build +QuicksortCostInput +QuicksortDriverCost
# Elaborate against the bytes produced by this run of the compiler and linker.
lake lean example03-c/QuicksortCost.lean
