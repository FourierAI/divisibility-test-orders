#!/bin/sh
set -eu
if [ "$#" -ne 1 ]; then echo "usage: sh build.sh OUTPUT_EXECUTABLE" >&2; exit 2; fi
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
incdir=$(mktemp -d)
trap 'rm -f "$incdir/trace_core.inc"; rmdir "$incdir"' EXIT
# Reuse the actual producer/estimator and omit its archived benchmark main.
awk '/^int main\(int argc/{found=1;exit} {print} END{if(!found)exit 2}' "$src/../stopped_benchmark.cpp" > "$incdir/trace_core.inc"
clang++ -std=c++17 -O3 -mcpu=native -I"$incdir" -I"$src/.." "$src/onehit_shift.cpp" -o "$1"
