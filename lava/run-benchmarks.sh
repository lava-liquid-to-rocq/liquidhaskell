#!/usr/bin/env bash
# Run the lava translation on every .ilh_no_elab.bin under lava/out/Benchmark
#
# Usage:
#   ./run-benchmarks.sh                 # plain mode
#   ./run-benchmarks.sh --equations     # Equations-mode preamble
#
# Requires `cabal build lava:exe:lava` to have produced the executable.

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
ROOT_DIR=$(cd -- "$SCRIPT_DIR/.." && pwd)
BENCH_DIR="$SCRIPT_DIR/out/Benchmark"

EXTRA_FLAGS=()
for arg in "$@"; do
    case "$arg" in
        --equations)   EXTRA_FLAGS+=("--equations") ;;
        --has-imports) EXTRA_FLAGS+=("--has-imports") ;;
        *) echo "unknown flag: $arg" >&2; exit 2 ;;
    esac
done

LAVA=$(cd "$ROOT_DIR" && cabal list-bin lava:exe:lava)
if [[ ! -x "$LAVA" ]]; then
    echo "lava executable not found at $LAVA; run \`cabal build lava:exe:lava\` first" >&2
    exit 1
fi

if [[ ! -d "$BENCH_DIR" ]]; then
    echo "no benchmark output dir at $BENCH_DIR" >&2
    exit 1
fi

mapfile -t bin_files < <(find "$BENCH_DIR" -type f -name '*.ilhb' | sort)

if (( ${#bin_files[@]} == 0 )); then
    echo "no .ilh_no_elab.bin files under $BENCH_DIR" >&2
    exit 1
fi

ok=0
fail=0
for bin in "${bin_files[@]}"; do
    rel=${bin#"$BENCH_DIR/"}
    echo "==> $rel"
    if "$LAVA" "${EXTRA_FLAGS[@]}" "$bin"; then
        ok=$((ok + 1))
    else
        fail=$((fail + 1))
        echo "    FAILED: $rel" >&2
    fi
done

echo
echo "translated: $ok    failed: $fail    total: ${#bin_files[@]}"
exit $(( fail > 0 ? 1 : 0 ))
