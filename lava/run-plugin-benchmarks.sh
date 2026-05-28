#!/usr/bin/env bash
# Drive `ghc -fplugin=LiquidHaskellBoot -fplugin=Lava.Plugin` over every
# benchmark under tests/refcore/Benchmark
#
# Usage:
#   ./run-plugin-benchmarks.sh                  # all benchmarks
#   ./run-plugin-benchmarks.sh Half PeanoNats   # subset (basenames, no extension)

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
ROOT_DIR=$(cd -- "$SCRIPT_DIR/.." && pwd)
BENCH_DIR="$ROOT_DIR/tests/refcore/Benchmark"

if [[ ! -d "$BENCH_DIR" ]]; then
    echo "no benchmark sources at $BENCH_DIR" >&2
    exit 1
fi

(cd "$ROOT_DIR" && cabal build liquidhaskell-boot lava) >/dev/null

mapfile -t all_files < <(find "$BENCH_DIR" -type f -name '*.hs' | sort)

if [[ $# -gt 0 ]]; then
    selected=()
    for f in "${all_files[@]}"; do
        for want in "$@"; do
            if [[ "$(basename "$f" .hs)" == "$want" ]]; then
                selected+=("$f")
            fi
        done
    done
    files=("${selected[@]}")
else
    files=("${all_files[@]}")
fi

if (( ${#files[@]} == 0 )); then
    echo "no matching benchmarks" >&2
    exit 1
fi

GHC_FLAGS=(
    -fplugin=LiquidHaskellBoot
    -fplugin=Lava.Plugin
    -package liquidhaskell-boot
    -package lava
    -package liquid-prelude
    -i"$ROOT_DIR/tests/refcore"
)

ok=0
fail=0
failed=()
for src in "${files[@]}"; do
    rel=${src#"$ROOT_DIR/"}
    echo "==> $rel"
    if (cd "$ROOT_DIR" && cabal exec -- ghc "${GHC_FLAGS[@]}" "$src") 2>&1 \
        | sed -e 's/^/    /'; then
        ok=$((ok + 1))
    else
        fail=$((fail + 1))
        failed+=("$rel")
    fi
done

echo
echo "passed: $ok    failed: $fail    total: ${#files[@]}"
if (( fail > 0 )); then
    printf '  failed: %s\n' "${failed[@]}"
fi
exit $(( fail > 0 ? 1 : 0 ))
