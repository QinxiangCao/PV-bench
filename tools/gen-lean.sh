#!/usr/bin/env bash
#
# Regenerate the Lean groundtruth for one or more cases.
#
#   scripts/gen-lean.sh                       # every case with a lean/ dir
#   scripts/gen-lean.sh benchmarks/Algorithms/bubble_sort
#   OUT_DIR=/tmp/gt scripts/gen-lean.sh <case>
#
# Same walk as gen-rocq.sh, but drives the Lean output path of symexec:
# --no-coq-gen --lean-output-dir=<case>/lean/groundtruth
#                --lean-logic-path=<dotted case path>.lean.groundtruth
#                --input-file-name=<stem>.c   (this is what names the outputs)
#
# Only the 83 cases that carry a lean/ directory are touched.

set -uo pipefail
source "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/qcp-env.sh"
ROOT="$(cd "$BACKEND/.." && pwd)"

TARGETS=()
for a in "$@"; do
  case "$a" in
    -h|--help) sed -n '3,14p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) TARGETS+=("$a") ;;
  esac
done
[ ${#TARGETS[@]} -gt 0 ] || TARGETS=("$ROOT/benchmarks")

cases=()
for t in "${TARGETS[@]}"; do
  [ -d "$t" ] || { echo "not a directory: $t" >&2; exit 2; }
  while IFS= read -r c; do cases+=("$(dirname "$(dirname "$c")")"); done \
    < <(find "$t" -path '*/lean/solution_annotated.c' | sort)
done
[ ${#cases[@]} -gt 0 ] || { echo "no cases with lean/solution_annotated.c under: ${TARGETS[*]}" >&2; exit 1; }

ok=0; fail=0
for case_dir in "${cases[@]}"; do
  out="${OUT_DIR:-$case_dir/lean/groundtruth}"
  mkdir -p "$out"

  args=(
    "--no-coq-gen"
    "--lean-output-dir=$out"
    "--lean-logic-path=$(lean_logic_path "$case_dir" lean.groundtruth)"
    "--input-file-name=$(case_stem "$case_dir").c"
    "-I$case_dir/lean/"
    "-I$case_dir/"
    "-I${case_dir%%benchmarks/*}benchmarks/"
    "${SHARED_ARGS[@]}"
    "--input-file=$case_dir/lean/solution_annotated.c"
    "--no-exec-info"
  )
  if [ -f "$case_dir/lean/.qcp-flags" ]; then
    while IFS= read -r f; do [ -n "$f" ] && args+=("$f"); done < "$case_dir/lean/.qcp-flags"
  fi

  if "$QCP_BIN/symexec$EXE" "${args[@]}"; then ok=$((ok+1)); else
    echo "[FAIL] $case_dir" >&2; fail=$((fail+1))
  fi
done

find "$ROOT" -name '*.sacgen.tmp' -delete 2>/dev/null
echo "lean groundtruth: $ok ok, $fail failed"
[ "$fail" -eq 0 ]
