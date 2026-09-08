#!/usr/bin/env bash
#
# Regenerate the Rocq groundtruth for one or more cases.
#
#   scripts/gen-rocq.sh                      # every case under benchmarks/
#   scripts/gen-rocq.sh benchmarks/Algorithms/bubble_sort
#   scripts/gen-rocq.sh benchmarks/Codeforces/examples_shard00
#   OUT_DIR=/tmp/gt scripts/gen-rocq.sh <case>   # write elsewhere, e.g. to diff
#
# For each case it runs symexec on rocq/solution_annotated.c and writes
# <stem>_goal.v, <stem>_proof_auto.v, <stem>_proof_manual.v and
# <stem>_goal_check.v into rocq/groundtruth/. A case that ships a .strategies
# file also gets StrategyCheck run on it.
#
# symexec refuses to overwrite, so existing generated files are removed first --
# except a proof_manual that holds real proofs (Qed./Defined.), which is kept
# unless --force-manual is passed.

set -uo pipefail
source "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/qcp-env.sh"
ROOT="$(cd "$BACKEND/.." && pwd)"

FORCE_MANUAL=0
TARGETS=()
for a in "$@"; do
  case "$a" in
    --force-manual) FORCE_MANUAL=1 ;;
    -h|--help) sed -n '3,20p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) TARGETS+=("$a") ;;
  esac
done
[ ${#TARGETS[@]} -gt 0 ] || TARGETS=("$ROOT/benchmarks")

# collect case dirs: a directory holding rocq/solution_annotated.c
cases=()
for t in "${TARGETS[@]}"; do
  [ -d "$t" ] || { echo "not a directory: $t" >&2; exit 2; }
  while IFS= read -r c; do cases+=("$(dirname "$(dirname "$c")")"); done \
    < <(find "$t" -path '*/rocq/solution_annotated.c' | sort)
done
[ ${#cases[@]} -gt 0 ] || { echo "no cases with rocq/solution_annotated.c under: ${TARGETS[*]}" >&2; exit 1; }

ok=0; fail=0
for case_dir in "${cases[@]}"; do
  stem="$(case_stem "$case_dir")"
  out="${OUT_DIR:-$case_dir/rocq/groundtruth}"
  mkdir -p "$out"

  for suffix in goal proof_auto goal_check; do rm -f "$out/${stem}_${suffix}.v"; done
  manual="$out/${stem}_proof_manual.v"
  if [ -f "$manual" ] && [ "$FORCE_MANUAL" -eq 0 ] && grep -qE '^\s*(Qed|Defined)\.' "$manual"; then
    :   # holds real proofs -- leave it, symexec will skip it
  else
    rm -f "$manual"
  fi

  args=(
    "--goal-file=$out/${stem}_goal.v"
    "--proof-auto-file=$out/${stem}_proof_auto.v"
    "--proof-manual-file=$manual"
    "--coq-logic-path=$(logic_path "$case_dir" rocq.groundtruth)"
    "-I$case_dir/rocq/"
    "-I$case_dir/"
    "-I${case_dir%%benchmarks/*}benchmarks/"
    "${SHARED_ARGS[@]}"
    "--input-file=$case_dir/rocq/solution_annotated.c"
    "--no-exec-info"
  )
  # extra driver flags a case needs (e.g. --float-finite-vc), one per line
  if [ -f "$case_dir/rocq/.qcp-flags" ]; then
    while IFS= read -r f; do [ -n "$f" ] && args+=("$f"); done < "$case_dir/rocq/.qcp-flags"
  fi
  # a case-local strategy folder maps onto the case's own logic path
  if compgen -G "$case_dir/rocq/*.strategies" > /dev/null; then
    args+=("-slp" "$case_dir/rocq/" "$(logic_path "$case_dir" rocq.groundtruth)")
  fi

  if "$QCP_BIN/symexec$EXE" "${args[@]}"; then
    for s in "$case_dir"/rocq/*.strategies; do
      [ -e "$s" ] || continue
      "$QCP_BIN/StrategyCheck$EXE" \
        "--coq-output-dir=$out/" \
        "--coq-logic-path=$(logic_path "$case_dir" rocq.groundtruth)" \
        "-I$case_dir/rocq/" "-I$case_dir/" "-I${case_dir%%benchmarks/*}benchmarks/" "-slp" "$case_dir/rocq/" "$(logic_path "$case_dir" rocq.groundtruth)" \
        "${SHARED_ARGS[@]}" \
        "--input-file=$s" "--no-exec-info" \
        || { echo "[FAIL strategy] $s" >&2; fail=$((fail+1)); continue 2; }
    done
    ok=$((ok+1))
  else
    echo "[FAIL] $case_dir" >&2
    fail=$((fail+1))
  fi
done

find "$ROOT" -name '*.sacgen.tmp' -delete 2>/dev/null
echo "rocq groundtruth: $ok ok, $fail failed"
[ "$fail" -eq 0 ]
