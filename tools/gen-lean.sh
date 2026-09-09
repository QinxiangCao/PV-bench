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
# Only the cases that carry a lean/ directory are touched.
#
# symexec writes all three files into --lean-output-dir, overwriting a
# proof_manual. One that carries any real proof -- a theorem whose body is not
# `sorry` -- is saved and put back, unless --force-manual is passed. This is the
# Lean counterpart of the Qed./Defined. check in gen-rocq.sh.
#
# The outputs are copied aside first and put back if the run fails, so a failing
# case keeps the groundtruth it already had.

set -uo pipefail
source "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/qcp-env.sh"
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

TARGETS=()
FORCE_MANUAL=0
for a in "$@"; do
  case "$a" in
    -h|--help) sed -n '3,18p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    --force-manual) FORCE_MANUAL=1 ;;
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

# True when some theorem in the file has a body that is not just `sorry`.
has_real_proof() {
  awk '
    /^[[:space:]]*(private[[:space:]]+)?theorem[[:space:]]/ {
      if (inb && !onlysorry) { found=1 }
      inb=1; onlysorry=1; next
    }
    inb {
      line=$0
      sub(/^[[:space:]]+/,"",line); sub(/[[:space:]]+$/,"",line)
      if (line=="" || line=="sorry") next
      onlysorry=0
    }
    END { if (inb && !onlysorry) found=1; exit(found?0:1) }
  ' "$1"
}

ok=0; fail=0
for case_dir in "${cases[@]}"; do
  out="${OUT_DIR:-$case_dir/lean/groundtruth}"
  mkdir -p "$out"

  stem="$(case_stem "$case_dir")"
  manual="$out/${stem}_proof_manual.lean"
  outputs=("${stem}_goal.lean" "${stem}_proof_auto.lean" "${stem}_goal_check.lean")
  backup="$(mktemp -d)"
  for f in "${outputs[@]}"; do
    [ -f "$out/$f" ] && cp "$out/$f" "$backup/$f"
  done

  saved=""
  if [ -f "$manual" ] && [ "$FORCE_MANUAL" -eq 0 ] && has_real_proof "$manual"; then
    saved="$(mktemp)"
    cp "$manual" "$saved"
  fi

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

  if "$QCP_BIN/symexec$EXE" "${args[@]}"; then
    ok=$((ok+1))
  else
    echo "[FAIL] $case_dir" >&2
    fail=$((fail+1))
    for f in "${outputs[@]}"; do
      [ -f "$backup/$f" ] && cp "$backup/$f" "$out/$f"
    done
  fi
  rm -rf "$backup"

  if [ -n "$saved" ]; then
    cp "$saved" "$manual"
    rm -f "$saved"
  fi

  # Only this case's staging files -- a repo-wide sweep would delete the
  # in-flight output of a concurrent run.
  find "$out" "$case_dir/lean" -maxdepth 1 -name '*.sacgen.tmp' -delete 2>/dev/null
done
echo "lean groundtruth: $ok ok, $fail failed"
[ "$fail" -eq 0 ]
