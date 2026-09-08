# Sourced by the generator scripts. Locates the QCP backend, then sets QCP_BIN
# to this machine's binary directory.
#
# The backend holds the symexec binaries, the shared .strategies/.h that symexec
# reads, and the compiled Rocq/Lean libraries. It is not part of this branch;
# point QCP_BACKEND at it, or check out the `with-backend` branch, which carries
# one at ./backend.

REPO="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

if [ -n "${QCP_BACKEND:-}" ]; then
  BACKEND="$QCP_BACKEND"
elif [ -d "$REPO/backend/binary" ]; then
  BACKEND="$REPO/backend"                       # the with-backend branch
elif [ -f "$REPO/benchmarks/CONFIGURE" ]; then
  # reuse the Rocq path already configured for make: <backend>/Rocq
  BACKEND="$(sed -n 's/^[[:space:]]*QCP_ROCQ[[:space:]]*=[[:space:]]*//p' "$REPO/benchmarks/CONFIGURE" | tail -1)"
  BACKEND="${BACKEND%/Rocq}"
fi

[ -n "${BACKEND:-}" ] && [ -d "$BACKEND/binary" ] || {
  echo "cannot find the QCP backend (needs <backend>/binary and <backend>/QCP_examples)." >&2
  echo "  set QCP_BACKEND=/path/to/backend, or use the with-backend branch." >&2
  exit 2
}
BACKEND="$(cd "$BACKEND" && pwd)"

case "$(uname -s)" in
  Darwin)
    case "$(uname -m)" in
      arm64|aarch64) QCP_BIN="$BACKEND/binary/mac-arm64-binary" ;;
      x86_64|amd64)  QCP_BIN="$BACKEND/binary/mac-x86-64-binary" ;;
      *) echo "unsupported macOS arch: $(uname -m)" >&2; exit 2 ;;
    esac ;;
  Linux)
    case "$(uname -m)" in
      x86_64|amd64) QCP_BIN="$BACKEND/binary/linux-binary" ;;
      *) echo "unsupported Linux arch: $(uname -m)" >&2; exit 2 ;;
    esac ;;
  MINGW*|MSYS*|CYGWIN*) QCP_BIN="$BACKEND/binary/win-binary" ;;
  *) echo "unsupported platform: $(uname -s)" >&2; exit 2 ;;
esac

EXE=""
[ -f "$QCP_BIN/symexec.exe" ] && EXE=".exe"

for tool in symexec StrategyCheck; do
  [ -x "$QCP_BIN/$tool$EXE" ] || {
    echo "missing or not executable: $QCP_BIN/$tool$EXE" >&2
    echo "  (git does not always preserve the exec bit: chmod +x $QCP_BIN/*)" >&2
    exit 2
  }
done

# Shared strategy sources. These folders hold the .strategies and .h files that
# symexec reads; they are not the compiled Rocq/Lean libraries.
SHARED_ARGS=(
  "-I$BACKEND/QCP_examples/QCP_demos_LLM/"
  "-slp" "$BACKEND/QCP_examples/QCP_demos_LLM/" "SimpleC.EE.QCP_demos_LLM"
  "-I$BACKEND/QCP_examples/LLM_bench/"
  "-I$BACKEND/QCP_examples/LLM_bench/Codeforces/"
  "-slp" "$BACKEND/QCP_examples/LLM_bench/" "SimpleC.EE.LLM_bench"
  "-I$BACKEND/QCP_examples/stdlib/"
  "-slp" "$BACKEND/QCP_examples/stdlib/" "SimpleC.StdLib"
)

# case_stem <case-dir> -- the prefix of the generated files, i.e. the directory name.
case_stem() {
  basename "$1"
}

# Rocq: PVbench.<dotted case path>.<suffix>  (matches -R benchmarks PVbench)
logic_path() {
  local rel="${1#*benchmarks/}"
  printf 'PVbench.%s.%s' "$(printf '%s' "$rel" | tr '/' '.')" "$2"
}

# Lean: <dotted case path>.<suffix>, no prefix -- lakefile roots are the corpus
# names themselves (Algorithms, Codeforces, ...), not a PVbench package.
lean_logic_path() {
  local rel="${1#*benchmarks/}"
  printf '%s.%s' "$(printf '%s' "$rel" | tr '/' '.')" "$2"
}
