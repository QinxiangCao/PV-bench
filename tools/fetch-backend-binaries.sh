#!/usr/bin/env bash
#
# Download the QCP binaries (symexec, StrategyCheck) into backend/binary/.
#
# They are not in git: they are ~13 MB of platform builds that upstream reissues
# every week or so, and committing each one would grow the history without bound.
# They ride on a GitHub release instead.
#
#   tools/fetch-backend-binaries.sh              # the release named below
#   tools/fetch-backend-binaries.sh v2026.09.07  # a specific one
#
# The repo carrying the release is read from the origin remote. Override it with
# QCP_BINARY_REPO=<owner>/<repo>, and the tag with QCP_BINARY_TAG.
#
# Or fetch them yourself: unpack the archive so that backend/binary/ holds
# linux-binary/, mac-arm64-binary/, mac-x86-64-binary/ and win-binary/.

set -euo pipefail

TAG="${1:-${QCP_BINARY_TAG:-backend-binaries}}"
ASSET="qcp-binaries.tar.gz"

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
dest="$root/backend/binary"

origin_repo() {
  local url
  url="$(git -C "$root" remote get-url origin 2>/dev/null)" || return 1
  case "$url" in *github.com[:/]*) ;; *) return 1 ;; esac
  url="${url#*github.com}"
  url="${url#[:/]}"
  printf '%s\n' "${url%.git}"
}

REPO="${QCP_BINARY_REPO:-$(origin_repo || true)}"
if [ -z "$REPO" ]; then
  echo "cannot tell which repo holds the release: no github.com origin remote." >&2
  echo "set QCP_BINARY_REPO=<owner>/<repo> and retry." >&2
  exit 2
fi

command -v curl >/dev/null || { echo "curl is required" >&2; exit 2; }

url="https://github.com/$REPO/releases/download/$TAG/$ASSET"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "fetching $url"
curl -fSL "$url" -o "$tmp/$ASSET" || {
  echo "download failed. check that the release '$TAG' has a '$ASSET' asset." >&2
  exit 1
}

mkdir -p "$dest"
tar -xzf "$tmp/$ASSET" -C "$dest" --strip-components=1 2>/dev/null \
  || tar -xzf "$tmp/$ASSET" -C "$dest"

chmod +x "$dest"/*/symexec "$dest"/*/StrategyCheck 2>/dev/null || true

echo "installed:"
for d in "$dest"/*/; do
  [ -d "$d" ] && printf '  %s\n' "$(basename "$d")"
done
