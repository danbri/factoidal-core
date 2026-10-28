#!/usr/bin/env bash
# tools/build-exe.sh — build the `factoidal` CLI as one executable file per
# platform with `deno compile`, the engine wasm included.
# Stage 1 of docs/designissues/2026-10-28-single-file-app.md (owner,
# 2026-10-28: "2y").
#
# Usage: tools/build-exe.sh OUTDIR [--targets T1,T2,...]
#
#   OUTDIR      receives factoidal-<platform>[.exe] and SHA256SUMS
#   --targets   deno targets (default: all six below)
#
# FACTOIDAL_PKG names another package directory (an npm install of
# @factoidal/core) in place of npm/factoidal.
#
# Needs: deno 2.9 or later on PATH, and the engine assets in
# npm/factoidal/l4-assets/ (tools/fetch-builds.sh --set web, or a wasm build).
# deno downloads its runtime for each target from dl.deno.land; where that
# host is not reachable, set DENORT_DIR to a directory that holds
# <target>/denort (or denort.exe), unpacked from the denort-<target>.zip
# assets of https://github.com/denoland/deno/releases for the same version.
#
# The executables are granted every Deno permission (--allow-all), which is
# what `node bin/factoidal.mjs` has. Each file is about 85 to 125 MB (the
# runtime plus the 17 MB wasm). Check one with tools/check-exe.sh.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${1:?usage: tools/build-exe.sh OUTDIR [--targets T1,T2,...]}"
shift
TARGETS="x86_64-unknown-linux-gnu,aarch64-unknown-linux-gnu,x86_64-apple-darwin,aarch64-apple-darwin,x86_64-pc-windows-msvc,aarch64-pc-windows-msvc"
while [ $# -gt 0 ]; do
  case "$1" in
    --targets) TARGETS="$2"; shift 2 ;;
    *) echo "build-exe: unknown argument $1" >&2; exit 2 ;;
  esac
done

command -v deno >/dev/null || { echo "build-exe: deno is not on PATH" >&2; exit 2; }
PKG="${FACTOIDAL_PKG:-$REPO_ROOT/npm/factoidal}"
[ -f "$PKG/l4-assets/l4factoidal.wasm" ] || { echo "build-exe: $PKG/l4-assets/l4factoidal.wasm is missing (tools/fetch-builds.sh --set web)" >&2; exit 2; }
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"

name_of () {
  case "$1" in
    x86_64-unknown-linux-gnu) echo factoidal-linux-x86_64 ;;
    aarch64-unknown-linux-gnu) echo factoidal-linux-aarch64 ;;
    x86_64-apple-darwin) echo factoidal-darwin-x86_64 ;;
    aarch64-apple-darwin) echo factoidal-darwin-arm64 ;;
    x86_64-pc-windows-msvc) echo factoidal-windows-x86_64.exe ;;
    aarch64-pc-windows-msvc) echo factoidal-windows-aarch64.exe ;;
    *) echo "build-exe: unknown target $1" >&2; return 1 ;;
  esac
}

echo "build-exe: $(deno --version | head -1); engine $(sha256sum "$PKG/l4-assets/l4factoidal.wasm" | cut -c1-16)"
IFS=',' read -r -a LIST <<<"$TARGETS"
for T in "${LIST[@]}"; do
  N="$(name_of "$T")"
  ENVS=()
  if [ -n "${DENORT_DIR:-}" ]; then
    B="$DENORT_DIR/$T/denort"; [ -f "$B" ] || B="$B.exe"
    [ -f "$B" ] || { echo "build-exe: DENORT_DIR has no $T/denort" >&2; exit 1; }
    ENVS=(DENORT_BIN="$B")
  fi
  # Paths relative to the package, so the engine resolves l4-assets/ next to
  # bin/ inside the executable as it does in an npm install.
  ( cd "$PKG" && env "${ENVS[@]}" deno compile --quiet --allow-all --no-check --target "$T" \
      --include l4-assets --output "$OUT/$N" bin/factoidal.mjs )
  echo "build-exe: $N $(du -m "$OUT/$N" | cut -f1) MB"
done
( cd "$OUT" && sha256sum factoidal-* > SHA256SUMS )
echo "build-exe: wrote $OUT/SHA256SUMS"
