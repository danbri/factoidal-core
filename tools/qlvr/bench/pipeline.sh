#!/usr/bin/env bash
#
# tools/qlvr/bench/pipeline.sh — rebuild the `l4qlvr` executable from the C
# that Lean generated, with other C compiler options, to measure what the
# Lean-to-C pipeline gives without a change to the Lean source
# (https://github.com/danbri/factoidal/issues/797; record:
# docs/designissues/2026-10-12-lean-to-c-performance.md).
#
# It reads the Lake build of `l4qlvr` (run `lake build l4qlvr` first): the C
# files under .lake/build/ir and the link response file
# .lake/build/bin/l4qlvr.rsp. Each variant compiles every C file of the
# closure again into OUT/VARIANT/obj and links OUT/VARIANT/l4qlvr with the
# same libraries as Lake. Nothing under .lake is changed.
#
#   tools/qlvr/bench/pipeline.sh OUT VARIANT [TRAIN-INDEXDIR]
#
# Variants:
#   o3       the bundled clang, the options Lake uses (-O3 -DNDEBUG)
#   o2       the bundled clang, -O2
#   native   the bundled clang, -O3 -march=native (this host only)
#   lto      the bundled clang, -O3 -flto=thin, linked with -flto=thin
#   o3-c18   system clang 18, -O3 (the baseline of the two PGO variants)
#   pgo-c18  system clang 18, -O3 with a profile: an instrumented build
#            (-fprofile-instr-generate) runs the kernel, zstd-diff and
#            q07/q10/q16 on TRAIN-INDEXDIR, llvm-profdata merges the
#            profile, then -fprofile-instr-use. Needs libclang-rt-18-dev.
#
# The Lean runtime (libleanrt.a, libInit.a) is machine code from the
# toolchain: LTO and PGO act on the generated C only, never on the runtime
# functions it calls (lean_byte_array_push, lean_nat_big_*, the allocator).
set -euo pipefail
OUT="${1:?OUT}"; VARIANT="${2:?VARIANT}"; TRAIN="${3:-/home/user/qlvr-work/instance}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
L4="$ROOT/formal/lean4"
B="$L4/.lake/build"
TC="$(cd "$L4" && PATH="$HOME/.elan/bin:$PATH" lean --print-prefix)"
RSP="$B/bin/l4qlvr.rsp"
[ -f "$RSP" ] || { echo "pipeline: no $RSP (run lake build l4qlvr)" >&2; exit 2; }
JOBS="${JOBS:-4}"
DIR="$OUT/$VARIANT"
mkdir -p "$DIR/obj"

COMMON=(-fstack-clash-protection -ffp-contract=off -fdata-sections -ffunction-sections -fPIC
        -fvisibility=hidden -Wno-unused-command-line-argument -DNDEBUG -DLEAN_EXPORTING)
C22=("$TC/bin/clang" --sysroot "$TC" -nostdinc -isystem "$TC/include/clang" -I "$TC/include")
C18=(clang-18 -nostdinc -isystem /usr/lib/llvm-18/lib/clang/18/include -isystem "$TC/include" -I "$TC/include")
LINKX=()
case "$VARIANT" in
  o3)      CC=("${C22[@]}"); OPT=(-O3) ;;
  o2)      CC=("${C22[@]}"); OPT=(-O2) ;;
  native)  CC=("${C22[@]}"); OPT=(-O3 -march=native) ;;
  lto)     CC=("${C22[@]}"); OPT=(-O3 -flto=thin); LINKX=(-flto=thin -O3) ;;
  o3-c18)  CC=("${C18[@]}"); OPT=(-O3) ;;
  pgo-c18-gen) CC=("${C18[@]}"); OPT=(-O3 -fprofile-instr-generate)
           LINKX=(-Wl,-u,__llvm_profile_runtime /usr/lib/llvm-18/lib/clang/18/lib/linux/libclang_rt.profile-x86_64.a) ;;
  pgo-c18) CC=("${C18[@]}"); OPT=(-O3 "-fprofile-instr-use=$OUT/pgo.profdata") ;;
  *) echo "pipeline: unknown variant $VARIANT" >&2; exit 2 ;;
esac

if [ "$VARIANT" = pgo-c18 ]; then
  "$0" "$OUT" pgo-c18-gen "$TRAIN"
  rm -f "$OUT"/pgo-*.profraw
  G="$OUT/pgo-c18-gen/l4qlvr"
  K="$OUT/pgo.kernel"
  LLVM_PROFILE_FILE="$OUT/pgo-%p.profraw" "$G" kernel-dump "$TRAIN" "$K" 2>/dev/null
  LLVM_PROFILE_FILE="$OUT/pgo-%p.profraw" "$G" kernel "$K" 3 >/dev/null
  LLVM_PROFILE_FILE="$OUT/pgo-%p.profraw" "$G" zstd-diff "$TRAIN" >/dev/null
  for q in q07-join-three q10-orderby-limit-double q16-strstarts; do
    LLVM_PROFILE_FILE="$OUT/pgo-%p.profraw" "$G" query "$TRAIN" --file "$ROOT/tests/qlvr/queries/$q.rq" --repeat 3 >/dev/null 2>&1
  done
  llvm-profdata-18 merge -o "$OUT/pgo.profdata" "$OUT"/pgo-*.profraw
  rm -f "$OUT"/pgo-*.profraw "$K"
fi

# The module objects in link order, and everything after them.
mapfile -t ARGS < <(tr ' ' '\n' < "$RSP" | sed -e 's/^"//' -e 's/"$//' | grep -v '^$')
OBJS=(); REST=()
for a in "${ARGS[@]}"; do
  case "$a" in
    "$B"/ir/*.c.o.export) OBJS+=("$a") ;;
    *) REST+=("$a") ;;
  esac
done
NEW=()
for o in "${OBJS[@]}"; do
  rel="${o#"$B"/ir/}"; NEW+=("$DIR/obj/${rel//\//_}.o")
done
{ echo '#!/bin/sh'; printf 'exec'; printf ' %q' "${CC[@]}" "${COMMON[@]}" "${OPT[@]}"; echo ' -c -o "$2" "$1"'; } > "$DIR/cc.sh"
chmod +x "$DIR/cc.sh"
for k in "${!OBJS[@]}"; do
  printf '%s\0%s\0' "${OBJS[$k]%.o.export}" "${NEW[$k]}"
done | xargs -0 -n 2 -P "$JOBS" "$DIR/cc.sh" 2>"$DIR/compile.err" \
  || { echo "pipeline: compile failed ($DIR/compile.err)" >&2; exit 1; }
"$TC/bin/clang" -o "$DIR/l4qlvr" "${NEW[@]}" "${REST[@]}" "${LINKX[@]}"
echo "pipeline: $VARIANT -> $DIR/l4qlvr ($(stat -c %s "$DIR/l4qlvr") bytes)"
