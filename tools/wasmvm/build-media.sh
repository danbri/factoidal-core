#!/bin/bash
# Build audio and video decoders to standalone WebAssembly modules for the Lean WasmVM
# engine (record: docs/designissues/2026-11-08-media-wasmvm.md).
#
# Usage: tools/wasmvm/build-media.sh [WORKDIR]
#   WORKDIR (default ~/working/media-wasm) gets the pinned release tarballs (checked by
#   SHA-256), their sources, and the outputs opus-wasmvm.wasm, vorbis-wasmvm.wasm and
#   vp8-wasmvm.wasm. Nothing is written into the repository; the outputs are not
#   committed.
#
# Libraries and licences (all permissive, BSD 3-clause):
#   libopus 1.5.2     https://opus-codec.org         (decoder; float build)
#   libogg 1.3.5      https://xiph.org/ogg/          (only ogg_packet and the bit reader)
#   libvorbis 1.3.7   https://xiph.org/vorbis/       (decoder files only)
#   libvpx 1.15.2     https://www.webmproject.org/   (VP8 decoder only)
# The Ogg and WebM containers are read in Lean (L4Factoidal/Media), not by these
# libraries: the modules get one packet or frame per call.
#
# Flags, and why:
#   -sSTANDALONE_WASM --no-entry  WASI imports only, no JavaScript glue
#   -mno-simd128                  the engine has no SIMD
#   no threads                    libvpx: --disable-multithread
#   libvpx: --target=generic-gnu, no assembly, no run-time CPU detection: plain C
#   -sSUPPORT_LONGJMP=wasm        libvpx's setjmp/longjmp error path as Wasm exceptions
#                                 (legacy try/catch/delegate, which WasmVM runs), not
#                                 the JavaScript invoke_* imports of the default
#   -O2                           speed matters more than size for a decoder in an
#                                 interpreter (-Oz sizes are printed with MEDIA_OZ=1)
set -euo pipefail
WORK=${1:-$HOME/working/media-wasm}
HERE=$(cd "$(dirname "$0")" && pwd)
EMCC=${EMCC:-/opt/homebrew/bin/emcc}
EMCONFIGURE=${EMCONFIGURE:-/opt/homebrew/bin/emconfigure}
EMMAKE=${EMMAKE:-/opt/homebrew/bin/emmake}
OPT=${OPT:--O2}

fetch() { # url file sha256
  local url=$1 file=$WORK/$2 sum=$3
  [ -f "$file" ] || curl -sSfL -o "$file" "$url"
  local got; got=$(shasum -a 256 "$file" | cut -d' ' -f1)
  if [ "$got" != "$sum" ]; then echo "$file: sha256 $got, expected $sum" >&2; exit 1; fi
  [ -d "$WORK/${2%.tar.gz}" ] || tar xzf "$file" -C "$WORK"
}

mkdir -p "$WORK"
fetch https://downloads.xiph.org/releases/opus/opus-1.5.2.tar.gz opus-1.5.2.tar.gz \
  65c1d2f78b9f2fb20082c38cbe47c951ad5839345876e46941612ee87f9a7ce1
fetch https://downloads.xiph.org/releases/ogg/libogg-1.3.5.tar.gz libogg-1.3.5.tar.gz \
  0eb4b4b9420a0f51db142ba3f9c64b333f826532dc0f48c6410ae51f4799b664
fetch https://downloads.xiph.org/releases/vorbis/libvorbis-1.3.7.tar.gz libvorbis-1.3.7.tar.gz \
  0e982409a9c3fc82ee06e08205b1355e5c6aa4c36bca58146ef399621b0ce5ab
fetch https://github.com/webmproject/libvpx/archive/refs/tags/v1.15.2.tar.gz libvpx-1.15.2.tar.gz \
  26fcd3db88045dee380e581862a6ef106f49b74b6396ee95c2993a260b4636aa

LINK=(-sSTANDALONE_WASM --no-entry -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=4MB -mno-simd128)
size() { echo "$1: $(wc -c < "$1" | tr -d ' ') bytes"; }

# --- Opus: the source lists of opus_sources.mk, celt_sources.mk, silk_sources.mk.
mklist() { # file variable
  sed -n "/^$2 = /,/^\$/p" "$1" | sed -e "s/^$2 = //" -e 's/\\$//' | tr -s ' \t' '\n' | grep '\.c$' || true
}
OPUS=$WORK/opus-1.5.2
OBJ=$WORK/obj-opus; rm -rf "$OBJ"; mkdir -p "$OBJ"
srcs=$( (mklist "$OPUS/celt_sources.mk" CELT_SOURCES; mklist "$OPUS/silk_sources.mk" SILK_SOURCES
         mklist "$OPUS/silk_sources.mk" SILK_SOURCES_FLOAT; mklist "$OPUS/opus_sources.mk" OPUS_SOURCES
         mklist "$OPUS/opus_sources.mk" OPUS_SOURCES_FLOAT) )
objs=()
for s in $srcs; do
  o=$OBJ/$(echo "$s" | tr / _).o
  "$EMCC" "$OPT" -mno-simd128 -DOPUS_BUILD -DUSE_ALLOCA -DHAVE_LRINTF -DHAVE_LRINT \
    -I"$OPUS/include" -I"$OPUS/celt" -I"$OPUS/silk" -I"$OPUS/silk/float" -I"$OPUS" \
    -c "$OPUS/$s" -o "$o"
  objs+=("$o")
done
"$EMCC" "$OPT" -mno-simd128 -I"$OPUS/include" -c "$HERE/media/opus_entry.c" -o "$OBJ/entry.o"
"$EMCC" "$OPT" "${objs[@]}" "$OBJ/entry.o" "${LINK[@]}" -o "$WORK/opus-wasmvm.wasm"
size "$WORK/opus-wasmvm.wasm"

# --- Vorbis: libogg (bitwise.c, framing.c) and the libvorbis decoder files.
OGG=$WORK/libogg-1.3.5; VOR=$WORK/libvorbis-1.3.7
OBJ=$WORK/obj-vorbis; rm -rf "$OBJ"; mkdir -p "$OBJ/ogg"
cat > "$OBJ/ogg/config_types.h" <<'EOF'
#ifndef __CONFIG_TYPES_H__
#define __CONFIG_TYPES_H__
#include <stdint.h>
typedef int16_t ogg_int16_t;
typedef uint16_t ogg_uint16_t;
typedef int32_t ogg_int32_t;
typedef uint32_t ogg_uint32_t;
typedef int64_t ogg_int64_t;
typedef uint64_t ogg_uint64_t;
#endif
EOF
objs=()
for s in "$OGG/src/bitwise.c" "$OGG/src/framing.c" \
         $(for f in mdct smallft block envelope window lsp lpc analysis synthesis psy info \
                    floor1 floor0 res0 mapping0 registry codebook sharedbook lookup bitrate; do
             echo "$VOR/lib/$f.c"; done); do
  o=$OBJ/$(basename "$s" .c).o
  "$EMCC" "$OPT" -mno-simd128 -I"$OBJ" -I"$OGG/include" -I"$VOR/include" -I"$VOR/lib" -c "$s" -o "$o"
  objs+=("$o")
done
"$EMCC" "$OPT" -mno-simd128 -I"$OBJ" -I"$OGG/include" -I"$VOR/include" -c "$HERE/media/vorbis_entry.c" -o "$OBJ/entry.o"
"$EMCC" "$OPT" "${objs[@]}" "$OBJ/entry.o" "${LINK[@]}" -o "$WORK/vorbis-wasmvm.wasm"
size "$WORK/vorbis-wasmvm.wasm"

# --- VP8: libvpx configured for a generic target, decoder only.
VPX=$WORK/libvpx-1.15.2
B=$WORK/build-vpx
if [ ! -f "$B/libvpx.a" ]; then
  rm -rf "$B"; mkdir -p "$B"
  (cd "$B" && "$EMCONFIGURE" "$VPX/configure" --target=generic-gnu --disable-vp8-encoder \
     --disable-vp9 --enable-vp8-decoder --disable-examples --disable-tools --disable-docs \
     --disable-unit-tests --disable-multithread --disable-runtime-cpu-detect \
     --disable-webm-io --disable-libyuv --extra-cflags="$OPT -mno-simd128 -sSUPPORT_LONGJMP=wasm" >/dev/null \
   && "$EMMAKE" make -j4 >/dev/null)
fi
OBJ=$WORK/obj-vp8; rm -rf "$OBJ"; mkdir -p "$OBJ"
"$EMCC" "$OPT" -mno-simd128 -I"$VPX" -I"$B" -c "$HERE/media/vp8_entry.c" -o "$OBJ/entry.o"
"$EMCC" "$OPT" "$OBJ/entry.o" "$B/libvpx.a" "${LINK[@]}" -sSUPPORT_LONGJMP=wasm -o "$WORK/vp8-wasmvm.wasm"
size "$WORK/vp8-wasmvm.wasm"

if command -v wasm-tools >/dev/null; then
  for m in opus vorbis vp8; do
    echo "$m imports:"; wasm-tools print "$WORK/$m-wasmvm.wasm" | grep '(import ' | sed 's/^ */  /'
  done
fi
