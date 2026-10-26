#!/usr/bin/env bash
# tests/trig-pack/compare_w3c.sh — TriG shard pack: chunk route against the
# whole-source route (https://github.com/danbri/factoidal/issues/769).
#
# For every .trig file of the W3C RDF 1.1 and 1.2 TriG suites and each wire
# format (ibk4 on 1.1 files, ibk5 on both), packs with
#   batch  L4_PACK_BUFFERED=1   (PackStream.quadArtifacts, whole source)
#   chunk  default 65,536-byte chunks
#   tiny   L4_PACK_CHUNK_BYTES=7 (chunk boundaries inside tokens)
# and compares the exit status and the generation hash (sha256 of the sorted
# per-file sha256 list). Prints labelled counts. Exit 0 only when every file
# agrees. Env: PACK (binary), OUT (scratch dir).
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
PACK=${PACK:-$ROOT/formal/lean4/.lake/build/bin/l4block-shard-pack}
OUT=${OUT:-$(mktemp -d)}
gen_hash() { (cd "$1" && find . -type f | sort | xargs sha256sum | sha256sum | cut -d' ' -f1); }
# Known expected failure, https://github.com/danbri/factoidal/issues/836 : default-graph
# blocks after named blocks. Its hash MUST differ; if it agrees, the run is RED.
KNOWN=trig-syntax-minimal-whitespace-01.trig
same=0; diff=0; xfail=0; xpass=0; bothfail=0; mismatch_status=0; total=0
for dir in rdf11/rdf-trig rdf12/rdf-trig; do
  for f in "$ROOT"/third_party/testing/w3c/rdf/$dir/*.trig; do
    for fmt in ibk4 ibk5; do
      [ "$fmt" = ibk4 ] && [ "$dir" = rdf12/rdf-trig ] && continue
      total=$((total+1))
      declare -A H=(); declare -A R=()
      for route in batch chunk tiny; do
        d="$OUT/$route"; rm -rf "$d"
        case $route in
          batch) L4_PACK_BUFFERED=1 "$PACK" "$f" "$d" $fmt >/dev/null 2>&1; rc=$?;;
          chunk) "$PACK" "$f" "$d" $fmt >/dev/null 2>&1; rc=$?;;
          tiny) L4_PACK_CHUNK_BYTES=7 "$PACK" "$f" "$d" $fmt >/dev/null 2>&1; rc=$?;;
        esac
        R[$route]=$rc
        if [ $rc -eq 0 ]; then H[$route]=$(gen_hash "$d"); else H[$route]=fail; fi
      done
      if [ "${R[batch]}" != "${R[chunk]}" ] || [ "${R[batch]}" != "${R[tiny]}" ]; then
        mismatch_status=$((mismatch_status+1)); echo "STATUS-DIFF $fmt $f batch=${R[batch]} chunk=${R[chunk]} tiny=${R[tiny]}"
      elif [ "${R[batch]}" != 0 ]; then bothfail=$((bothfail+1))
      elif [ "${H[batch]}" = "${H[chunk]}" ] && [ "${H[batch]}" = "${H[tiny]}" ]; then
        same=$((same+1)); [ "$(basename "$f")" = "$KNOWN" ] && { xpass=$((xpass+1)); echo "XPASS $fmt $f agrees now; close issue 836 and remove KNOWN"; }
      elif [ "$(basename "$f")" = "$KNOWN" ] && [ "${H[chunk]}" = "${H[tiny]}" ]; then xfail=$((xfail+1)); echo "XFAIL (issue 836) $fmt $f"
      else diff=$((diff+1)); echo "HASH-DIFF $fmt $f batch=${H[batch]} chunk=${H[chunk]} tiny=${H[tiny]}"; fi
    done
  done
done
echo "trig-pack W3C: $total pack cases (file x format): $same identical generation hash, $xfail expected hash difference (issue 836), $diff unexpected hash difference, $xpass unexpected agreement, $bothfail refused by all three routes, $mismatch_status exit status differs"
[ $diff -eq 0 ] && [ $mismatch_status -eq 0 ] && [ $xpass -eq 0 ]
