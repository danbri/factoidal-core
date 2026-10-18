#!/usr/bin/env bash
#
# tests/delta-log/run.sh — what each delta log reader does with the bytes
# after the committed batches (https://github.com/danbri/factoidal/issues/843).
#
# Only a crash artifact at the end of the log is a torn tail: the final frame
# is cut short, or it is complete and fails its checksum. A frame that fails its
# checksum with more bytes after it (damaged), and a committed frame whose
# checksum verifies but whose entries the reader cannot decode (undecodable),
# are errors. Until 2026-10-14 `l4sbm11 query`, `serve` and `compact` used the
# batches before such a frame with exit 0 and no message, so the frame and
# every later batch were lost (the compaction folded only the batches before
# it). The rule is `Storage.classifyTail` and `parseLogChecked`
# (formal/lean4/L4Factoidal/Storage/DeltaLog.lean); the theorems are section 7
# of `Storage/BrowserLogTheorems.lean`; the browser log is tested in
# npm/factoidal/test/delta-log.test.mjs.
#
#   SBM11  the gate fixture (tests/sbm11/gate/gate.nq) packed and activated,
#          three batches by `l4sbm11 update`, then copies of the log:
#          torn (the last frame cut by 4 bytes; the last frame with one body
#          byte changed): query, serve and compact answer with the first two
#          batches, exit 0, and stderr says "torn final frame left out";
#          damaged (one body byte of batch 2 changed), undecodable at the end
#          and in the middle: query, serve, compact and update exit non-zero
#          and name the frame.
#   DLOG versions (https://github.com/danbri/factoidal/issues/792 item 1 and
#          https://github.com/danbri/factoidal/issues/856): the clean SBM11 log
#          with its header set to version 2, and to version 3, is read as before
#          and takes an append; the IBK3 log with version 2 or 3 is refused by
#          query, compact and update (`--inspect` reads it; activation reads a
#          DLOG only as the source of a compacted generation, after the
#          compaction that refuses it); a version 4 header is refused by every
#          SBM11 command.
#   IBK3   a small Turtle file packed and activated, two batches by
#          `l4block-delta-log`, then the same copies: `--inspect` names the
#          tail kind; the torn copy keeps the IBK3 rule (the query refuses a
#          log with a torn final frame until it is removed); the damaged and
#          undecodable copies are refused by query, compact and update with
#          the frame named.
#
# Usage: tests/delta-log/run.sh   (needs the l4sbm11, l4sbm11-pack,
# l4block-shard-pack, l4block-shard-activate, l4block-delta-log,
# l4block-id-v3-query and l4block-shard-compact binaries of this checkout).
# Prints "N pass, M fail (out of T)"; exit 0 only when every check passes.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${DELTA_LOG_BIN:-$ROOT/formal/lean4/.lake/build/bin}"   # DELTA_LOG_BIN: other binaries
for need in l4sbm11 l4sbm11-pack l4block-shard-pack l4block-shard-activate \
    l4block-delta-log l4block-id-v3-query l4block-shard-compact; do
  if [ ! -x "$BIN/$need" ]; then echo "missing: $BIN/$need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/delta-log-run.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
DLOG="python3 -I $HERE/dlog.py"
PASS=0; FAIL=0
record() { # record <part> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok   %-6s %-40s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL %-6s %-40s %s\n' "$1" "$2" "$4"; fi
}
has() { grep -q -- "$2" "$1"; }

# ---------------------------------------------------------------- SBM11
echo "=== SBM11"
S="$TMP/sbm11"
rc=0
"$BIN/l4sbm11-pack" "$ROOT/tests/sbm11/gate/gate.nq" "$S/col/gen" --workers 1 >"$TMP/s-pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$S/col" gen >"$TMP/s-act.log" 2>&1 || rc=$?; }
for i in 1 2 3; do
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" update "$S/col" "INSERT DATA { <http://ex.org/n$i> <http://ex.org/name> \"N$i\" }" \
    >>"$TMP/s-upd.log" 2>&1 || rc=$?; }
done
if [ "$rc" -ne 0 ]; then
  record sbm11 setup 1 "exit $rc: $(tail -1 "$TMP/s-pack.log" "$TMP/s-act.log" "$TMP/s-upd.log" 2>/dev/null | tr '\n' ' ')"
else
  record sbm11 setup 0 "gate fixture, 3 batches"
  LOG="$S/col/gen/deltas.dlog"
  cp "$LOG" "$TMP/s-clean.dlog"
  NAMES='SELECT ?o WHERE { ?s <http://ex.org/name> ?o } ORDER BY ?o'
  # one copy of the collection per case; the log is replaced in each
  copy() { rm -rf "$TMP/s-case"; cp -a "$S/col" "$TMP/s-case"; cp "$1" "$TMP/s-case/gen/deltas.dlog"; }
  query_case() { # query_case <name> <log> <want: rows|error> <expected names or error text>
    copy "$2"
    local rc=0
    "$BIN/l4sbm11" query "$TMP/s-case" "$NAMES" >"$TMP/q.srj" 2>"$TMP/q.err" || rc=$?
    local got
    got="$(grep -o '"value":"N[0-9]"' "$TMP/q.srj" | tr -d '"' | sed 's/value://' | tr '\n' ' ')"
    if [ "$3" = rows ]; then
      if [ "$rc" -eq 0 ] && [ "$got" = "$4" ] && has "$TMP/q.err" "$5"; then
        record sbm11 "query-$1" 0 "exit 0; names: $got"
      else record sbm11 "query-$1" 1 "exit $rc; names: $got; $(tail -1 "$TMP/q.err")"; fi
    else
      if [ "$rc" -ne 0 ] && has "$TMP/q.err" "$4"; then
        record sbm11 "query-$1" 0 "exit $rc: $(tail -1 "$TMP/q.err" | head -c 120)"
      else record sbm11 "query-$1" 1 "exit $rc; names: $got; $(tail -1 "$TMP/q.err")"; fi
    fi
    # serve opens the same session: one query on stdin
    rc=0
    echo "$NAMES" | "$BIN/l4sbm11" serve "$TMP/s-case" >"$TMP/sv.out" 2>"$TMP/sv.err" || rc=$?
    if [ "$3" = rows ]; then
      if [ "$rc" -eq 0 ] && has "$TMP/sv.out" '"N2"' && ! has "$TMP/sv.out" '"N3"'; then
        record sbm11 "serve-$1" 0 "exit 0"
      else record sbm11 "serve-$1" 1 "exit $rc; $(tail -1 "$TMP/sv.err")"; fi
    else
      if [ "$rc" -ne 0 ] && has "$TMP/sv.err" "$4"; then record sbm11 "serve-$1" 0 "exit $rc"
      else record sbm11 "serve-$1" 1 "exit $rc; $(tail -1 "$TMP/sv.err")"; fi
    fi
    # compaction folds the committed batches, or refuses
    rc=0
    "$BIN/l4sbm11" compact "$TMP/s-case" "$TMP/s-case/gen2" >"$TMP/c.log" 2>&1 || rc=$?
    if [ "$3" = rows ]; then
      local dumped
      dumped="$("$BIN/l4sbm11" dump "$TMP/s-case/gen2" 2>/dev/null | grep -o '"N[0-9]"' | tr -d '"' | sort | tr '\n' ' ')"
      if [ "$rc" -eq 0 ] && [ "$dumped" = "$4" ] && has "$TMP/c.log" 'torn final frame left out'; then
        record sbm11 "compact-$1" 0 "exit 0; compacted names: $dumped"
      else record sbm11 "compact-$1" 1 "exit $rc; compacted names: $dumped; $(tail -1 "$TMP/c.log")"; fi
    else
      if [ "$rc" -ne 0 ] && has "$TMP/c.log" "$4" && [ ! -e "$TMP/s-case/gen2/manifest.sbm11" ]; then
        record sbm11 "compact-$1" 0 "exit $rc, no generation written"
      else record sbm11 "compact-$1" 1 "exit $rc; $(tail -1 "$TMP/c.log")"; fi
    fi
    # an update is refused after any tail (torn: the recovery decision is not the writer's)
    rc=0
    "$BIN/l4sbm11" update "$TMP/s-case" 'INSERT DATA { <http://ex.org/z> <http://ex.org/name> "Z" }' >"$TMP/u.log" 2>&1 || rc=$?
    local want_upd="$4"; [ "$3" = rows ] && want_upd='uncommitted suffix'
    if [ "$rc" -ne 0 ] && has "$TMP/u.log" "$want_upd"; then record sbm11 "update-$1" 0 "refused: $(head -c 100 "$TMP/u.log")"
    else record sbm11 "update-$1" 1 "exit $rc; $(tail -1 "$TMP/u.log")"; fi
  }
  # clean: all three batches
  copy "$TMP/s-clean.dlog"
  rc=0; "$BIN/l4sbm11" query "$TMP/s-case" "$NAMES" >"$TMP/q.srj" 2>"$TMP/q.err" || rc=$?
  got="$(grep -o '"value":"N[0-9]"' "$TMP/q.srj" | tr -d '"' | sed 's/value://' | tr '\n' ' ')"
  if [ "$rc" -eq 0 ] && [ "$got" = "N1 N2 N3 " ]; then record sbm11 query-clean 0 "names: $got"
  else record sbm11 query-clean 1 "exit $rc; names: $got"; fi
  # torn: the last frame cut by 4 bytes
  cp "$TMP/s-clean.dlog" "$TMP/s-cut.dlog"; $DLOG cut "$TMP/s-cut.dlog" 4
  query_case torn-cut "$TMP/s-cut.dlog" rows "N1 N2 " 'torn final frame left out'
  # torn: the last frame complete, one body byte changed (its checksum fails)
  cp "$TMP/s-clean.dlog" "$TMP/s-last.dlog"; $DLOG bump "$TMP/s-last.dlog" 3 9
  query_case torn-checksum "$TMP/s-last.dlog" rows "N1 N2 " 'torn final frame left out'
  # damaged: one body byte of batch 2 changed, batch 3 after it
  cp "$TMP/s-clean.dlog" "$TMP/s-mid.dlog"; $DLOG bump "$TMP/s-mid.dlog" 2 9
  query_case damaged "$TMP/s-mid.dlog" error 'damaged frame'
  # undecodable at the end: a committed frame with the unknown entry tag 9
  cp "$TMP/s-clean.dlog" "$TMP/s-unk.dlog"; $DLOG append-unknown "$TMP/s-unk.dlog" 4 1
  query_case undecodable-end "$TMP/s-unk.dlog" error 'cannot decode'
  # undecodable in the middle: the same frame, then a plain batch
  cp "$TMP/s-unk.dlog" "$TMP/s-unk2.dlog"
  $DLOG append-plain "$TMP/s-unk2.dlog" 5 1 http://ex.org/n4 http://ex.org/name N4
  query_case undecodable-middle "$TMP/s-unk2.dlog" error 'cannot decode'
fi

# ----------------------------------------------------------------- IBK3
echo "=== IBK3"
I="$TMP/ibk3"
mkdir -p "$I"
cat >"$I/in.ttl" <<'EOF'
<http://ex.org/a> <http://ex.org/name> "A" .
<http://ex.org/b> <http://ex.org/name> "B" .
<http://ex.org/a> <http://ex.org/knows> <http://ex.org/b> .
EOF
rc=0
"$BIN/l4block-shard-pack" "$I/in.ttl" "$I/col/gen-1" ibk3 >"$TMP/i-pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4block-shard-activate" "$I/col" gen-1 >"$TMP/i-act.log" 2>&1 || rc=$?; }
for i in 1 2; do
  [ "$rc" -eq 0 ] && { "$BIN/l4block-delta-log" "$I/col" --update "INSERT DATA { <http://ex.org/n$i> <http://ex.org/name> \"N$i\" }" \
    >>"$TMP/i-upd.log" 2>&1 || rc=$?; }
done
if [ "$rc" -ne 0 ]; then
  record ibk3 setup 1 "exit $rc: $(tail -1 "$TMP/i-pack.log" "$TMP/i-act.log" "$TMP/i-upd.log" 2>/dev/null | tr '\n' ' ')"
else
  record ibk3 setup 0 "3 triples, 2 batches"
  ILOG="$I/col/gen-1/deltas.dlog"
  cp "$ILOG" "$TMP/i-clean.dlog"
  IQ='SELECT ?o WHERE { ?s <http://ex.org/name> ?o }'
  icopy() { rm -rf "$TMP/i-case"; cp -a "$I/col" "$TMP/i-case"; cp "$1" "$TMP/i-case/gen-1/deltas.dlog"; }
  # clean: the query sees both batches
  icopy "$TMP/i-clean.dlog"
  rc=0; "$BIN/l4block-id-v3-query" "$TMP/i-case" --query "$IQ" >"$TMP/iq.out" 2>"$TMP/iq.err" || rc=$?
  if [ "$rc" -eq 0 ] && has "$TMP/iq.out" 'N1' && has "$TMP/iq.out" 'N2'; then record ibk3 query-clean 0 "N1 and N2 seen"
  else record ibk3 query-clean 1 "exit $rc; $(tail -1 "$TMP/iq.err")"; fi
  ibk3_case() { # ibk3_case <name> <log> <tail kind> <text the refusals name>
    icopy "$2"
    local rc=0
    "$BIN/l4block-delta-log" "$TMP/i-case/gen-1" --inspect >"$TMP/ii.out" 2>"$TMP/ii.err" || rc=$?
    if [ "$rc" -ne 0 ] && has "$TMP/ii.out" "tail=$3" && has "$TMP/ii.out" 'committed-batches=1'; then
      record ibk3 "inspect-$1" 0 "$(grep -o 'committed-batches=[0-9]*.*' "$TMP/ii.out")"
    else record ibk3 "inspect-$1" 1 "exit $rc; $(cat "$TMP/ii.out")"; fi
    rc=0
    "$BIN/l4block-id-v3-query" "$TMP/i-case" --query "$IQ" >"$TMP/iq.out" 2>"$TMP/iq.err" || rc=$?
    if [ "$rc" -ne 0 ] && has "$TMP/iq.err" "$4"; then record ibk3 "query-$1" 0 "refused, exit $rc"
    else record ibk3 "query-$1" 1 "exit $rc; $(tail -2 "$TMP/iq.err" | tr '\n' ' ')"; fi
    rc=0
    "$BIN/l4block-shard-compact" "$TMP/i-case/gen-1" "$TMP/i-case/gen-2" >"$TMP/ic.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ] && has "$TMP/ic.log" "$5"; then record ibk3 "compact-$1" 0 "refused, exit $rc"
    else record ibk3 "compact-$1" 1 "exit $rc; $(tail -1 "$TMP/ic.log")"; fi
    rc=0
    "$BIN/l4block-delta-log" "$TMP/i-case" --update 'INSERT DATA { <http://ex.org/z> <http://ex.org/name> "Z" }' >"$TMP/iu.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ] && has "$TMP/iu.log" "$6"; then record ibk3 "update-$1" 0 "refused, exit $rc"
    else record ibk3 "update-$1" 1 "exit $rc; $(tail -1 "$TMP/iu.log")"; fi
  }
  cp "$TMP/i-clean.dlog" "$TMP/i-cut.dlog"; $DLOG cut "$TMP/i-cut.dlog" 4
  ibk3_case torn "$TMP/i-cut.dlog" torn 'malformed DLOG sidecar' 'uncommitted suffix' 'torn or uncommitted suffix'
  cp "$TMP/i-clean.dlog" "$TMP/i-mid.dlog"; $DLOG bump "$TMP/i-mid.dlog" 1 9
  # batch 1 damaged: no committed batch before it
  icopy "$TMP/i-mid.dlog"
  rc=0; "$BIN/l4block-delta-log" "$TMP/i-case/gen-1" --inspect >"$TMP/ii.out" 2>"$TMP/ii.err" || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/ii.out" 'tail=damaged' && has "$TMP/ii.out" 'committed-batches=0'; then
    record ibk3 inspect-damaged 0 "$(grep -o 'committed-batches=[0-9]*.*' "$TMP/ii.out")"
  else record ibk3 inspect-damaged 1 "exit $rc; $(cat "$TMP/ii.out")"; fi
  rc=0; "$BIN/l4block-id-v3-query" "$TMP/i-case" --query "$IQ" >"$TMP/iq.out" 2>"$TMP/iq.err" || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/iq.err" 'damaged frame'; then record ibk3 query-damaged 0 "refused, exit $rc"
  else record ibk3 query-damaged 1 "exit $rc; $(tail -2 "$TMP/iq.err" | tr '\n' ' ')"; fi
  rc=0; "$BIN/l4block-shard-compact" "$TMP/i-case/gen-1" "$TMP/i-case/gen-2" >"$TMP/ic.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/ic.log" 'damaged frame'; then record ibk3 compact-damaged 0 "refused, exit $rc"
  else record ibk3 compact-damaged 1 "exit $rc; $(tail -1 "$TMP/ic.log")"; fi
  rc=0; "$BIN/l4block-delta-log" "$TMP/i-case" --update 'INSERT DATA { <http://ex.org/z> <http://ex.org/name> "Z" }' >"$TMP/iu.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/iu.log" 'damaged frame'; then record ibk3 update-damaged 0 "refused, exit $rc"
  else record ibk3 update-damaged 1 "exit $rc; $(tail -1 "$TMP/iu.log")"; fi
  # undecodable at the end, after batch 1 only
  cp "$TMP/i-clean.dlog" "$TMP/i-unk.dlog"; $DLOG cut "$TMP/i-unk.dlog" "$(( $(stat -c %s "$TMP/i-clean.dlog") - $($DLOG frames "$TMP/i-clean.dlog" | awk 'NR==2 {print $4}') ))"
  $DLOG append-unknown "$TMP/i-unk.dlog" 2 1
  ibk3_case undecodable "$TMP/i-unk.dlog" undecodable 'cannot decode' 'cannot decode' 'cannot decode'
fi

# --------------------------------------------------------- DLOG versions
# A DLOG of version 2 may hold RDF 1.2 terms (triple terms, directional
# literals; https://github.com/danbri/factoidal/issues/792 item 1). Every
# version 1 frame is a version 2 frame (`DeltaLogCodecTheorems.
# parseLog_v2_of_frames`), so the SBM11 tools read the clean SBM11 log with its
# header set to version 2 as before, and append to it. The readers of IBK3,
# IBK4 and IBK5 collections refuse version 2 (`parseLogCheckedV1`). Version 3
# (a graph named by a blank node, https://github.com/danbri/factoidal/issues/856)
# extends version 2 in the same way (`DeltaLogCodecTheorems.parseLog_v3_of_frames`):
# the SBM11 tools read it and append to it, the IBK readers refuse it. Every
# reader refuses version 4 at the header.
echo "=== DLOG versions"
if [ -s "$TMP/s-clean.dlog" ]; then
  cp "$TMP/s-clean.dlog" "$TMP/s-v2.dlog"; $DLOG set-version "$TMP/s-v2.dlog" 2
  copy "$TMP/s-v2.dlog"
  rc=0; "$BIN/l4sbm11" query "$TMP/s-case" "$NAMES" >"$TMP/q.srj" 2>"$TMP/q.err" || rc=$?
  got="$(grep -o '"value":"N[0-9]"' "$TMP/q.srj" | tr -d '"' | sed 's/value://' | tr '\n' ' ')"
  if [ "$rc" -eq 0 ] && [ "$got" = "N1 N2 N3 " ]; then record sbm11 query-version-2 0 "version 1 frames under a version 2 header; names: $got"
  else record sbm11 query-version-2 1 "exit $rc; names: $got; $(tail -1 "$TMP/q.err")"; fi
  rc=0; "$BIN/l4sbm11" update "$TMP/s-case" 'INSERT DATA { <http://ex.org/n4> <http://ex.org/name> "N4" }' >"$TMP/u.log" 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" query "$TMP/s-case" "$NAMES" >"$TMP/q.srj" 2>"$TMP/q.err" || rc=$?; }
  got="$(grep -o '"value":"N[0-9]"' "$TMP/q.srj" | tr -d '"' | sed 's/value://' | tr '\n' ' ')"
  if [ "$rc" -eq 0 ] && has "$TMP/u.log" 'log-version=2' && [ "$got" = "N1 N2 N3 N4 " ]; then
    record sbm11 update-version-2 0 "appended to the version 2 log; names: $got"
  else record sbm11 update-version-2 1 "exit $rc; names: $got; $(tail -1 "$TMP/u.log")"; fi
  cp "$TMP/s-clean.dlog" "$TMP/s-v3.dlog"; $DLOG set-version "$TMP/s-v3.dlog" 3
  copy "$TMP/s-v3.dlog"
  rc=0; "$BIN/l4sbm11" query "$TMP/s-case" "$NAMES" >"$TMP/q.srj" 2>"$TMP/q.err" || rc=$?
  got="$(grep -o '"value":"N[0-9]"' "$TMP/q.srj" | tr -d '"' | sed 's/value://' | tr '\n' ' ')"
  if [ "$rc" -eq 0 ] && [ "$got" = "N1 N2 N3 " ]; then record sbm11 query-version-3 0 "version 1 frames under a version 3 header; names: $got"
  else record sbm11 query-version-3 1 "exit $rc; names: $got; $(tail -1 "$TMP/q.err")"; fi
  rc=0; "$BIN/l4sbm11" update "$TMP/s-case" 'INSERT DATA { <http://ex.org/n4> <http://ex.org/name> "N4" }' >"$TMP/u.log" 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" query "$TMP/s-case" "$NAMES" >"$TMP/q.srj" 2>"$TMP/q.err" || rc=$?; }
  got="$(grep -o '"value":"N[0-9]"' "$TMP/q.srj" | tr -d '"' | sed 's/value://' | tr '\n' ' ')"
  if [ "$rc" -eq 0 ] && has "$TMP/u.log" 'log-version=3' && [ "$got" = "N1 N2 N3 N4 " ]; then
    record sbm11 update-version-3 0 "appended to the version 3 log; names: $got"
  else record sbm11 update-version-3 1 "exit $rc; names: $got; $(tail -1 "$TMP/u.log")"; fi
  cp "$TMP/s-clean.dlog" "$TMP/s-v4.dlog"; $DLOG set-version "$TMP/s-v4.dlog" 4
  query_case version-4 "$TMP/s-v4.dlog" error 'malformed or unsupported'
else
  record sbm11 versions 1 "the SBM11 setup failed"
fi
if [ -s "$TMP/i-clean.dlog" ]; then
  cp "$TMP/i-clean.dlog" "$TMP/i-v2.dlog"; $DLOG set-version "$TMP/i-v2.dlog" 2
  icopy "$TMP/i-v2.dlog"
  rc=0; "$BIN/l4block-delta-log" "$TMP/i-case/gen-1" --inspect >"$TMP/ii.out" 2>"$TMP/ii.err" || rc=$?
  if [ "$rc" -eq 0 ] && has "$TMP/ii.out" 'version=2 committed-batches=2' && has "$TMP/ii.out" 'tail=clean'; then
    record ibk3 inspect-version-2 0 "$(grep -o 'version=2 committed-batches=2.*' "$TMP/ii.out")"
  else record ibk3 inspect-version-2 1 "exit $rc; $(cat "$TMP/ii.out" "$TMP/ii.err")"; fi
  V2='header version 2'
  rc=0; "$BIN/l4block-id-v3-query" "$TMP/i-case" --query "$IQ" >"$TMP/iq.out" 2>"$TMP/iq.err" || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/iq.err" "$V2"; then record ibk3 query-version-2 0 "refused, exit $rc"
  else record ibk3 query-version-2 1 "exit $rc; $(tail -2 "$TMP/iq.err" | tr '\n' ' ')"; fi
  rc=0; "$BIN/l4block-shard-compact" "$TMP/i-case/gen-1" "$TMP/i-case/gen-2" >"$TMP/ic.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/ic.log" "$V2"; then record ibk3 compact-version-2 0 "refused, exit $rc"
  else record ibk3 compact-version-2 1 "exit $rc; $(tail -1 "$TMP/ic.log")"; fi
  rc=0; "$BIN/l4block-delta-log" "$TMP/i-case" --update 'INSERT DATA { <http://ex.org/z> <http://ex.org/name> "Z" }' >"$TMP/iu.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/iu.log" "$V2"; then record ibk3 update-version-2 0 "refused, exit $rc"
  else record ibk3 update-version-2 1 "exit $rc; $(tail -1 "$TMP/iu.log")"; fi
  cp "$TMP/i-clean.dlog" "$TMP/i-v3.dlog"; $DLOG set-version "$TMP/i-v3.dlog" 3
  icopy "$TMP/i-v3.dlog"
  V3='header version 3'
  rc=0; "$BIN/l4block-id-v3-query" "$TMP/i-case" --query "$IQ" >"$TMP/iq.out" 2>"$TMP/iq.err" || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/iq.err" "$V3"; then record ibk3 query-version-3 0 "refused, exit $rc"
  else record ibk3 query-version-3 1 "exit $rc; $(tail -2 "$TMP/iq.err" | tr '\n' ' ')"; fi
  rc=0; "$BIN/l4block-shard-compact" "$TMP/i-case/gen-1" "$TMP/i-case/gen-2" >"$TMP/ic.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/ic.log" "$V3"; then record ibk3 compact-version-3 0 "refused, exit $rc"
  else record ibk3 compact-version-3 1 "exit $rc; $(tail -1 "$TMP/ic.log")"; fi
  rc=0; "$BIN/l4block-delta-log" "$TMP/i-case" --update 'INSERT DATA { <http://ex.org/z> <http://ex.org/name> "Z" }' >"$TMP/iu.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ] && has "$TMP/iu.log" "$V3"; then record ibk3 update-version-3 0 "refused, exit $rc"
  else record ibk3 update-version-3 1 "exit $rc; $(tail -1 "$TMP/iu.log")"; fi
else
  record ibk3 versions 1 "the IBK3 setup failed"
fi

echo
echo "delta log tails: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
