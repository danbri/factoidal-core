#!/usr/bin/env bash
# Expected failure for https://github.com/danbri/factoidal/issues/836 :
# a default-graph block AFTER a named-graph block packs to different bytes on
# the chunk route (source order) and the whole-source route (default graph
# first). This case PASSES while they differ and turns the suite RED when
# they agree, so the flip to a real assertion cannot be forgotten.
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
PACK=${PACK:-$ROOT/formal/lean4/.lake/build/bin/l4block-shard-pack}
D=$(mktemp -d)
printf '<http://e/g> {<http://e/a> <http://e/p> <http://e/b> .}\n{<http://e/c> <http://e/q> <http://e/d> .}\n' > "$D/o.trig"
L4_PACK_BUFFERED=1 "$PACK" "$D/o.trig" "$D/b" ibk4 >/dev/null || { echo "xfail setup: batch pack failed"; exit 1; }
"$PACK" "$D/o.trig" "$D/c" ibk4 >/dev/null || { echo "xfail setup: chunk pack failed"; exit 1; }
hb=$(cd "$D/b" && find . -type f | sort | xargs sha256sum | sha256sum)
hc=$(cd "$D/c" && find . -type f | sort | xargs sha256sum | sha256sum)
rm -rf "$D"
if [ "$hb" != "$hc" ]; then echo "XFAIL (expected, issue 836): generation hashes differ"; exit 0
else echo "XPASS: hashes now agree; replace this case with an assertion and close https://github.com/danbri/factoidal/issues/836"; exit 1; fi
