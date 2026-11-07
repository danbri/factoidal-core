#!/usr/bin/env bash
# Run one shard of Test262 through the upstream harness of VerifiedJS, with a
# time limit on each compile and each run: the harness has none.
# Usage: test262-shard.sh <verifiedjs checkout> <shard index> <shard count>
set -euo pipefail
root="$1"; index="$2"; count="$3"
cd "$root"
mkdir -p .wrap
mv .lake/build/bin/verifiedjs .wrap/verifiedjs.real
printf '#!/bin/sh\nexec timeout 20 %s/.wrap/verifiedjs.real "$@"\n' "$PWD" > .lake/build/bin/verifiedjs
chmod +x .lake/build/bin/verifiedjs
real="$(command -v wasmtime)"
printf '#!/bin/sh\nexec timeout 10 %s "$@"\n' "$real" > .wrap/wasmtime
chmod +x .wrap/wasmtime
export PATH="$PWD/.wrap:$PATH"
shard="tests/test262-shard-$index"
mkdir -p "$shard"
(cd tests/test262 && find test -type f \( -name '*.js' -o -name '*.case' \) | LC_ALL=C sort | awk -v i="$index" -v n="$count" 'NR % n == i') > "$shard.list"
rsync -a --files-from="$shard.list" tests/test262/ "$shard/"
rc=0
bash scripts/run_test262_compare.sh --full --suite-dir "$shard/test" --max-fail 100000000 || rc=$?
echo "SHARD_RC=$rc"
