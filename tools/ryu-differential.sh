#!/usr/bin/env bash
# Number::toString of BubblePopJS (Ryū, JS/Ryu.lean) against its exact reference, Node and
# QuickJS-NG, on N random doubles plus the fixed edge cases of `leanjs numfmt-diff`.
# Issue https://github.com/danbri/factoidal-core/issues/1076.
#   tools/ryu-differential.sh LEANJS N SEED [QJS]
# Exit 0 when every engine agrees with every line; 1 otherwise.
set -u
here=$(cd "$(dirname "$0")" && pwd)
leanjs=$1; n=$2; seed=$3; qjs=${4:-}
out=$(mktemp); rc=0
"$leanjs" numfmt-diff "$n" "$seed" "$out" || rc=1
cp "$here/ryu-differential/check.js" "$here/ryu-differential/check.mjs"
node "$here/ryu-differential/node-main.mjs" "$out" || rc=1
if [ -n "$qjs" ]; then "$qjs" -m "$here/ryu-differential/qjs-main.js" "$out" || rc=1; fi
rm -f "$out" "$here/ryu-differential/check.mjs"
exit $rc
