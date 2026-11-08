#!/bin/bash
# Run the QuickJS-NG Test262 sample with the Lean JavaScript engine, for a comparison
# on the same files: tools/wasmvm/quickjs/test262-sample.py 500 1244 makes DIR (436
# self-contained files whose first line is "// expect: ..."; record
# docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").
# Usage: tools/leanjs/test262-sample.sh LEANJS DIR OUT
# Not in the repository: DIR (generated from Test262) and LEANJS (lake exe leanjs).
B=$1; D=$2; out=$3; pass=0; fail=0; : > "$out"
for f in $D/*.js; do
  exp=$(head -1 $f | sed 's|// expect: ||; s| ;.*||')
  res=$(timeout 20 $B run $f 2>&1); rc=$?
  ok=0
  case "$exp" in
    pass*) [ $rc -eq 0 ] && ok=1;;
    "negative "*) t=${exp#negative }; t=$(echo $t | tr -d ' '); echo "$res" | grep -q "^\(Uncaught \)\?$t" && ok=1;;
    async*) echo "$res" | grep -q "Test262:AsyncTestComplete" && ok=1;;
  esac
  if [ $ok -eq 1 ]; then pass=$((pass+1)); echo "PASS $f" >> $out; else fail=$((fail+1)); echo "FAIL $f $(head -1 $f | cut -d';' -f2) :: $(echo "$res" | tail -1 | cut -c1-120)" >> $out; fi
done
echo "pass $pass fail $fail"
