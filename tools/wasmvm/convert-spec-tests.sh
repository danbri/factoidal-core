#!/usr/bin/env bash
# Regenerate third_party/wasm-spec/test/core-json/ from the vendored
# WebAssembly spec tests in third_party/wasm-spec/test/core/.
#
# Each <rel>/<name>.wast becomes core-json/<rel>/<name>/<name>.json plus the
# .wasm (and, for text-only modules, .wat) files that the JSON names.
# Primary tool: wasm-tools json-from-wast (Bytecode Alliance).
# Fallback, per file, only when wasm-tools fails: wabt wast2json --enable-all.
# The outcome of every file is written to core-json/conversion-log.tsv.
#
# Usage: tools/wasmvm/convert-spec-tests.sh   (from the repository root)
# Needs: wasm-tools; wast2json for the fallback (brew install wasm-tools wabt).
set -u
ROOT=$(git rev-parse --show-toplevel)
SRC="$ROOT/third_party/wasm-spec/test/core"
OUT="$ROOT/third_party/wasm-spec/test/core-json"
command -v wasm-tools >/dev/null || { echo "wasm-tools not found" >&2; exit 2; }
HAVE_WABT=0; command -v wast2json >/dev/null && HAVE_WABT=1

rm -rf "$OUT"; mkdir -p "$OUT"
LOG="$OUT/conversion-log.tsv"
{
  printf '# wasm-tools %s\n' "$(wasm-tools --version | awk '{print $2}')"
  [ $HAVE_WABT = 1 ] && printf '# wabt wast2json %s\n' "$(wast2json --version)"
  printf 'file\ttool\tresult\terror\n'
} > "$LOG"

ok=0; fb=0; bad=0
while IFS= read -r wast; do
  rel=${wast#"$SRC"/}; rel=${rel%.wast}; name=$(basename "$rel")
  dir="$OUT/$rel"; mkdir -p "$dir"
  ERR=$(cd "$dir" && wasm-tools json-from-wast "$wast" -o "$name.json" --wasm-dir . 2>&1)
  RC=$?
  if [ $RC = 0 ]; then
    printf '%s\twasm-tools\tok\t\n' "$rel.wast" >> "$LOG"; ok=$((ok+1)); continue
  fi
  WT_ERR=$(printf '%s' "$ERR" | tr '\n\t' '  ' | cut -c1-400)
  rm -rf "$dir"; mkdir -p "$dir"
  if [ $HAVE_WABT = 1 ]; then
    ERR2=$(cd "$dir" && wast2json --enable-all "$wast" -o "$name.json" 2>&1)
    RC2=$?
    if [ $RC2 = 0 ]; then
      printf '%s\twast2json\tok (wasm-tools failed)\t%s\n' "$rel.wast" "$WT_ERR" >> "$LOG"; fb=$((fb+1)); continue
    fi
    WT_ERR="wasm-tools: $WT_ERR | wast2json: $(printf '%s' "$ERR2" | tr '\n\t' '  ' | cut -c1-400)"
  fi
  rm -rf "$dir"
  printf '%s\tnone\tFAILED\t%s\n' "$rel.wast" "$WT_ERR" >> "$LOG"; bad=$((bad+1))
done < <(find "$SRC" -name '*.wast' | LC_ALL=C sort)

echo "converted with wasm-tools: $ok; with wast2json fallback: $fb; failed: $bad"
echo "log: $LOG"
