# Native EVM call-transaction timings

The baseline is the native `evm-subset` built from local commit
`254c8329a8cd7da95b51901ba2091fa3ce43a97e`. The published baseline has
byte-identical native Lean sources, Lake configuration and toolchain
pin. Its tree also contains updates to the axiom-audit script and proof
ledger. The paired runners alternate executable order. Every sample
comprises a fresh native process, execution and JSON output.
[Published baseline](https://github.com/danbri/factoidal-core/commit/d3843c42d3b9c6fea8e96c3d0eebd65890dbea4b)

## Initial build with the umbrella JSON import

The first candidate at local commit
`fb5812620c0feb2334fa016861baeab6f7f89879` used `Lean.Data.Json`, which
imports the Lean elaborator. The binary grew from 6,558,824 to 121,084,456
bytes. Native text grew from 3,860,933 to 79,111,972 bytes. The paired
run measured a large process-startup regression on both legacy paths.
Lean 4.33.1 generates a call to `lean_initialize` for an executable with
a runtime import under `Lean`. The linker trace showed the initializer
pulling in the compiler and elaborator even with the narrower
`Lean.Data.Json.Parser` and `Lean.Data.Json.Printer` imports.

| Path | Pairs | p50 before → after (ms) | p95 before → after (ms) | p99 before → after (ms) | Max before → after (ms) | Spread before → after (ms) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ABI frame call | 160 | 4.716 → 33.901 | 6.005 → 46.308 | 15.679 → 77.419 | 16.062 → 85.189 | 11.947 → 54.784 |
| Zero-window CALL with storage | 160 | 4.513 → 33.176 | 5.678 → 40.807 | 9.857 → 80.756 | 27.471 → 85.622 | 23.354 → 54.812 |
| 10,000-case raw opcode batch | 11 | 154.781 → 187.701 | 158.881 → 200.424 | 158.881 → 200.424 | 158.881 → 200.424 | 8.208 → 18.630 |

Quantiles use nearest rank. The 11 batch pairs give the maximum for both
p95 and p99. Spread is maximum minus minimum. Median paired deltas were
+28.955 ms, +28.496 ms and +34.453 ms. The legacy paths preserved every
original JSON field. Both executables returned the same 2,071,386 bytes
of raw opcode JSONL, SHA-256
`86621eeda2458d6f5a8a5aaa157e21a09d188c3f253314ff67af38b33a677a0f`.
[Initial CLI samples](elaborator-import-regression/legacy-cli-timing.json) ·
[Initial raw batch samples](elaborator-import-regression/raw10000-timing.json) ·
[Initial run environment](elaborator-import-regression/environment.log)

## Split native entry points

The split build uses the regular lightweight Lean runtime in `evm-subset`
and the standard Lean JSON parser and full runtime in
`evm-call-transaction`. The executables occupy 6,653,936 and 120,842,224
bytes respectively. Only transaction requests start the companion. The
second paired run resampled the same baseline and used the split
`evm-subset` compiled from local integration commit
`ff345ca6e922fb2e96394de436804bee6c5b7f77`, Git tree
`d598cd08b0c87ce19def66b50b23f8be78174711`. Both executable digests are
recorded in the active evidence and the timing paths use only `evm-subset`.
[Native executable pins](../active-claim-manifest-v2.json) ·
[Published checkpoint with the same native source](https://github.com/danbri/factoidal-core/commit/c1e119557f75bd262d9c3c84b3195178f27c3e83)

| Path | Pairs | p50 before → after (ms) | p95 before → after (ms) | p99 before → after (ms) | Max before → after (ms) | Spread before → after (ms) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ABI frame call | 160 | 4.303 → 4.392 | 6.640 → 5.901 | 10.432 → 10.292 | 24.783 → 15.889 | 20.890 → 11.853 |
| Zero-window CALL with storage | 160 | 4.275 → 4.321 | 5.311 → 6.104 | 16.714 → 15.060 | 25.548 → 31.010 | 21.654 → 27.068 |
| 10,000-case raw opcode batch | 11 | 164.644 → 174.384 | 240.126 → 240.266 | 240.126 → 240.266 | 240.126 → 240.266 | 88.075 → 84.044 |

Median paired deltas were +0.055 ms for the ABI frame, +0.072 ms for the
zero-window CALL and +2.534 ms for the batch. The corresponding median
levels rose 2.08%, 1.09% and 5.92%. The CALL p95 and maximum increased.
The small batch sample had a +64.890 ms maximum paired delta. Every
legacy field comparison and the raw 2,071,386-byte JSONL comparison
passed. Remaining performance investigation stays open.
[Legacy CLI samples](legacy-cli-timing.json) ·
[Raw batch samples](raw10000-timing.json) ·
[Split run environment](timing-environment.log) ·
[Original split run script](timing-commands.sh) ·
[Reproduce from public commits](#reproduce-from-public-commits) ·
[Issue 739](https://github.com/danbri/factoidal-core/issues/739)

## Reproduce from public commits

Use the pinned Lean 4.33.1 toolchain on Linux. Set `before_checkout`
and `after_checkout` to the absolute paths of checkouts at the specified
public commits. The archived run script and raw reports preserve the
original local commit IDs and paths. The following commands regenerate
and hash-check the input, then run 160 pairs per legacy CLI path and
11 pairs for the full raw batch. The runners set these counts internally.

```bash
before_source=d3843c42d3b9c6fea8e96c3d0eebd65890dbea4b
after_source=c1e119557f75bd262d9c3c84b3195178f27c3e83
test "$(git -C "$before_checkout" rev-parse HEAD)" = "$before_source"
test "$(git -C "$after_checkout" rev-parse HEAD)" = "$after_source"
(cd "$before_checkout/formal/lean4" && lake -d evm-cleanroom build evm-subset)
(cd "$after_checkout/formal/lean4" && lake -d evm-cleanroom build evm-subset evm-call-transaction)
before_exe="$before_checkout/formal/lean4/evm-cleanroom/.lake/build/bin/evm-subset"
after_exe="$after_checkout/formal/lean4/evm-cleanroom/.lake/build/bin/evm-subset"
cd "$after_checkout/formal/lean4/evm-cleanroom"
results=$(mktemp -d)
node scripts/differential/generate.mjs --seed 20261119 --count 10000 --out "$results/corpus.jsonl"
python3 -c 'import json,sys; print("\n".join("\t".join(case[key] for key in ("hex","gas","fuel")) for case in map(json.loads,sys.stdin)))' \
  < "$results/corpus.jsonl" > "$results/corpus.tsv"
sha256sum --check <<EOF
610012bd5b278c5e4d08545560beed11910e01c0233ad8f9c9a4c9a52e0a2efb  $results/corpus.jsonl
aa2533e3fa8b1d2907e5c84933956e207a53e2b0a674e1d8bef716b1afc99ea0  $results/corpus.tsv
EOF
(
  flock -x 9
  node scripts/differential/byte-call-timing.mjs \
    "$before_exe" "$before_source" "$after_exe" "$after_source" > "$results/legacy-cli-timing.json"
  python3 scripts/differential/raw10000-timing.py \
    "$before_exe" "$before_source" "$after_exe" "$after_source" \
    "$results/corpus.tsv" "$results/corpus.jsonl" > "$results/raw10000-timing.json"
) 9>/tmp/foafnaut-timing.lock
```
