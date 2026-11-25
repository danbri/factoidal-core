# Paired EVM CLI timings, 22 November 2026

The native Linux measurements compare the prior implementation at
`5f90c3e6f9f42dd51a4c6c0f0a218526ee8be834` with the CALL byte-window and
nested-execution implementation. The tested integration commit and the
published implementation have the same Git tree,
`7d2cbe6bbd1ccf1bb1abd3fb485d415c1f7bf944`.
[Prior source](https://github.com/danbri/factoidal-core/commit/5f90c3e6f9f42dd51a4c6c0f0a218526ee8be834) · [Published implementation](https://github.com/danbri/factoidal-core/commit/f9fec7cbc5213aef53c19b0561efd21abba7db0c)

Each pair alternates which executable runs first. Each sample includes
fresh process launch, execution and JSON output. The unrounded samples and
binary SHA-256 digests are in the two JSON reports.

| Path | Pairs | p50 before → after | p95 before → after | p99 before → after | Max before → after | Spread before → after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ABI frame call | 160 | 4.733 → 4.782 | 8.507 → 7.793 | 18.484 → 16.637 | 20.236 → 38.203 | 16.278 → 34.124 |
| Zero-window CALL with storage | 160 | 4.504 → 4.630 | 5.883 → 6.163 | 11.506 → 10.190 | 30.151 → 18.157 | 26.223 → 14.162 |
| 10,000-case raw opcode batch | 11 | 154.794 → 163.367 | 181.091 → 199.809 | 181.091 → 199.809 | 181.091 → 199.809 | 30.600 → 46.189 |

Times are milliseconds per process. Quantiles use nearest rank and spread
means maximum minus minimum. The 11 batch pairs give the maximum for both
p95 and p99. The batch median rose 5.54% and the spread widened. The ABI
frame maximum rose from 20.236 to 38.203 ms. Median paired deltas were
+0.041 ms for the ABI frame, +0.111 ms for the zero-window CALL and +4.325 ms
for the batch. Paired batch deltas ranged from −26.580 to +41.554 ms.
Performance investigation remains open. [Issue 739](https://github.com/danbri/factoidal-core/issues/739)

Every CLI pair returned identical values for all original JSON fields.
Every raw batch returned the same 2,071,386 bytes of JSONL, SHA-256
`86621eeda2458d6f5a8a5aaa157e21a09d188c3f253314ff67af38b33a677a0f`.
The raw input is the existing deterministic synthetic opcode corpus with
seed `20261119` and 10,000 cases.

## Reproduce

Build `evm-subset` in the two source checkouts with the pinned Lean toolchain.
Set `before_exe` and `after_exe` to those executable paths and set
`before_source` and `after_source` to the commit IDs in the reports.
From the EVM package directory, run the following commands in a quiet interval.

```sh
node scripts/differential/generate.mjs --seed 20261119 --count 10000 --out corpus.jsonl
python3 -c 'import json,sys; print("\n".join("\t".join(case[key] for key in ("hex","gas","fuel")) for case in map(json.loads,sys.stdin)))' < corpus.jsonl > corpus.tsv
flock /tmp/foafnaut-timing.lock node scripts/differential/byte-call-timing.mjs \
  "$before_exe" "$before_source" "$after_exe" "$after_source"
flock /tmp/foafnaut-timing.lock python3 scripts/differential/raw10000-timing.py \
  "$before_exe" "$before_source" "$after_exe" "$after_source" corpus.tsv corpus.jsonl
```

[Legacy CLI samples](legacy-cli-timing.json) · [Raw batch samples](raw10000-timing.json)
