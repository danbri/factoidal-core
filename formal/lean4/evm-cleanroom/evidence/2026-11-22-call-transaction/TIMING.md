# Native EVM call-transaction timings

The baseline is the native `evm-subset` built from local commit
`254c8329a8cd7da95b51901ba2091fa3ce43a97e`, whose Git tree matches the
published source. The paired runners alternate executable order. Every
sample comprises a fresh native process, execution and JSON output.
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
