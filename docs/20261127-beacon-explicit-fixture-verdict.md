# 2026-11-27 — Explicit beacon fixture execution verdict

Issue #1219; parent #725/#652. Base `e3468d30a0f6687118d3a24fc50d0a48bee76261`.

The Fulu payload transition previously consumed a Boolean with default true. The new context has no default verdict. The actual transition returns a distinct execution-unavailable error before inspecting a payload when no fixture verdict is present. Explicit fixture true/false retains the previous header checks and their ordering.

The official test harness explicitly supplies the operation-vector execution.yaml verdict and the previous assumption for block, finality and random vectors. Each decoded execution-payload operation additionally exercises the missing-verdict path; the harness must not count missing-verdict or control failure as expected protocol invalidity. This is fixture-only, not a production execution authority. The theorem inventory adds two statements about the actual payload transition; kernel checking and native runs are pending hosted CI.

No new imports, dependency, runtime proof search or toolchain changes. An independent EL block runner, authenticated parent state, computed commitments and payload-bound production admission remain required. Local source checks only; no native or theorem pass claimed.
