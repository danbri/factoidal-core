# 2026-11-28 — Require explicit execution fixture metadata

Issue #1219, parent #725/#652. Base `d487f8005029aefb5b0a7d3bcd70c287f1072834` (#1236).
The pinned consensus-specs v1.6.1 operation format and Bellatrix/Deneb
generators require an explicit boolean mapping for execution-payload
operation fixtures. The previous parser accepted prefixes and defaulted
missing or unrecognised metadata to true. The actual operation runner now
calls a restricted complete-mapping parser and throws a harness error
before transition if it cannot read an explicit boolean. Block vectors
retain the documented test-only assumption. Four positive and twelve
negative closed-value controls are included in the compiled harness.

This change does not implement independent execution-layer verification.
No protocol transition, theorem statement, import, native audit, test
inventory or acceptance threshold changes. The existing two payload
refusal theorems and all 8,883 vectors must recheck on this exact source.
Local compiler unavailable; no new kernel or native pass claimed.
