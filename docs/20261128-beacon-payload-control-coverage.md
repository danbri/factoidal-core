# 2026-11-28 — Count actual missing-verdict controls

Issue #1219; parent #725/#652. Base #1237 `4d0bc6acfe3cabadec4de68efcc63b9be9feb5b8`.
The actual payload-operation runner now decodes the operation once and executes
the absent-verdict control on the same decoded body and prestate before running
the timed fixture transition. A case-local reference records passed, failed,
body-decode-refused or not-reached coverage; no shared mutable counter. A failed
control throws a harness error, never an expected protocol-invalid result.
SSZ decoding refusal retains the existing invalid-fixture semantics.
The JSON report partitions every handler's cases; the ratchet requires positive
control coverage and no failed or unreached controls for execution_payload, with
all other handler and BLS baseline checks retained. Eight negative ratchet
controls and a positive mixed decode/execute case are added. Exact counts
remain to be observed; no normative EL admission or new theorem claim.
The measured payload transition no longer includes the negative control.
No protocol, dependency, native startup, proof or baseline changes.
Fresh hosted native/vector/proof gates are required; local Lean unavailable.
