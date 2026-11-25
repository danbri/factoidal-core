# Consensus retained source-pin repair — 2026-11-25

Issue #1128, parent #1120/#1085. Base b60a2dd98a0870312a45f984c884517f59f78bbe. Fresh proposer and attester runtime gates passed (jobs 139541659604 and 139541658800). Six retained BLS jobs stopped at source audits and the SSZ job stopped at the GIndex source pin after printing axioms (job 139541660163). These are failures, not retained native passes.

Five old/new source blobs were fetched at exact commits and compared by a single import substitution, with every other byte preserved:

- G1PublicKey: `d7e64f304280cb505f60252506e1500d3861f398` → `c046f6d470909b6b65f90d3eebd16eb9fb435806`
- G2Signature: `120832a8cf37cb82255e0b94e37551215725fe37` → `4e3762c7b67542bde20403c9952a65a901001242`
- PairingTarget: `2137b263efea22b0045c9cbc156807b28a82d9fa` → `c5dd9d71cc73b63212643087bbe3277847ecdbd6`
- HashToField: `5a187a3cdb8353e2d1a3fae9f552d5418e272e68` → `f504bf8ca4229ea13395326df484a1fd6d92164a`
- GIndex: `ec69368d7bf3d4ec1bbe533560ae93e3aaecbb2b` → `68292f05814e61ed0ad6007f155ddc9303c73f2d`

The six workflow import inventories now expect Init in place of Lean; their fixed arithmetic-source pins are updated where used. Two active attestation/slashing checker pins are updated. The original 23 November JSON ledgers and historical reports are untouched; the two new named copies retain all expected theorem axioms, theorem sources and all other source pins. The SSZ workflow selects the new copies. No protocol code, expected axioms, native comparator or trust policy changes.

Source controls performed before publication: exact import-only comparison on all five Lean files; reverse-substitution checks for the six workflow files; JSON theorem inventory and one-pin-only comparison on both ledger copies. These are source checks only. Fresh hosted compilation, theorem reports, falsification controls and native comparisons remain mandatory. Standalone runtime binary coverage remains a separate obligation. No main merge or release.
