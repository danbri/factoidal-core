# Textarea cloning worknote, 26 November 2026

Prepared on exact main `21a8f7532d4afdadc04603cdf6a8ae893ea15d9f` for a draft PR.
[Design, specification, pinned WPT evidence and validation boundary](designissues/2026-11-26-textarea-cloning.md).

Implemented independent textarea live state, clean clone snapshots, dirty flag copying,
mutation/reset integration and the shared host ABI. Added ten Lean guard expressions and
six prelude source-boundary tests. The source tests pass 6/6; JavaScript and shell syntax
checks pass. Lean compilation, the printed axiom report, package tests and candidate WPT
results are pending cloud CI. No local heavy build was started.
