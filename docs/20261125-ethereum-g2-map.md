# Independent Ethereum G2 map — 25 November 2026

Tracks #1013 and #725. Owned branch `wip/ethereum-g2-map-20261125-0500`, stacked on #1009 at `1c48f899391e67b565e66607e42d924a455fbe52`. No predecessor branch or EL file edited. EL identity CALL/transaction integration #839 remains separately owned, current head 60995cd75a425fcde5eea20281f074f57605ae6a.

## Confirmed predecessor

Actual Linux job https://github.com/danbri/factoidal-core/actions/runs/45544702426/job/138971391682 passed all steps. Merge commit 017dd86ac167ebfba727c926fb232c930be8d7da, tree f5cf6d157fb6fcbf37e29d17f41834efa9b43cfa. Lean 4.33.1 compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 222 native hash-to-field rows passed (80.078 ms batch); all seven selected reports depend on propext and Quot.sound. Five comparator and four axiom audit controls detected. Source pins and symbol/import checks passed. These results are predecessor evidence, not fresh results on the new tree.

## Implementation

Normative reference: RFC 9380 §§6.6.2–6.6.3, 8.8.2 and E.3/J.10.1, https://www.rfc-editor.org/rfc/rfc9380.html. The actual map uses norm-based Fp2 square-root recovery (reused repository-owned arithmetic from G2Signature.lean, no explicit imports beyond Lean), Fermat inversion in Fp, parity sign, exceptional SSWU denominator selection, Horner evaluation of the four rational-map polynomials, explicit infinity result when either isogeny denominator is zero, and checked finite output on the target curve. The signing-root entry feeds both concrete SHA-XMD-derived field values into that map. It returns two points before addition or cofactor clearing; no BLS verdict or authenticated state transition. No secret inputs or shipping signer path.

The test-only independent JavaScript oracle uses full extension-field exponentiation for inversion, Tonelli–Shanks for square roots and direct power-sum polynomial evaluation. Its exact map generator executed in the isolated JS environment on 83 direct rows (75 canonical, 8 rejection expectations, of which three concern root transport); it matched both published RFC empty-message Q0/Q1 points (eight coefficients), with 35 first-candidate and 40 second-candidate selections, one exceptional SSWU denominator. Rejection expectations are generated, not native comparisons. The full hosted oracle adds 19 signing roots with independent Node SHA-256 XMD and five comparator mutation controls; fresh CI will run 102 rows and all 222 retained hash-field rows. The full Node script and native Lean build have not executed locally: Lean/Codex and shared Mac access are absent in this container. Native build, actual seven new and seven retained axiom reports, source and native-link audits, and regression verdicts are pending.

## Exact source pins

Source commit e7a0e1c74d91a9840d41b8547d521e7060c0401a:
- HashToField.lean 88bcf4e2686e97707ad7e8a5d01cc74131b5e592
- G2Signature.lean 9a135cce63739f5e62017e98bd76a888b0d89306
- scripts/check-g2-map.mjs ba7bf058421444e876566406bf96175464a947e5
- .github/workflows/ethereum-bls-g2-map.yml 550bcc5bcff293e65a9322b79136b203e9dc5ea8
- SHA2.lean 92737f4d83035745dba29ef2c3867b01b8dfa50f
- lean-toolchain a8afa7d1b02d96f0671eba854a8dc4b416beb473
- lake-manifest.json 15728fe01a01ed2369565ec5be9afdf6abcf2f91
- lakefile.toml b08203129886735a8fbfc2c31fb7027024665d1f

The new gate preserves the original seven hash-field reports and oracle, adds exact map theorem inventory, audits source and native symbols and retains the empty package manifest. Compiler/runtime and host transport remain trusted; no constant-time or cryptographic security claim. Field/isogeny refinement, completeness, subgroup/cofactor clearing, BLS pairing-product authentication, full consensus and execution remain open. No merge or release.
