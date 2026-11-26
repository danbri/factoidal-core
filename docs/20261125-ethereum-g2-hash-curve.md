# Independent Ethereum G2 hash-to-curve — 25 November 2026

Parent #725, work item #1015. Base #1014 at d326e64f048211e5cb1a97dd83aa29013258857c, specialised job 138989929610 passed. This branch is separate from the EL and prior CL work. No main merge.

## Executable path

RFC 9380 sections 3, 7, 8.8.2 and J.10.1: existing concrete SHA-256 XMD, hash-to-field, SSWU and isogeny feed two points to mixed Jacobian addition, then multiplication by the exact 636-bit effective cofactor, normalisation, target-curve check and 255-step subgroup check. Infinity stays distinct from internal invariant failure. Both generic message/DST and fixed POP 32-byte signing-root entry points use this path. The Jacobian formulas are reused from repository-owned G2Signature.lean, blob 9a135cce63739f5e62017e98bd76a888b0d89306; it imports only Lean. There is no new package, host cryptographic answer or runtime fallback. The pinned Lean 4.33.1 toolchain and empty manifest are unchanged.

Source blob HashToField.lean: 569ae35b0d319ff74f14fce322ef37bb62a78ae8. Oracle blob: c3c3d816beaf257f3b2423b5235cb46ad0b20e1c. Workflow blob: 745276d07e5fef70d28c2f1293549861a828baa4. Hosted workflow records actual checkout/tree and all audited source pins.

## Evidence and commands

A local independent Python affine model with modular inversion and a separate mixed-Jacobian model matched the RFC J.10.1 empty-message full point and agreed on 23/23 group cases (including infinity, cancellation, doubling and scalar-generated pairs); subgroup checks matched and changing h_eff to h_eff-1 was detected. This was model-only execution, 1.174 s in the isolated environment; no native Lean test or theorem result is inferred from it.

The updated Node test-only oracle uses independent Euclidean inversion and right-to-left affine scalar multiplication. It retains 102 map rows and adds 34 curve rows: 7 direct clearing cases, 19 POP roots, 2 full RFC known answers (empty message and abc), 6 rejection cases. It requires exact output and checks subgroup membership of finite oracle results. Six comparator mutation controls. Retain 222 hash-field rows and both axiom inventories.

Reproduce on the isolated consensus directory with the pinned toolchain: see .github/workflows/ethereum-bls-g2-map.yml for clean native compile, source and import audit, native linking and actual #print axioms. Run node scripts/check-g2-map.mjs --self-test, then node scripts/check-g2-map.mjs <native hash-field executable>. The workflow runs these and the retained hash-field suite.

Six new theorem statements: clearCheck_ok, clearMapped_ok, hashSigningRoot_error, hashSigningRoot_delegates, hashToCurve_error, hashToCurve_delegates (EthereumConsensus.BLS.G2Map). Native and kernel checks pending at submission; actual axiom sets must be obtained from the hosted job. No claim of normative universal group-law, field or RFC refinement, authenticated signing root, signature verification, complete consensus, or production performance. Lean compiler/runtime and host test transport remain trusted. The bounded scalar loops are 636 and 255 iterations; field exponentiation is bounded by existing 381-step loops. Full signature verification still needs compressed-point admission and pairing-product integration; authenticated consensus state transitions remain open.
