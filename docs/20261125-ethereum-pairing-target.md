# Independent pairing target field — 25 November 2026

Tracks #984 / #725, stacked on #977 at 08f3d1a10ad44d73012960055c602eb46d4db351. The preceding [actual G2 Linux job](https://github.com/danbri/factoidal-core/actions/runs/45505913523/job/138840981093) passed every step: 325/325 native comparisons in 1067.581611 ms, all six actual G2 theorem reports depend only on propext, five comparator controls and four theorem inventory controls. [Retained G1 job](https://github.com/danbri/factoidal-core/actions/runs/45505913591/job/138840982037) also passed all steps. These are predecessor results.

New pure Lean field arithmetic: six Fp2 coefficients in w, u²=-1, w⁶=1+u; bounded 36-term product with one wrap, right-to-left exponentiation with 4572-bit cap, full final exponent (p^12−1)/r and explicit zero input refusal. No signature or pairing verdict. EIP-2537 and CFRG pairing-friendly-curves tower define the basis. The independent oracle uses the alternate single-polynomial relation w^12−2w^6+2 and left-to-right exponentiation. Oracle generation produced 312 rows (303 successful expectations, 9 rejection expectations), all five comparator mutations detected. A separate temporary JS arithmetic model matched all 303 valid arithmetic expectations, including three final exponents. This is model/harness evidence only; no native Lean pass claimed yet. Fresh CI must compile and check six candidate statements, exact axiom inventory, dependencies and complete native output. Run retained G1/G2 gates as well.

Exact new source blobs:
- formal/lean4/ethereum-consensus/PairingTarget.lean 250719fa2f1be651d66918c75a419c3f0b77fafd
- formal/lean4/ethereum-consensus/scripts/check-pairing-target.mjs f00d737bdabd6c84347e2fdd1f273c153fffb275
- .github/workflows/ethereum-bls-pairing-target.yml 48e0436af36f5999c01bae9984deb3bca763a084

Unchanged predecessor blobs:
- formal/lean4/ethereum-consensus/G2Signature.lean 9a135cce63739f5e62017e98bd76a888b0d89306
- formal/lean4/ethereum-consensus/lean-toolchain a8afa7d1b02d96f0671eba854a8dc4b416beb473
- formal/lean4/ethereum-consensus/lakefile.toml b08203129886735a8fbfc2c31fb7027024665d1f
- formal/lean4/ethereum-consensus/lake-manifest.json 15728fe01a01ed2369565ec5be9afdf6abcf2f91

Only Lean imported, pinned Lean 4.33.1, empty external Lake package graph. Native compiler/runtime and test transport remain trusted. Resource limit checks precede public arithmetic but not line allocation. No shared Mac or coding subagent available. General field irreducibility/refinement, exponentiation completeness, Miller loop, hash-to-curve, proof-of-possession and integration into authenticated consensus transitions remain outstanding. No production risk acceptance or main merge.
