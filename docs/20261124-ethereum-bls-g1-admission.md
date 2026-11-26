# Independent BLS12-381 G1 public-key admission — 24 November 2026

Tracks #954 under #725. Isolated branch from #947, `d4589c2733d8d5bf5ec97b13eea865c88aa6a552`. No changes to existing implementation files, Lake configuration, external manifest, toolchain or proof ledgers. The execution stack (including the actual identity CALL/direct-transaction integration #839) remains separate.

## Newly confirmed predecessor evidence

The combined SSZ/slashing integration #947 was compiled and tested at PR test merge `d0f75be70b21f9e39d4402f366ab508664360960`, tree `b1b7db6423a1d0de38d920d07fcb0c98bbbbc9e4` (identical to the #947 head). The actual [registry job](https://github.com/danbri/factoidal-core/actions/runs/45466902675/job/138704108028) passed 9293/9293 native rows, eight comparator controls and 35 selected axiom reports. The actual [proposer job](https://github.com/danbri/factoidal-core/actions/runs/45466902585/job/138704102402) passed 1218/1218 rows, 46 candidates, three comparator controls, and 12 selected axiom reports. The [retained SSZ job](https://github.com/danbri/factoidal-core/actions/runs/45466903729/job/138704113530) passed every step including the two exact-source ledgers and their six mutations each. These passes establish integration of the two preparatory paths, not authentication. The [full corpus job](https://github.com/danbri/factoidal-core/actions/runs/45466903053/job/138704103742) compiled the library and native runners but failed its compiled recursion/replacement gate; subsequent suites were skipped. No broad premerge pass is asserted.

## New implementation under test

`G1PublicKey.lean` implements compressed 48-byte public-key admission, fixed BLS12-381 p and r, canonical field coordinate bounds, square root by exponent (p+1)/4, lexicographic sign selection, checked curve equation, and [r]P=O using fixed 255-step Jacobian scalar multiplication. The two exceptional mixed-addition cases are treated separately. Source references are [RFC 9380 §8.8.1](https://www.rfc-editor.org/rfc/rfc9380.html#section-8.8.1), [pairing-friendly-curves-11 Appendix C](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11#appendix-C), [BLS signature draft-06 §2.5](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-06#section-2.5). The latter two are versioned drafts, not final standards. No third-party implementation was used.

The arithmetic uses only Lean core Nat and the byte decoder. It is not on any production transition path, nor a risk acceptance for cryptography on private data. The bounded test transport does not perform any protocol decisions outside Lean. The admitted point checks are explicit but projective group-law refinement, correct square-root completeness, input-to-field decoding completeness, and resource/compiled arithmetic proofs are open. The compiler/runtime remain trusted. No signing or private key path, no BLS signature or pairing verification and no state authentication.

## Tests

Independent Node BigInt oracle uses affine chord/tangent slopes and extended Euclidean modular inverse, rather than the Lean projective implementation. Generator encoding, multiplication by r, and the on-curve non-subgroup point (0,2) of order three are checked. The generated suite and comparator were executed in the development environment: 447 cases generated; all four comparator mutations rejected. Expected distribution: 130 accepted coordinate pairs, 98 not subgroup, 102 not on curve, 24 not compressed, 12 infinity, 68 noncanonical x, nine wrong width and four malformed hex. This is **oracle self-test only**, not a result from Lean. No local Lean installation or repository checkout was available. New Lean proofs, native compilation, and all 447 real comparisons are pending fresh Linux CI. Four selected theorem names are exact-inventory audited with four additional transcript falsification controls. This work is draft and remains off the production path. There is no measured native performance or claim of complete KeyValidate refinement until the exact build and differential checks finish.

Commands (explicit working directory: formal/lean4/ethereum-consensus):
```sh
node scripts/check-g1-public-key.mjs --self-test
lean -o /tmp/G1PublicKey.olean -c /tmp/g1.c G1PublicKey.lean
"$(lean --print-prefix)/bin/leanc" -O2 -o /tmp/g1-public-key /tmp/g1.c
node scripts/check-g1-public-key.mjs /tmp/g1-public-key
```

Next: pass the actual native gate; then connect validated public keys to the commitment-bound proposer and attester preparation without weakening their proof obligations, implement independently checked G2 and hash-to-curve, pairing and signature verification, and only then authorise slashing state changes. Full #725 remains open; no main merge or release.
