# Independent Ethereum BLS hash-to-field — 25 November 2026

Tracks [#1008](https://github.com/danbri/factoidal-core/issues/1008) and [#725](https://github.com/danbri/factoidal-core/issues/725). Base [#1003](https://github.com/danbri/factoidal-core/pull/1003) at `0f99e6b6a093c282cf699fd009f33007ae504f19`. Owned branch `wip/ethereum-bls-hash-field-20261125-0405`.

## Confirmed predecessor evidence

[Actual Linux job 138947898402](https://github.com/danbri/factoidal-core/actions/runs/45537591032/job/138947898402) tested merge commit 15a57ead1506c803945ab49caccab721aa7ffb3e, tree a6c9de4dd9f1c36a252faccd34bca141f4d5882d. All 318 target-field rows and 30 reduced Tate rows passed; batch times 1209.167272 ms and 4960.032101 ms. Five oracle comparator controls in each suite plus four axiom-audit controls passed. Ten actual theorem reports: checkedOutput_ok [propext]; multiply_width, multiply_noncanonical, powLoop_zero_exp, powLoop_one, power_limit, tate_width, tate_noncanonical, tate_curve, tate_ok each [propext, Quot.sound]. Lean 4.33.1 compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. This is not a proof of bilinearity or complete BLS authentication. The tested coordinate Tate interface does not check G2 subgroup admission.

## New executable slice

RFC 9380 sections 5.2, 5.3.1, 8.8.2 and J.10.1: https://www.rfc-editor.org/rfc/rfc9380.html. The SHA-256 XMD implementation constructs all eight blocks in Lean and reduces four consecutive 64-byte big-endian chunks modulo p. The consensus entry fixes the POP ciphersuite DST and requires an exact 32-byte signing root. Generic short-DST test entry permits 1–255-byte DST and at most 4096 message bytes, with resource refusal before hashing. RFC long-DST preprocessing and arbitrary length messages are not supported by the bounded test interface. No host digest or field answer. Reuse the repository-owned SHA2 module with no explicit imports, pinned below. The public protocol verification context is the only intended use; this experimental module is not part of any shipping signer, private-data API, or production acceptance path. No constant-time, cryptographic security or FIPS refinement claim. Existing general crypto policy still applies outside this public verification experiment.

Locally executed the exact test-only Python oracle (Git blob d934e2515f9aa42e74fd87f9d130590639aa91b4): RFC J.10.1 empty-message known answer matched all four coefficients, 222 expectations generated (208 positive, 14 errors/refusals), five deliberate comparator corruptions detected. This is oracle evidence, not a native Lean comparison. Seven theorem statements address admission, exact delegation, and canonical result. Actual compiler and kernel evidence not yet available. Fresh hosted gate compiles SHA2 and HashToField separately, links the Lean objects, checks native symbols, source pins, seven exact axiom reports and four falsification controls, then compares all 222 native rows. Existing regression workflows and their source inputs are unchanged; do not inherit their pass counts onto edited trees. Local container has no Lean, Codex or access to the shared Mac/build lock; isolated hosted Linux CI is the native build lane.

## Source pins at 1807e60696154b90d6370baf0609c749060d05e2

- HashToField.lean 46c24283e62a3ea88bccc259e201dfb9a95e83c2
- ../L4Factoidal/Crypto/SHA2.lean 92737f4d83035745dba29ef2c3867b01b8dfa50f
- scripts/check-hash-to-field.py d934e2515f9aa42e74fd87f9d130590639aa91b4
- .github/workflows/ethereum-bls-hash-field.yml a01a83a2b234f3fe9bc8b3f8124342d63ff6d57d
- lean-toolchain a8afa7d1b02d96f0671eba854a8dc4b416beb473
- lake-manifest.json 15728fe01a01ed2369565ec5be9afdf6abcf2f91
- lakefile.toml b08203129886735a8fbfc2c31fb7027024665d1f

No new external package, runtime dependency or change to toolchain. Compiler, native Lean runtime and host transport remain trusted. SSWU, isogeny, cofactor clearing, compressed-point pairing-product integration, complete BLS signature verdict and authenticated consensus state transitions remain open. #725 and #652 remain open. No main merge or release.
