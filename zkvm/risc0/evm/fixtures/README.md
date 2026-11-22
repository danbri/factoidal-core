# Recorded public ASK proof

These files retain a genuine Groth16 proof of the Lean ASK guest's
`rule-inference` case, generated and verified locally on 2026-11-22.
The Solidity gate accepted this proof and all six rejection controls
passed. Tracking: [ASK attestations](https://github.com/danbri/factoidal-core/issues/745).

| File | Purpose |
| --- | --- |
| `expected-statement.json` | Authorised image and 128-byte journal, prepared from the independent native execution before proof export |
| `ask-proof.json` | SDK-verified Groth16 seal and its public journal |
| `provenance.json` | Exact file and checkpoint hashes, source/image baseline, toolchain pins, observed tests, resource settings and timings |

Only the small public proof export and expected statement are in Git.
Compiled binaries, large STARK receipts, prover inputs and witnesses are
excluded. The source fixture is deliberately synthetic and public; it
contains no private user data.

## Computation and authorised baseline

The N-Triples input has two edges:

```ntriples
<urn:a> <urn:p> <urn:b> .
<urn:b> <urn:p> <urn:c> .
```

The positive SPARQL-RL rules are:

```sparql
RULE { ?x <urn:reach> ?y } WHERE { ?x <urn:p> ?y }
RULE { ?x <urn:reach> ?z } WHERE { ?x <urn:reach> ?y . ?y <urn:p> ?z }
```

The query `ASK { <urn:a> <urn:reach> <urn:c> }` succeeds after checked rule
closure. This particular proof uses the `simple` regime, with no RDFS
step. The public salt is 32 bytes of `0x07`; the context is
`beneficiary=public-fixture;action=check;nonce=1`. Exact byte hashes are
recorded in the provenance. The source generator is
[`tools/check-ask-attestation.py`](https://github.com/danbri/factoidal-core/blob/1bf9c1b430f7ddc3489d72991c82b01bd625600c/tools/check-ask-attestation.py).

The authorised guest image is
`c6d11ad4ba2b40d049bd3c117779816c73b3247d7bc50bb00e1c5c898618239b`.
Its recorded public source baseline is
[`1bf9c1b430f7ddc3489d72991c82b01bd625600c`](https://github.com/danbri/factoidal-core/commit/1bf9c1b430f7ddc3489d72991c82b01bd625600c),
tree `985a6bd54f57da71530fc24f84b54bcd3e9f2192`. The host proof driver is
recorded at
[`3cf6ccb83fea652753f9e6c8c0c380a924bc1c74`](https://github.com/danbri/factoidal-core/commit/3cf6ccb83fea652753f9e6c8c0c380a924bc1c74).
The journal was checked against native execution and the independent
byte-protocol oracle before the Groth16 export. The expected policy and
context therefore do not come from an untrusted proof submission.

## Local proof and verification record

The actual composite receipt was independently verified, compressed to a
verified succinct receipt, converted to a verified `identity_p254`
receipt, and proved by the official pinned CPU witness generator and
gnark prover. The SDK then verified the constructed Groth16 receipt
against the authorised image and journal before export.

The first identity attempt stopped on a verifier-parameter mismatch:
the adapter had supplied the identity leaf ID in place of its fixed
depth-eight Merkle root. The corrected context derives the root from
pinned SDK constants using the official hash function. Its full integrity
and claim checks passed on retry. The verified succinct checkpoint was
reused unchanged; the composite proof was not repeated for this repair.

| Stage | Observed wall time |
| --- | ---: |
| Composite proof, 34 segments | 3,941.714 s |
| First prepare, including the refused identity attempt | 1,287.029 s |
| Successful identity retry from saved succinct receipt | 81.368 s |
| Official CPU witness generation | 6.904 s |
| Official CPU Groth16 proving | 23.700 s |

These are this run's measurements, including the recorded failed
conversion attempt. They are not a clean end-to-end benchmark.
`RAYON_NUM_THREADS=8` and `GOMAXPROCS=8` were configured for their respective
stages, with an 8 GiB address-space limit; the Go prover also used a
6 GiB soft memory limit. No remote proving service or external
chain transaction was used, and no new setup ceremony was run.

The local Foundry EVM passed all 18 admission tests and all seven actual
ASK proof tests: acceptance plus rejection of changed image, graph
commitment, authorised policy, authorised context, false result and
tampered seal. The successful `verifyTrue` external call used
**230,839 gas**, including ABI/STATICCALL/return overhead. The measurement
excludes input copies, deployment/setup, log emission and transaction
intrinsic gas. The whole positive Forge test used 273,492 gas. The pinned
compiler is Solidity 0.8.26, Cancun, via IR, with 10,000 optimiser runs.

The successful-call figure is not a worst-case bound for invalid proofs.
The existing tampered-seal test caused a pairing precompile error and
then `VerificationFailed`; its whole Forge test used 1,008,173,841 gas
under the harness's large gas budget. The pinned verifier forwards
`gas() - 2000` to the curve/pairing precompiles, subject to EVM forwarding
rules. Application verification-call budgets are separate from this
reference view gate; the verifier has not been altered to add one.

## Re-verification and regeneration

From the parent `evm` directory, after the pinned dependency bootstrap:

```sh
FACTOIDAL_EVM_FIXTURE_DIR=fixtures FOUNDRY_PROFILE=proof forge test -vv
```

CI verifies these recorded file hashes and runs all seven proof tests.
It re-verifies this historical image and statement; it does not rebuild
the current guest or generate a new proof for changed Lean sources.
Missing or invalid fixtures fail explicitly. There is no mock or skip
path.

For a new image or statement, follow the parent README's
[fresh export procedure](../README.md#export-a-newly-generated-ask-proof).
Its fresh child directory is selected explicitly by the test profile.
The recorded validation regenerated both files in such a directory and
passed all seven tests. A separate selected child with a changed
expected image failed setup with `proof image differs` while the valid
default remained unchanged, establishing that no fallback occurred.

Update the two retained JSON files and their provenance together only
after independent authorisation and actual proof verification. A true
result attests the admitted computation over the committed input; it
does not establish the source or authority of that RDF data.
