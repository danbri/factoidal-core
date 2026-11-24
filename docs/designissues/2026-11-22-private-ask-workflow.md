# Private ASK workflow: authority, checkpoints and public export

Date: 2026-11-22. Tracking:
[private workflow, issue 801](https://github.com/danbri/factoidal-core/issues/801),
[ASK attestations, issue 745](https://github.com/danbri/factoidal-core/issues/745)
and [implementation PR 805](https://github.com/danbri/factoidal-core/pull/805).
Commands and resource settings are in the
[workflow README](../../zkvm/risc0/private/README.md); the
[dated worknote](../20261122-private-ask-workflow.md) records validation status.
This record describes the design; proof-run status is recorded in the dated worknote.

## Authority is independent of provenance

The relying party independently authorises the guest image, policy hash,
context hash and the requirement for a true result. An optional expected
commitment can restrict the graph claim. Without that restriction, the
commitment is proved public data, not an ownership or application permission.
Submitted proof fields and descriptive provenance do not supply authority.

The public journal contains the salted original-byte commitment, policy hash,
context hash and canonical ABI Boolean, each in one 32-byte word. Verification
binds all 128 bytes to the independently authorised image using the pinned SDK
and Groth16 verifier parameters. The receipt helper reconstructs the successful
SDK claim from that image and journal; it does not trust a submitted success
label. Public policy/context hashes can be established with the reviewed native
Lean/HACL computation and separate public test data, without disclosing the
private graph or implementing hashing semantics in Python.

## One saved witness and the same computation

Preparation snapshots the original input once and obtains a fresh 32-byte salt
from the operating system CSPRNG. Missing or short entropy refuses preparation.
RDF parsing, checked inference, ASK and commitment hashing remain in the existing
Lean/HACL path. The commitment covers original bytes, not RDF canonicalisation.
The native result must match the authorised policy/context and the guest
executor's complete journal before proof work starts.

A false result becomes `not-satisfied` only after that native/guest agreement.
It creates no proof or public package. Parse, resource, runtime, identity and
proof failures remain refusals; they never become a successful false answer.

Resume takes the saved witness and salt, not a new input argument. It checks
public software/source identities, reruns native Lean/HACL, compares the full
journal and framed bytes with the saved preparation, then checks guest execution
again. A changed original input path is irrelevant; changed saved witness,
salt, authority or software is refused. The reviewed historical guest image is
recorded explicitly, rather than attributed to every later source checkout.

## Checkpoints require verification

Composite and final Groth16 receipts are created in fresh attempt directories,
independently verified against the authorised image and saved native journal,
then atomically promoted without replacing canonical checkpoints. A filename
alone establishes no result. Invalid canonical checkpoints are refused and kept
for inspection. An incomplete or unverified attempt-directory succinct receipt
is skipped; a verified composite remains available for fresh compression.

Ordinary succinct receipts are reused only after independent verification.
Identity input is regenerated in a fresh attempt, rather than accepting stale
witness-generation inputs. The pinned SDK conversion and official CPU Groth16
prover remain distinct checked stages. A historical public proof verifies its
own statement; it does not establish success of a new private run.

## Exact public package

Successful export verifies the final proof and exact saved journal before
atomically publishing a new directory containing exactly `ask-proof.json` and
`public-provenance.json`. An existing destination, extra files, symlinks and
invalid schemas are refused. Public provenance is constructed from approved
public configuration and software/source identities. It excludes private input
or salt hashes, witness lengths, private paths, traces and per-input statistics.
It is descriptive metadata, not a claim authenticated by the Groth16 proof.

The public verifier needs the two-file package, independent authority and the
pinned verifier tool; it does not need the private witness or proving setup.
An EVM test's separately authorised expected-statement fixture stays outside
this package. Private snapshots, intermediate receipts and fixed stage records
stay in the private work directory under its retention policy.

## Trusted host and application boundaries

Private directories and executable tool snapshots use mode 0700; private data
files use 0600. These are permissions, not encryption. The local host, its runtime libraries and other local processes
must be trusted. The pinned SDK's
[ParentProcessConnector](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/host/api/mod.rs)
accepts the first connection to an ephemeral loopback listener after launching
its worker. The
[Hello exchange](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/host/api/client.rs)
checks versions but does not authenticate that peer before private payloads.
The workflow therefore does not isolate mutually hostile local tenants.

The attestation establishes execution over the committed bytes under the
admitted policy. It does not establish the RDF's origin, issuer authority,
truth or ownership. It does not perform an application action, identify an
authorised beneficiary, consume a nonce or prevent replay. The relying
application must enforce those decisions and any stateful context policy.
This host workflow and reference Solidity verifier are not a proof of the
whole application, compiler/runtime stack or the separate Lean Ethereum client.
