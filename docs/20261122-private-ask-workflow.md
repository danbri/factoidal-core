# Private ASK workflow: 22 November 2026

Tracking: [private workflow #801](https://github.com/danbri/factoidal-core/issues/801)
and [ASK attestations #745](https://github.com/danbri/factoidal-core/issues/745).

## Decision

Build a repeatable private-witness lifecycle around the already reviewed guest
image `c6d11ad4ba2b40d049bd3c117779816c73b3247d7bc50bb00e1c5c898618239b`.
Keep RDF parsing, checked RDFS/rules, ASK evaluation and salted commitment
hashing in the existing Lean/HACL path. Add no guest semantics or primitive.

The relying party supplies image/policy/context independently of submitted
proofs. This milestone is true-only. False is an evaluated `not-satisfied`
outcome only after native/executor agreement; errors never become false. An
optional independently supplied commitment can restrict the graph claim.
Without it, the commitment is proved public data and carries no ownership or
application permission. Beneficiary/action/nonce enforcement remains a separate
stateful application milestone, independent of the Lean Ethereum client.

## Implementation

`zkvm/risc0/private/` provides preparation, one-invocation proving, resumable
checkpoints and public-only verification. Input and fresh OS CSPRNG salt are
snapshotted once under an exclusive 0700 work directory. Tool copies are hashed
while copying public software bytes; Python never hashes the private input or
salt. Resume checks public software/source identities and reruns native HACL
over the original saved witness before any new proof work.

The receipt helper adds strict `verify-public`, reconstructing an SDK
`ReceiptClaim::ok` from the independent image and submitted exact journal, and
verifying the patched fixed-parameter Groth16 receipt. Unknown/duplicate fields,
noncanonical bytes, wrong policy/context/image, false journals and modified
seals are refused. No provenance field supplies verifier authority.

Only the strict proof JSON and freshly constructed public provenance can leave
the private workflow. Public provenance identifies approved public configuration
and software/source, never raw-input/salt hashes, witness lengths, private paths
or per-input diagnostics. Publication is atomic and refuses an existing name.
Raw child diagnostics are discarded; only fixed structured stage records remain
private. Own process groups are cleaned even if a wrapper has exited first.

## Validation checkpoint

The public-only receipt verifier passed 12 release tests, including the retained
real ASK Groth16 proof and independent expectation/claim/seal/schema refusal
controls. These reverify historical public evidence; they do not establish a new
private proof. The Python public-only wrapper also accepted that retained proof
and refused a package with an extra file. Fifteen Python lifecycle/refusal tests
passed. Ten actual private
synthetic native/executor controls passed, covering true and false agreement,
original-input snapshot isolation, saved-salt binding, independently supplied
policy/context refusal, stale work, malformed input and diagnostic privacy.
These controls did not start a prover. No new private proof result is claimed at
this source checkpoint.

The first bounded native launch aborted because its default thread reservation
did not fit the 3 GiB address-space ceiling. Explicitly setting one Lean thread
and its existing 16 MiB stack setting, as the native harness does, resolved the
launch. The final workflow retains that setting. The first isolated Rust test
run also lacked the pinned official Solidity fixture checkout; after installing
the exact already available source with `bootstrap.py`, all 12 tests passed.

Independent source review checked the public trust origin, strict JSON/byte
validation, CSPRNG refusal, output allowlist, process-group cleanup, no-overwrite
publication, private diagnostics and false-result distinction. The existing
receipt-boundary CI job now includes the cheap Python lifecycle suite. The
native/executor controls require reviewed native/guest artifacts and remain a
separate explicitly invoked check.

The [workflow README](../zkvm/risc0/private/README.md) gives exact commands,
resource settings, filesystem/privacy limits and the public package contract.
