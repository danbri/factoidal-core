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
verifying the receipt using the pinned SDK's fixed Groth16 parameters. Unknown/duplicate fields,
noncanonical bytes, wrong policy/context/image, false journals and modified
seals are refused. No provenance field supplies verifier authority.

Only the strict proof JSON and freshly constructed public provenance can leave
the private workflow. Public provenance identifies approved public configuration
and software/source, never raw-input/salt hashes, witness lengths, private paths
or per-input diagnostics. Publication is atomic and refuses an existing name.
Raw child diagnostics are discarded; only fixed structured stage records remain
private. Own process groups are cleaned even if a wrapper has exited first.

The local host must be trusted, including its other local processes. Source
review of pinned SDK commit `22c5fb90522cb4d9427d4af6c05e747d20be2b7f` found that
[`ParentProcessConnector`](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/host/api/mod.rs)
uses an ephemeral loopback TCP listener and accepts its first connection after
launching `r0vm --port`. The
[`Hello` protocol](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/host/api/client.rs)
checks versions, without peer authentication before private payloads. File
permissions protect retained files; they do not provide hostile local tenant
isolation for this transport. This is an explicit host trust condition, with no
SDK or cryptographic modification in this milestone.

## Initial source validation

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

## Private proof and reviewed recovery: 23 November 2026

A fresh synthetic private RDF witness and OS-generated salt produced a genuine
composite receipt, ordinary succinct receipt, identity receipt and CPU Groth16
proof for the reviewed guest. The witness and salt remain private. The final
verified package contains exactly
[`ask-proof.json`](../zkvm/risc0/private/fixtures/20261123/ask-proof.json) and
[`public-provenance.json`](../zkvm/risc0/private/fixtures/20261123/public-provenance.json).
No unsalted input digest, salt digest, witness length, private path or per-input
proving statistic is published.

The first run stopped after both official CPU children succeeded. Its private
stage logger accepted only letters and hyphens, so `groth16-proving` raised
`invalid-stage-record` in `run_child`'s final status write. The second production
label, `groth16-verification`, had the same defect. This failure occurred before
SDK Groth16 finalisation and public export. It left no accepted final receipt or
public package; the verified earlier checkpoints and unverified CPU output
remained available privately.

The [separate stage repair](https://github.com/danbri/factoidal-core/commit/03e44cd084441908e9b696bc42731962dcfeeeee)
admits lower-case identifiers containing digits and validates them before any
child starts. All 17 lifecycle tests passed, including real successful and
nonzero children under both affected labels, diagnostic suppression, and
invalid labels refused before `Popen`. This is focused validation of the
corrected wrapper; its entire proving path was not rerun.

Recovery preserved the original prepared state, RDF, salt, policy, frame, native
journal and software snapshots. The original Python files were checked against
the reviewed source in
[`41dea73f7a73d5d7ee08b767392e3835d026bad7`](https://github.com/danbri/factoidal-core/commit/41dea73f7a73d5d7ee08b767392e3835d026bad7),
tree `9d3bbc077e74c542b1279f5bca46660c002746de`, before importing them.
The edited current source refused the old preparation with
`workflow-source-changed` before any child started; the verified original
snapshot accepted it. No recorded source hash was rewritten.

Under the original work lock, the pinned receipt helper's existing `finish`
command verified the saved composite and candidate Groth16 proof against the
independently authorised image and complete pre-proof native journal. It wrote
a fresh private candidate. The separate pinned host verifier then verified that
candidate before atomic no-replace promotion to the canonical Groth16 receipt.
The original frozen workflow resumed from that verified checkpoint, repeated
native/frame/executor agreement and receipt checks, and published the package.
The public provenance retains those original runtime-source identities. This
was an explicitly reviewed manual recovery, not an uninterrupted run of the
corrected wrapper or an automatic adoption of unverified CPU output.

Final checks passed:

- Public-only verification using separately committed image/policy/context and
  an expected commitment taken from the pre-proof native journal. A second
  independent invocation also passed and checked the entire journal.
- All seven existing local Solidity proof-profile cases: one valid proof and
  the existing authority/journal/seal refusal controls, with no skipped tests.
- The structural two-file allowlist and a supplemental private-content scan.
  The retained package is byte-identical to the verified export. Its commitment
  and seal differ from the earlier public fixture.

Public file SHA-256 values are:

| File | SHA-256 |
| --- | --- |
| `ask-proof.json` | `34277469939c7fe2f08cb22fe6b69e37cee4c5135b9b2ee1297f13498cc1cd51` |
| `public-provenance.json` | `bc923665a8cde7dd52fc19e427da69788259d952a0faa03663b07e21970b0736` |

The ordinary receipt-boundary CI job now rebuilds the locked public verifier and
reverifies these two files against the separately committed authorisation. This
replays the recorded historical image and statement; it does not rebuild that
guest or prove a new witness for every later checkout. The EVM test's independent
native-derived expected statement stays outside the two-file public package.

At this evidence checkpoint, final-head core CI, premerge checks after integration
with current `main`, and the exact-head
[`factoidal-builds/build.yml` run](https://github.com/danbri/factoidal-builds/actions/workflows/build.yml)
remain required and outstanding. Proof verification alone does not complete those
landing gates. [PR 805](https://github.com/danbri/factoidal-core/pull/805) records
the current integration and CI status.
