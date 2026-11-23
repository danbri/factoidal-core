# Private ASK workflow

This Linux host workflow prepares a private RDF witness with a fresh 32-byte OS
CSPRNG salt, checks native Lean/HACL against the reviewed RISC Zero executor,
proves the same journal locally, and exports a small public Groth16 package.
It keeps the existing guest and ASK semantics unchanged.

Tracking: [private workflow #801](https://github.com/danbri/factoidal-core/issues/801),
within [ASK attestations #745](https://github.com/danbri/factoidal-core/issues/745).

## Authority and Boolean contract

The verifier's `--policy` file is supplied independently by the relying party.
It specifies the reviewed image, policy hash, context hash and an explicit
`requireTrue: true`. The journal is exactly four 32-byte words: salted graph
commitment, policy hash, context hash and canonical ABI Boolean. The SDK verifies
the reconstructed successful claim for the separately authorised image and
submitted journal using its pinned default Groth16 parameters. The EVM seal is
exactly 260 bytes with selector `0xe71e6620`.

`expectedCommitment` can independently authorise a particular graph commitment.
When it is `null`, the first word is a proved public claim, not evidence that the
prover owns or is authorised to use any particular graph. The application must
decide what that claim means. The workflow does not identify a beneficiary,
perform an action, consume a nonce or prevent replay. Those require a separate
application policy. The reference Solidity view gate and this SDK verifier are
separate from the repository's Lean Ethereum client.

A successfully evaluated false ASK is `not-satisfied`, exit status 3, **only
after native and guest executor journals agree**. It produces no composite
proof and no public package. A parser, runtime, resource, entropy, tool identity
or proof failure is a refusal, exit status 2. Neither kind of failure is converted
to a false answer. This milestone exports true attestations only.

`authorisation.example.json` uses the public transitive-rule policy and context
already used by the retained ASK proof. It authorises that demonstration only;
its context text does not confer application authority. Replace the public
query/rules/context and their independently established native/HACL hashes for a
different policy. Do not derive the expected hashes from an untrusted receipt.
For a different policy, the relying party can run the pinned native CLI with
those public query/rules/context bytes and a separate public test graph and test
salt, then take the second and third journal words as the policy/context hashes.
Those two words are independent of the test graph and salt; the dummy ASK may
be false while still producing a successful native journal. Review the public
policy text and those hashes before using the configuration with private data.
Before any proving, native output must match the configured policy/context
words. Python does not implement RDF semantics or private commitment hashing.

## Reviewed guest and software configuration

The workflow is pinned to image
`c6d11ad4ba2b40d049bd3c117779816c73b3247d7bc50bb00e1c5c898618239b`
and the recorded program built from
[`1bf9c1b430f7ddc3489d72991c82b01bd625600c`](https://github.com/danbri/factoidal-core/commit/1bf9c1b430f7ddc3489d72991c82b01bd625600c),
tree `985a6bd54f57da71530fc24f84b54bcd3e9f2192`. This is a reviewed historical
guest, not a claim that each future checkout rebuilds to that image. The
program's SHA-256 is checked against the recorded pin before execution.

Build the receipt helper from this checkout using its locked dependencies and
the [pinned EVM setup](../evm/README.md). It must include `verify-public`. Obtain
the native runner, host, guest program and `r0vm` from the reviewed build and
validate their source/tool provenance. The [toolchain setup](../README.md) and
[official CPU prover setup](../evm/README.md) describe the existing prerequisites.
No binary is committed by this workflow.

Create a private `tools.json` from `tools.example.json`, replacing each path and
placeholder with the independently verified public software identity. Hashing
executables and source files with the standard system SHA-256 utility is public
software bookkeeping. Do not apply that operation to the private RDF, salt,
frame or witness. The CPU runner, its downloader module and committed pin file
must be from the same reviewed source checkout. The official CPU runner checks
all six installed prover/setup files against their committed pins.

Preparation copies each pinned tool/program into the new private work directory
while hashing that exact copied stream. Later stages use those copies. The
workflow also records its own three source files and the Python interpreter;
resume refuses changed orchestration source or tool bytes. This records the
software used without putting private paths into public provenance. The host
OS, Python, dynamic loader/runtime libraries and independently supplied
configuration remain trusted prerequisites.

The local host must also have no hostile local co-tenants. The pinned SDK's
[`ParentProcessConnector`](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/host/api/mod.rs)
binds an ephemeral `127.0.0.1` TCP listener, launches `r0vm --port`, and accepts
the first connection. Its
[`Hello` exchange](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/host/api/client.rs)
checks version compatibility; it does not authenticate that local peer before
requests and private input are transmitted. Mode 0700/0600 file permissions do
not isolate this transport from another local process racing the connection.
The workflow therefore assumes a trusted local execution environment, rather
than providing a sandbox for mutually hostile tenants. The SDK and its transport
are unchanged here.

## One invocation, or a cheap preparation first

Choose new paths outside the source checkout. Existing files, directories and
symlinks are refused. Private work directories are mode 0700; files are 0600
and executable software snapshots 0700. They are **not encrypted**. Other users
of the same account and host administrators are outside this filesystem
isolation boundary. Salt and witness retention is deliberate for resume; remove
the private directory when it is no longer needed under your storage policy.

```sh
python3 zkvm/risc0/private/workflow.py run \
  --policy /secure/authorisation.json \
  --tools /secure/tools.json \
  --input /secure/private.nt \
  --work-dir /secure/new-ask-work \
  --public-dir /exports/new-ask-package
```

For a cheap native/executor check before starting a long proof:

```sh
python3 zkvm/risc0/private/workflow.py prepare \
  --policy /secure/authorisation.json \
  --tools /secure/tools.json \
  --input /secure/private.nt \
  --work-dir /secure/new-ask-work

python3 zkvm/risc0/private/workflow.py prove \
  --policy /secure/authorisation.json \
  --work-dir /secure/new-ask-work \
  --public-dir /exports/new-ask-package
```

Preparation snapshots the input once and generates the salt through `os.urandom`.
An exception or short entropy result refuses preparation, with no fallback.
Resume has no input or salt option: it reruns native Lean/HACL on the saved
snapshot, compares the full journal and frame, and checks guest execution again.
A changed original input file is irrelevant. A changed prepared witness or
salt is refused. A changed policy configuration is refused.

Composite and final Groth16 receipts are written in fresh attempt directories,
verified, then atomically promoted without replacing a canonical checkpoint.
An interrupted partial write stays in its attempt directory. Verified ordinary
succinct receipts can be reused after independent verification; identity input
is regenerated in a fresh attempt rather than trusting stale `input.json` or
witness files. A partial or otherwise unverified attempt-directory succinct
candidate is retained and skipped; the verified composite remains available for
fresh compression. Invalid existing canonical checkpoints are refused and left
for inspection. No receipt is accepted because its filename exists.

Every proof stage uses the shared `/tmp/factoidal-zk-prove.lock`. Native/executor
children use a 3 GiB address-space ceiling, one Lean thread and two Rayon threads.
The composite and SDK recursion stages configure `RAYON_NUM_THREADS=8`, an 8 GiB
address-space ceiling and a three-hour timeout per stage. Composite segment size
is `2^19`; the guest's existing session ceiling remains unchanged. The official
CPU stage configures eight jobs, `GOMAXPROCS=8`, `GOMEMLIMIT=6GiB`, an 8 GiB
address-space ceiling and a 30-minute timeout for each of its two sequential
children. These settings do not assert a bound on every internal C++ thread pool
or measured RSS. A five-GiB free-space admission check precedes expensive stages;
it is not a disk quota. Run only when the host has sufficient exclusive resources.

Core dumps are disabled for children. Raw stdout/stderr and exception messages
are discarded. The one executor JSON response is bounded and used in memory;
its input-dependent cycle counts are not exported. Private stage logs contain
only fixed stage/status identifiers, exit code and elapsed time. Child timeouts,
failures and interrupted wrappers clean their own process group. The CPU runner's
`--redact-diagnostics` suppresses its witness/prover logs and command/path records.
This workflow also discards the CPU runner's own stderr, including startup and
timeout exceptions.

## Public-only verification

Successful publication creates exactly:

| File | Contents |
| --- | --- |
| `ask-proof.json` | The existing strict EVM JSON: journal, seal, image and pinned format/SDK/parameter fields. |
| `public-provenance.json` | Approved public IDs, recorded guest source and software hashes. No input or salt digest, witness length, private path, execution trace or per-input statistic. |

The package is verified before an atomic `RENAME_NOREPLACE` publication. Any
existing target, including an empty directory or symlink, is refused. An
interrupted unpublished staging directory contains public material only and is
not the requested destination. Once atomic publication succeeds, the complete
package exists even if the process is interrupted before printing its final
status. No partial package at the requested name is accepted by the verifier.

Transfer only this directory to the verifier. The verifier does not need the
private work directory, native runner, RDF input, salt, frame, intermediate
receipt, witness generator or proving setup:

```sh
python3 zkvm/risc0/private/verify.py \
  --policy /verifier/independently-authorised.json \
  --verifier-tool /verifier/factoidal-evm-receipt \
  --verifier-sha256 VERIFIED_PUBLIC_EXECUTABLE_SHA256 \
  --package /received/ask-package
```

The verifier rejects extra files, symlinks, duplicate or unknown JSON fields,
oversized/noncanonical data, wrong authority fields, false answers and malformed
or modified proofs. It copies the bounded proof bytes and pinned verifier into
a temporary private directory before SDK verification. Descriptive provenance
does not supply trusted expectations and is not itself authenticated by the
Groth16 proof. Its exact allowlisted shape is checked to prevent accidental
private metadata export.

## Checks and cost

```sh
python3 zkvm/risc0/private/test_workflow.py
python3 zkvm/risc0/private/check_native.py \
  --policy zkvm/risc0/private/authorisation.example.json \
  --tools /secure/tools.json \
  --work-dir /secure/new-private-controls
```

The first command tests lifecycle/refusal boundaries with short process doubles;
those are not cryptographic proof evidence. The second generates a local private
synthetic intermediate RDF node and tests real native/executor agreement,
snapshot/resume, salt/policy/context binding, false/invalid distinction and
diagnostic privacy. It never starts a prover or emits witness details.

Receipt-tool release tests independently verify the retained public ASK Groth16
proof and reject mutations and mismatched verifier configuration. The previous
public transitive-rule fixture took about 66 minutes for composite proving and
roughly 20 minutes for ordinary succinct compression on the recorded host. New
private input bytes can change execution/proving cost. A successful cheap
preparation is not a proof, and a previous retained proof is not proof of the new
private witness. Record a new private run's completion separately; publish only
its allowlisted public package.

## Retained private-witness proof

[`fixtures/20261123`](fixtures/20261123) contains exactly the two public export
files from a newly proved private synthetic witness with a fresh OS salt. The
public-only verifier and all seven existing local Solidity proof-profile cases
accepted the valid proof and passed their refusal controls. The native-derived
expected statement used for the independent checks stays outside this package.
The witness, salt and intermediate proof material are not retained in Git.

To replay the public package, use the public-only verification command above
with `--policy zkvm/risc0/private/authorisation.example.json` and
`--package zkvm/risc0/private/fixtures/20261123`, supplying a verifier built from
reviewed locked source and its independently checked executable hash. The normal
receipt-boundary CI job performs this replay. The fixture records the historical
reviewed guest image; CI does not regenerate its private proof or infer a guest
rebuild from the current source.

The first private run exposed a stage-name logging defect after the CPU prover
succeeded, before SDK finalisation or export. The saved proof was subsequently
verified through the pinned helper and separate host verifier, then the original
frozen workflow resumed from the verified final receipt. Original input, salt,
prepared state and source hashes were preserved. The separate stage-name fix
passes 17 lifecycle tests, including the actual digit-bearing production labels
and refusal before child launch. Its complete proving path was not rerun.
The [dated worknote](../../../docs/20261122-private-ask-workflow.md) records the
manual recovery, independent verification and exact public file hashes.
