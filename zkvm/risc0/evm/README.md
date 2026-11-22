# Local Groth16 and EVM verification for ASK attestations

Tracking: [factoidal-core #745](https://github.com/danbri/factoidal-core/issues/745).

This directory adds a reference Solidity gate for the existing Lean ASK
journal, a local receipt conversion/export tool, and a way to run the
unmodified official CPU Groth16 prover without a Docker daemon. It does
not implement RDF or SPARQL semantics in the host or in Solidity.

## Verified status on 2026-11-22

| Layer | Observed result |
| --- | --- |
| Official patched Solidity verifier | All five upstream tests passed in the local Foundry EVM, including its genuine Groth16 fixture |
| `FactoidalAskGate` checks | 18 local EVM tests passed, including wrong image/journal, policy/context, size, Boolean, missing-proof and old/development-selector cases |
| Rust receipt bridge | Five bridge tests and four shared receipt-decoder tests passed; these include SDK verification of the same official real Groth16 fixture, exact equality of its encoded EVM seal, shared-lock interoperability with Linux `flock`, the pinned identity verifier root and transport refusal controls |
| Official CPU prover/setup | Downloaded from the pinned OCI image; every layer and all six selected files verified; real ASK witness generation and gnark proving completed successfully |
| ASK proof integration test | All seven tests passed against the genuine ASK receipt: acceptance and six rejection controls; absent fixtures fail setup |
| New local succinct/identity/Groth16 generation through this bridge | Completed locally from the verified ASK composite receipt; verified intermediate checkpoints were retained |
| Lean ASK receipt verified in the EVM | Verified for the recorded `rule-inference` case and independently authorised 128-byte journal; successful `verifyTrue` external-call cost was 230,839 gas with the scope below |

The upstream fixture proves its own short journal, `just a
simple receipt`. It is not an ASK proof. The ASK gate explicitly rejects
that journal, and a well-formed 128-byte ASK journal paired with that
unrelated proof also fails. The separate `proof` test profile is the
gate for recording actual ASK verification. Its retained fixture is the
newly generated proof of the Lean ASK execution, described in
[fixtures/README.md](fixtures/README.md) with machine-readable
[provenance](fixtures/provenance.json).

No external-chain transaction, RPC call to a public chain, or remote
proof request is part of these tools or the recorded tests.

## Required patched versions

The RISC Zero advisories
[GHSA-g6qg-9j8p-7j87](https://github.com/risc0/risc0/security/advisories/GHSA-g6qg-9j8p-7j87)
and [GHSA-mm6c-35cm-g4x2](https://github.com/risc0/risc0-ethereum/security/advisories/GHSA-mm6c-35cm-g4x2)
require regenerated receipts and the patched circuit/setup. They identify
3.1.0 selector `0xe71e6620` as the released verifier. The earlier 3.1
selector `0x8b38038c` is superseded and is not accepted here.

| Component | Pin |
| --- | --- |
| `risc0-zkvm` / local `r0vm` | `3.1.0` |
| `risc0-circuit-rv32im`, `risc0-circuit-recursion` | `4.1.0`, recorded in `receipt-tool/Cargo.lock` |
| `risc0-zkp`, `risc0-groth16` | `3.0.6` |
| Solidity repository | [`risc0-ethereum` commit `ff30da77ba4afdd496290ebebedb205348b15d83`](https://github.com/risc0/risc0-ethereum/tree/ff30da77ba4afdd496290ebebedb205348b15d83), tag `v3.1.0` |
| `forge-std` | `8f24d6b04c92975e0795b5868aa0d783251cdeaa` |
| OpenZeppelin contracts | `acd4ff74de833399287ed6b31b4debf6b2b35527` |
| Solidity compiler / target | `0.8.26`, Cancun, optimiser 10000 runs, via IR |
| Foundry used for the recorded tests | `v1.5.0`, commit `1c57854462289b2e71ee7654cd6666217ed86ffd` |
| Official CPU image | `risczero/risc0-groth16-prover:v2026-10-20.1` |
| amd64 OCI manifest | `sha256:49093ed164b82aca9305dd80e4a6eb996bd443201ac7bd50b52909b2761ef583` |
| Existing trusted setup | `2026-10-20.1`; no new ceremony is run |

The full verifier-parameter digest is
`e71e6620a834f4d8dc1998476b865a9a6437a14474f9442cf8664f9ec22a5eee`.
The Rust bridge checks this full value at startup. The Solidity reference
instantiates the official verifier with its pinned `ControlID` constants
and checks the resulting selector. It accepts no caller-supplied verifier.

The official `ControlID.sol` fixes the recursion root to
`e6feef13db7aed4a731c7b0852de1f5c89b137726073f625d05333184d3a551d`.
Its Solidity BN254 control ID is
`0ac2eaf9d5ae64ffb75c4747fde32456e9ee6db3b32350cb2a0614ba91d081de`;
upstream explicitly notes that this constant has the opposite byte order
to the corresponding Rust value. No local byte-order conversion of those
control constants is introduced.

## Statement accepted by the Solidity gate

The journal must have exactly 128 bytes:

| Offset | ABI type | Meaning |
| --- | --- | --- |
| 0–31 | `bytes32` | Commitment to the original input bytes and salt |
| 32–63 | `bytes32` | Hash of the complete versioned policy encoding |
| 64–95 | `bytes32` | Hash of the supplied versioned context message |
| 96–127 | `bool` | Canonical ABI Boolean word; the gate requires exactly one |

This matches `L4Factoidal.Attestation.Journal.encode`: three digest
words followed by 31 zero bytes and either zero or one. The gate rejects
trailing bytes, nonzero Boolean padding, Boolean values above one and a
valid false result. It requires the journal's policy and context to match
the values authorised at construction, then calls the official verifier
with the independently authorised image ID and `sha256(journal)`.

The seal must be exactly 260 bytes: the four-byte verifier selector plus
the SDK's 256-byte Groth16 seal. The Rust encoder uses the same byte
transport as the official
[`encode_seal`](https://github.com/risc0/risc0-ethereum/blob/ff30da77ba4afdd496290ebebedb205348b15d83/contracts/src/lib.rs).
Its test compares all bytes against the official real proof fixture.

The image ID must identify the actual reviewed ASK guest binary, including
its runtime and kernel packaging. The verifier's policy/context values
must come from application configuration, independently of untrusted
receipt metadata. In particular, accepting whichever policy hash a receipt
supplies would accept arbitrary policies returning true.

`verifyTrue` is a view function. It returns the verified graph commitment
and performs no application action or nonce consumption. An application
using it for an action must authorise and consume the corresponding
context, including whichever chain, contract, beneficiary, action and
nonce fields its protocol requires. Repeated verification remains
possible. A commitment and a true ASK result do not establish the origin
or authority of the supplied RDF data.

## Local EVM tests

From this directory:

```sh
python3 bootstrap.py
forge test -vv
```

`bootstrap.py` installs the exact official source and submodule commits,
and refuses a mismatching revision or changes to tracked source. With an
existing clean checkout, `--source /absolute/path` links that checkout
after the same checks. Nothing is downloaded from an unpinned Solidity
branch. The verifier source remains unmodified.

The dependency source includes upstream tests that can also be run in
`lib/risc0-ethereum/contracts` with:

```sh
forge test --match-contract RiscZeroGroth16VerifierTest -vv
```

The recorded Foundry Linux amd64 archive was downloaded from its official
[v1.5.0 release](https://github.com/foundry-rs/foundry/releases/tag/v1.5.0)
and checked against release SHA-256
`5cd98f9092bcc28be087939491f786b2bf3ed55e492996a409e29519b8ab4dc8`.
Foundry executes the tests in its local EVM, with real BN254 verification
precompiles and no network fork. FFI is disabled in the test configuration.

## Local Groth16 proving options

### Official SDK Docker/CUDA paths

The exact SDK source
[`risc0-groth16/src/prove/docker.rs`](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/groth16/src/prove/docker.rs)
uses Docker for CPU shrink-wrapping and invokes the image pinned above.
An installed `r0vm` can request this path with `--receipt-kind groth16`.
The SDK's CUDA path instead requires the `risc0-groth16` rzup component
version `0.2.0`; installing that component alone does not provide a CPU
replacement for the Docker path.

The recorded environment has no Docker daemon or GPU. The following
manual path uses the same official CPU binaries and setup directly.

### Native CPU path

The pinned upstream
[Dockerfile](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/groth16_proof/docker/prover.Dockerfile)
builds a Circom witness generator and a statically linked gnark prover.
Its final image includes the existing proving key and compiled constraint
system. The official
[manual workflow](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/groth16_proof/README.md)
describes producing a proof JSON and converting it into an SDK Groth16
receipt.

```sh
python3 fetch_cpu_prover.py --output-dir "$FACTOIDAL_CPU_PROVER"
python3 run_cpu_prover.py --install-dir "$FACTOIDAL_CPU_PROVER" --check
```

The downloader verifies the fixed OCI manifest and every downloaded
layer before extracting the six selected regular files. The runner
checks each file against the committed hashes in `cpu-prover-pins.json`.
The binary dependencies observed on Linux are standard glibc, libstdc++,
libgcc, libm and libgmp; the gnark binary itself is static. The witness
generator and prover have both completed the recorded ASK proof. The
setup-only `--check` path checks the witness generator's startup without
starting a proof.

Build and test the receipt bridge using the pinned lockfile:

```sh
cargo test --release --locked --manifest-path receipt-tool/Cargo.toml
cargo build --release --locked --manifest-path receipt-tool/Cargo.toml
```

Set `FACTOIDAL_IMAGE_ID`, `FACTOIDAL_RECEIPT` and
`FACTOIDAL_EXPECTED_JOURNAL` to the independently reviewed guest image,
its real composite/succinct receipt, and the exact authorised journal
file. Choose a new `FACTOIDAL_PROOF_WORK` directory. Then:

```sh
RAYON_NUM_THREADS=2 receipt-tool/target/release/factoidal-evm-receipt prepare \
  "$FACTOIDAL_IMAGE_ID" "$FACTOIDAL_RECEIPT" "$FACTOIDAL_EXPECTED_JOURNAL" \
  "$FACTOIDAL_R0VM" "$FACTOIDAL_PROOF_WORK"

python3 run_cpu_prover.py \
  --install-dir "$FACTOIDAL_CPU_PROVER" --work-dir "$FACTOIDAL_PROOF_WORK"

receipt-tool/target/release/factoidal-evm-receipt finish \
  "$FACTOIDAL_IMAGE_ID" "$FACTOIDAL_RECEIPT" "$FACTOIDAL_EXPECTED_JOURNAL" \
  "$FACTOIDAL_PROOF_WORK/proof.json" "$FACTOIDAL_PROOF_WORK/groth16.receipt"
```

`prepare` uses the explicit local `r0vm` subprocess API, not a default
prover that could select a remote service. It checks the original receipt
and journal, compresses to a genuine succinct receipt, then calls the
official `identity_p254` API. It verifies that intermediate proof using
the pinned SDK's BN254/inner control roots and checks preservation of the
claim before calling the official `to_json` encoder.

The identity verifier uses the fixed depth-eight Merkle root containing
the pinned BN254 identity control ID and 255 zero leaves. The root is
derived with the SDK's unmodified Poseidon254 `hash_pair`, following its
[identity API test](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/host/api/tests.rs)
and [Merkle tree definition](https://github.com/risc0/risc0/blob/22c5fb90522cb4d9427d4af6c05e747d20be2b7f/risc0/zkvm/src/receipt/merkle.rs).
The leaf ID alone is not that root. Its verifier context admits only the
`poseidon_254` suite; no trusted parameter comes from returned receipt
metadata. The parameter digest is pinned by a regression test.

The verified succinct receipt is checkpointed before `identity_p254`
starts. If a later stage fails, pass that `succinct.receipt` as the
receipt input to `prepare`, with a new output directory. The pinned
SDK returns an already succinct receipt unchanged for this compression
request. The intermediate identity proof is also saved after verification.
Only a successful final `finish` produces an accepted Groth16 receipt.

The CPU runner uses the official witness generator and gnark prover
sequentially, with a regular witness file instead of the container's
FIFO. This avoids overlapping their memory use. Both `prepare` and the
CPU runner acquire `/tmp/factoidal-zk-prove.lock` internally; do not wrap
them in another lock on that same file. The runner defaults to
`GOMAXPROCS=2`, an 8 GiB address-space limit, a 6 GiB soft Go memory
limit, and a 30-minute timeout for each native child process. `--jobs`
sets Go's execution concurrency; the pinned prover derives its internal
task counts from `runtime.NumCPU()`. Increasing `--jobs` therefore does
not multiply its main circuit/key/witness arrays, although peak memory
can still change with scheduling and worker scratch use. This setting
does not control the separate C++ witness generator.
It preserves the 4 GiB disk reserve and reports process failure without
accepting a receipt. Its proof JSON is untrusted until `finish` verifies
the constructed receipt under the ordinary pinned SDK verifier, the
authorised image and the exact expected journal.

The native invocation preserves the official entrypoint's bare
`stark_verify` argument zero and runs in the extracted `app` directory,
while selecting the executable through its pinned absolute path.
This matters because the generated Circom main opens `argv[0] + ".dat"`.
An absolute argument zero would search in the binary directory and miss
the image's data file. The compiled official binary was inspected to
confirm this path construction; `--check` also tests its actual startup
and argument zero without entering witness generation.

Intermediate files are created with private permissions. This path
does not upload input, witness, proof or journal to a proving service.
The downloaded image/setup are public; their retrieval sends no witness.

## Verify the recorded ASK fixture in the local EVM

The `proof` profile reads `fixtures/expected-statement.json` and
`fixtures/ask-proof.json`. Their provenance identifies the recorded guest
image and source baseline. CI re-verifies that image/statement pair; it
does not rebuild the current guest or generate a fresh proof. CI explicitly
selects `fixtures`; absent or invalid files fail the job.

```sh
FOUNDRY_PROFILE=proof forge test -vv
```

The profile requires exact agreement with the independently authorised
statement, checks the genuine proof, then rejects changed image,
commitment, authorised policy, authorised context, false result and
tampered seal. Missing fixtures fail setup.

The existing successful test also reports local `verifyTrue` external-call
gas, including ABI/STATICCALL and return overhead. Its measurement begins
after copying the input bytes and gate address into locals. It excludes
those copies, deployment/setup, log emission and intrinsic transaction gas.
The recorded value is **230,839 gas** under the pinned compiler and local
Cancun EVM. The complete positive Forge test used 273,492 gas. These are
one fixture's measurements, not a general proving or transaction benchmark.

The successful-call measurement is not a worst-case bound for malformed
proofs. The pinned
[`Groth16Verifier`](https://github.com/risc0/risc0-ethereum/blob/ff30da77ba4afdd496290ebebedb205348b15d83/contracts/src/groth16/Groth16Verifier.sol)
requests `gas() - 2000` for its curve and pairing precompile calls, subject
to EVM forwarding rules. The tampered-seal test reached a pairing
`PrecompileError` and then reverted with `VerificationFailed`; under
Forge's large test budget, that complete negative test used
1,008,173,841 gas. An application must set its own verification-call
budget policy. This reference view gate does not impose that policy.

## Export a newly generated ASK proof

After the preceding real proof and SDK verification have succeeded:

```sh
FACTOIDAL_NEW_EXPORT="fixtures/new-ask"
mkdir -m 0700 "$FACTOIDAL_NEW_EXPORT"

receipt-tool/target/release/factoidal-evm-receipt statement \
  "$FACTOIDAL_IMAGE_ID" "$FACTOIDAL_EXPECTED_JOURNAL" \
  "$FACTOIDAL_NEW_EXPORT/expected-statement.json"

receipt-tool/target/release/factoidal-evm-receipt export \
  "$FACTOIDAL_IMAGE_ID" "$FACTOIDAL_PROOF_WORK/groth16.receipt" \
  "$FACTOIDAL_EXPECTED_JOURNAL" "$FACTOIDAL_NEW_EXPORT/ask-proof.json"

FACTOIDAL_EVM_FIXTURE_DIR="$FACTOIDAL_NEW_EXPORT" \
  FOUNDRY_PROFILE=proof forge test -vv
```

The statement file is created from authorised inputs separately from
the proof export. Both commands refuse existing output files, so a fresh
export directory preserves the retained fixture. Choose an unused child
directory name; it may contain only letters, digits, hyphens and underscores.
`FACTOIDAL_EVM_FIXTURE_DIR` selects that exact child for the seven proof tests
within the existing read-only `fixtures` permission. Empty, absolute,
traversing or nested overrides are refused. When updating the retained
fixture, replace its two JSON files and `provenance.json` together, record
the new authorised source/image baseline, and run both test profiles.

`disable-dev-mode` is compiled into the Rust SDK dependency; explicit
variant checks also reject fake receipts. A composite or succinct receipt
cannot be exported as an EVM seal. An invalid native proof JSON cannot
be turned into an accepted receipt by wrapping it in metadata.

The shared `../receipt_format.rs` transport decoder limits receipt input
to 512 MiB and composite receipts to 1–1,024 segments. It refuses nonempty
composite assumption-receipt lists before the SDK's recursive decoding;
the admitted ASK guest uses no receipt assumptions. Fake and unknown
variants, truncated input and trailing bytes are refused. These transport
checks precede ordinary SDK proof verification and do not replace it.

## Trust and evidence boundaries

The Lean theorems describe the admitted computation and journal
construction. They do not prove the compiler, native runtime, this
transport code, RISC Zero circuits, Groth16 setup, gnark, Solidity
compiler or EVM precompiles. This integration uses the official prover
and verifier implementations for those boundaries and records actual
verification tests. It neither supplies a substitute cryptographic
primitive nor counts a mock, an execution trace, a journal, or successful
compilation as a Groth16 proof.
