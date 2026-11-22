# Local RISC Zero ASK attestations

Tracking: [factoidal-core #745](https://github.com/danbri/factoidal-core/issues/745).

This backend executes the checked Lean ASK pipeline as RV32 machine code.
The private input is a framed N-Triples document, 32-byte salt, ASK query,
positive rule programme and application context. Only the 128-byte public
journal is committed: graph commitment, policy hash, context hash and a
canonical Boolean word. Parsing, admission, closure, rule evaluation, ASK
and journal encoding remain in Lean. The production SHA-256 primitive is
the repository's pinned HACL* implementation.

The precise admitted policy, limits and theorem scope are documented in
[the computation protocol](../../docs/20261122-ask-attestation-pipeline.md).
This is a bounded, versioned policy, not an arbitrary SPARQL service.
The RDFS regime runs the existing full-seed closure before the positive
rule closure; it does not alternate the two closures to a joint fixpoint.
The seed profile is pinned explicitly, including the existing RDF 1.2
axioms. It is not presented as complete RDF 1.1 model-theoretic entailment.

## Components and trust boundaries

| Component | Responsibility |
| --- | --- |
| `build-runtime.py` | Rebuild the pinned Lean targets, capture their generated C and source hashes under the shared lock, generate the required core C, apply reviewed RV32 adaptations, cross-compile and record a manifest |
| `bridge.cpp` | Copy bounded byte slices into owned Lean arrays, initialise the runtime, call the exported computation, and release the managed result |
| `runtime.cpp`, `platform.c`, `io-port.cpp` | Restricted single-hart runtime, real newlib allocation/free, sequential atomic ABI operations and explicit refusal of unavailable OS/worker/stream services |
| `guest/` | Bound input allocation, enforce exact framing, call the C ABI and commit only a successful 128-byte journal |
| `host/` | Frame bytes, package the SDK kernel with the user ELF, run an explicitly selected local executor/prover, and verify the exact authorised image and journal |
| `receipt_format.rs` | Bound receipt transport and reject unsupported recursive assumptions before SDK decoding; no proof verification is reimplemented |
| `verify-elf.py` | Check the final ELF and every runtime object for the restricted ABI, static linking and absence of TLS |
| `evm/` | Patched official Groth16 conversion and a local Solidity gate requiring the authorised true ASK statement |

The Lean statements do not prove the compiler, C/Rust bridge, allocator,
HACL FFI, RISC Zero circuits or Solidity implementation. These remain
explicit trusted components, with native/guest parity, binary inspection
and cryptographic receipt checks providing separate executable evidence.
The [alignment audit](../../docs/20261122-rv32-lean-runtime-alignment.md)
and [runtime review](../../docs/20261122-risc0-elf-review.md) record concrete
port defects and their bounded repairs.

The non-mimalloc Lean allocator retains its genuine allocation/free
pairing. Four potentially misaligned UInt64/double constructor accesses
use `memcpy`. The RV32 `List.nil` constructor uses `lean_box(0)`. One-hart
once-cell locking refuses recursive entry; the four thread-storage macros
use ordinary storage because the SDK does not initialise C TLS. The
existing 32-bit Nat-literal rewrite is shared with the Wasm build.

GCC emits ordinary memory fences for those atomic loads/stores even on
RV32IM. This zkVM rejects those instructions. After GCC emits assembly,
`lower-fences.py` replaces only standalone ordinary full fences with
four-byte NOPs, retaining GCC's ordering of the actual operations. This
is restricted to the single non-preemptive hart, with no threads, signal
handlers, memory-mapped devices or self-modifying code. FENCE.I and other
forms are refused. Original/lowered assembly and every edit are retained;
the cache binds the helper hash and both compiler/assembler commands.
It also binds the complete installed C/C++ toolchain tree and driver hashes.
The guest linker consumes a private, immutable copy of the archive bytes
that passed the manifest check. The [provenance review](../../docs/20261122-risc0-link-provenance.md)
records the corresponding cache and linking controls.
The final linked instruction gate also covers Rust and prebuilt libraries,
which are never modified by this lowering.

`Init.Data.Random` requests eight bytes once during standard-library
initialisation. The restricted port obtains them from the SDK's actual
`sys_rand` advice service. Their entropy is not proved, they do not supply
the private salt, and the admitted pure ASK policy cannot call this RNG.
Unavailable clock/file/process operations return real errors; unsupported
Lean streams and task workers abort. Neither an initialisation error nor
a runtime panic is converted into a valid false journal.

## Pinned Linux toolchains

The supported setup is Linux x86_64, Python 3.12+, host Rust/Cargo 1.97.1,
Lean 4.33.1 and the exact archives in `toolchain-pins.json`. The SDK is
RISC Zero 3.1.0, with the patched 4.1.0 circuits and 3.0.6 proof crates
recorded in the committed Cargo lockfiles. Guest Rust is the official
RISC Zero 1.97.0 build; C/C++ uses its GCC 13.2.0 toolchain release
2024.1.5. No new cryptography or trusted-setup ceremony is introduced.

Install into a new private directory, using an existing host Rust setup:

```sh
python3 zkvm/risc0/setup-toolchains.py \
  --root /absolute/zk-tools \
  --rustup /absolute/rust/cargo/bin/rustup \
  --rustup-home /absolute/rust/rustup \
  --cargo-home /absolute/rust/cargo
```

The JSON result provides `CARGO_HOME`, `RUSTUP_HOME`, `RISC0_HOME`,
`R0VM` and PATH entries. Export those values for the following commands.
`--check --offline --archive-dir /absolute/archive-cache` performs a
read-only comparison against the pinned archives and an installed tree.
The installer does not bootstrap or update the host Rust installation.

## Build

Use absolute paths for `LEAN_TOOLCHAIN` (the Lean 4.33.1 installation),
`LEAN_SOURCE` (a checkout containing commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and
`FACTOIDAL_ZK_RUNTIME` (an output directory outside the source checkout).
The builder archives pristine runtime sources from that commit and never
patches the supplied source checkout. Run this command at the repository
root; all internal Lake/Lean commands have `formal/lean4` as their explicit
working directory.

```sh
python3 zkvm/risc0/build-runtime.py \
  --toolchain "$LEAN_TOOLCHAIN" --lean-source "$LEAN_SOURCE" \
  --cpp "$RISC0_HOME/cpp" --out "$FACTOIDAL_ZK_RUNTIME" --jobs 2
```

Build the guest from `zkvm/risc0/guest`:

```sh
export FACTOIDAL_ZK_RUNTIME
export RUSTFLAGS='-C passes=lower-atomic -C link-arg=-Ttext=0x00200800 -C link-arg=--fatal-warnings -C panic=abort --cfg getrandom_backend="custom"'
cargo +risc0 build --release --locked --target riscv32im-risc0-zkvm-elf -j2
```

Unset `RUSTFLAGS` before building the ordinary host tool. From
`zkvm/risc0/host`:

```sh
cargo +1.97.1 build --release --locked -j2
cargo +1.97.1 test --release --locked -j2
```

At the repository root, inspect the final guest and its runtime archive:

```sh
python3 zkvm/risc0/verify-elf.py \
  --readelf "$RISC0_HOME/cpp/bin/riscv32-unknown-elf-readelf" \
  --elf zkvm/risc0/guest/target/riscv32im-risc0-zkvm-elf/release/factoidal-ask-guest \
  --runtime-archive "$FACTOIDAL_ZK_RUNTIME/libfactoidal_ask.a" \
  --report "$FACTOIDAL_ZK_RUNTIME/elf-check.json"
python3 zkvm/risc0/verify-instructions.py \
  --objdump "$RISC0_HOME/cpp/bin/riscv32-unknown-elf-objdump" \
  --elf zkvm/risc0/guest/target/riscv32im-risc0-zkvm-elf/release/factoidal-ask-guest \
  --report "$FACTOIDAL_ZK_RUNTIME/instruction-check.json"
```

Build outputs, private frames and receipts are ignored by Git. Keep the
manifest, ELF inspection, exact image ID, input/output hashes and test
results together when recording an attestation build.

## Guest execution against native fixtures

After `tools/check-ask-attestation.py` has completed in a fresh evidence
directory, `check-guest.py` reuses its 24 input fixtures and independently
checked native journals. Supply the already-built host tool, pinned local
executor and packaged programme explicitly. The output directory must not
already exist:

```sh
python3 zkvm/risc0/check-guest.py \
  --host-tool "$ASK_TOOL" --r0vm "$R0VM" --program "$ASK_PROGRAM" \
  --native-evidence "$NATIVE_EVIDENCE" --output-dir "$GUEST_EVIDENCE"
```

This runs 28 checks: all 24 native file cases, plus trailing-frame,
truncated-field, invalid-regime and 257-retained-triple refusals. It requires
the complete native result and source inventory to match the current
checkout. Missing fixtures or journals, changed public byte commitments,
unexpected refusal categories, non-JSON success and any refusal stdout fail
the run. A valid false journal remains a successful execution.

The runner never compiles or proves. It uses one executor thread and a
180-second wall-clock limit per case; the host's cycle limits also apply.
`result.json` records the supplied programme and tool hashes, native source
record, input/journal hashes, reported image/cycles/time and measured wall
time. Private frames, comparison journals and separate stdout/stderr logs
are retained in the new private directory. A comparison journal supplied
to a refusal case is not reported as an emitted journal. The result is
execution evidence only, not a cryptographic receipt or a claim about the
origin of a supplied binary.

The lightweight refusal tests run without the zkVM:
`python3 -m unittest discover -s zkvm/risc0 -p test_check_guest.py`.

## Execute, prove and verify

Let `ASK_TOOL` be the absolute path of
`zkvm/risc0/host/target/release/factoidal-ask-receipt`. Package the user
ELF with the exact SDK kernel; the command prints its image ID:

```sh
ASK_IMAGE_ID="$("$ASK_TOOL" pack "$ASK_ELF" "$ASK_PROGRAM")"
"$ASK_TOOL" frame 0 input.nt salt.bin query.rq rules.srl context.bin private.frame
```

Regime `0` is the simple-input policy followed by positive rules; `1`
adds checked RDFS closure first. The frame has one regime byte and five
little-endian UInt32 byte lengths followed by their payloads. This private
transport framing is separate from the public journal's big-endian
length-prefixed commitment encoding. The guest rejects truncation,
oversized fields and trailing bytes before committing anything.

Supply an independently authorised 128-byte journal file. Native fixture
checks use Python's standard SHA-256 solely as an independent public-byte
oracle, not as another RDF evaluator. An application must establish its
expected policy, context and guest image independently of a submitted
receipt.

```sh
unset RISC0_DEV_MODE
RAYON_NUM_THREADS=2 "$ASK_TOOL" execute \
  "$R0VM" "$ASK_PROGRAM" private.frame expected.journal
RAYON_NUM_THREADS=2 "$ASK_TOOL" prove \
  "$R0VM" "$ASK_PROGRAM" private.frame expected.journal result.receipt
"$ASK_TOOL" verify "$ASK_IMAGE_ID" result.receipt expected.journal
```

`execute` reports execution parity and cycle counts; it is not a proof.
`prove` requests a genuine composite receipt from the explicit local
`r0vm`, verifies its image and journal with the pinned SDK, checks the
bounded receipt decoder, then writes a new private receipt file. It uses
the shared local proving lock. Both commands enforce a 64 Mi user-cycle
session ceiling. Paging and proving rows are additional; this is not a
wall-clock or process-memory limit. The default segment size is 2^18 rows;
`FACTOIDAL_ZK_SEGMENT_PO2` accepts 18, 19 or 20. Smaller segments reduce
per-segment prover memory, while larger segments reduce continuation
overhead. Address-space and wall-clock limits must be imposed by the
invocation wrapper. The guest image and statement are unchanged by these
resource settings. `RAYON_NUM_THREADS` independently controls
the Rust polynomial/NTT work pool; the pinned C++ witness generator has
its own hardware-sized pool. Measure memory and elapsed time on the actual
machine before selecting a production proving budget. The parity runner
always uses the reproducible 18/one-Rayon-thread execution profile.
Development mode is refused,
and the Bonsai feature/default remote-prover selection is not used.

The receipt transport accepts flat composite receipts of at most 1,024
segments, succinct receipts and Groth16 receipts. Any composite assumption
receipt is rejected before recursive SDK deserialisation. Fake receipts,
unknown variants, trailing bytes, wrong image IDs and differing journals
are refused. A valid false journal remains distinguishable from an error.

For patched Groth16 conversion and actual local EVM verification, follow
[`evm/README.md`](evm/README.md). That gate requires true, authorised policy
and context hashes, the reviewed image, and the official `0xe71e6620`
verifier. It does not execute an external-chain transaction or consume an
application nonce. A commitment to RDF and an ASK result do not prove the
origin or authority of those RDF statements.
