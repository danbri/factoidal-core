# Shardborough storage foundation in factoidal-core

Date: 2026-10-10. Status: migrated; preliminary full-library validation
passes. Final validation after review changes is pending.

The owner directs that factoidal-core become Factoidal's home, with Lean 4
and tests first. This change brings the existing pure Shardborough block
and dictionary foundation into core, where the SPARQL index-reuse
improvement already exists. It makes the persisted engine's dependency
chain available for further integration; it supplies no database
performance comparison.

## Provenance and scope

Core base: `7f5c9623`. Source checkout:
`/Users/danbri/working/factoidal`, HEAD
`0c331255b3a0fec0306b5459a944749364db891f`. The source storage tree was
clean when inspected. The migration preserves the source Lean
implementations and proofs, then makes the shared-code repairs listed
below. Existing core SPARQL definitions and their performance changes
remain the integration target.

The 22 new modules are under `formal/lean4/L4Factoidal/`:

| Group | Modules | Count |
| --- | --- | ---: |
| Block foundation | `NatBounds`; `Storage/BlockArtifact`, `BlockArtifactTests`, `BlockMerkle`, `BlockMvp`, `BlockMvpTests`, `BlockWireV0`, `BlockWireV0Tests` | 8 |
| Indexed blocks | `Storage/IndexedBlock`, `IndexedBlockTests`, `IndexedBlockWireV1`, `IndexedBlockWireV1Tests`, `IndexedBlockWireV2`, `IndexedBlockWireV2Tests`, `IndexedBlockWireV3`, `IndexedBlockWireV3Tests`, `IndexedBlockWireV3Theorems` | 9 |
| Paged dictionaries and term proofs | `Storage/PagedTermDictionaryCore`, `PagedTermDictionaryCoreTheorems`, `PagedTermDictionary`, `PagedTermDictionaryTheorems`, `TermCodecTheorems` | 5 |

`formal/lean4/L4Factoidal.lean` imports these modules. Shared
`Storage/Bytes.lean`, `Storage/DeltaLog.lean`, and `DeltaLogTests.lean`
are reconciled with the source dependency chain rather than replaced
along with unrelated core code.

The migrated `Bytes` work includes little-endian u32 inverses and a
total byte-array CRC32C loop proved equal to the list fold. `DeltaLog`
extends its typed entries with the established variable-length DLE1 framing,
DLB1 batches, DLOG parsing, checked writers, and epoch-filtered replay. The
old core DLE1 form used a one-byte version and no payload-length field;
the established form uses u32 version and length fields. The CEP1
marker uses a u64 epoch. F* lineage for these formats remains
`formal/fstar/RDF.Store.Columnar.DeltaLog.fst` in the source repository;
this change ports existing Lean code, without running F* verification.

## Repairs beyond source migration

- Checked v1 term encoding refuses directional literals. This refusal
  propagates through checked framed-entry, batch, and log writers. The
  v1 codec cannot reconstruct their direction. The checked-term proof
  now derives support from successful encoding and preserves arbitrary
  trailing bytes without a separate support hypothesis.
- A DLE1 golden-byte regression pins magic, u32 version, payload length,
  payload, and checksum. Additional regressions cover variable-sized
  adjacent frames and exact suffix consumption.
- CEP1 regressions cover an epoch above the u32 limit, trailing-byte
  rejection, and refusal of an epoch outside u64. New proofs establish
  u64 field inversion, raw DLE1 frame inversion under the payload-size
  bound, checked DLE1 frame inversion from successful checked encoding,
  and CEP1 round trip for a representable epoch.
- Shared fixed-width proofs use Lean core bit-vector lemmas. They do
  not add a `BVDecide` tactic initializer to storage consumers.
- Hash-boundary comments identify native hashing as a realization
  still to migrate and compare in core. A source-repository measurement
  is not evidence that the native implementation exists in core.
- IBK3 selective row planning/execution now checks the encoded row positions
  against the requested start, refuses prefixes beyond the declared row
  count, and checks the complete dictionary extent against its page layout.
  Review reproduced three structural-admission defects; six new refusal
  guards failed before the fix. These checks still require a previously
  admitted artifact and authenticated byte ranges. They do not authenticate
  supplied bytes or prove query correctness for partial reads.

The raw total v1 term serializer remains a legacy byte function. Its
general round-trip theorem requires support and string-size bounds;
durable callers must use the checked writer. Triple terms and
directional literals remain outside the v1 admitted subset.

## Proof boundaries

`BlockMvp` proves exact solution-sequence equality with SPARQL `evalTP`
and exact candidate equality with `tripleMatchesBound`, including row
order and duplicates. `BlockWireV0` lifts those results after a
successful complete decode. It has no general BLK0 encode/decode
round-trip theorem. Its legacy encoder also narrows the row count to
u32 without a count admission check.

PTD1's whole-dictionary theorem states that successful `encode?`
implies `decode?` returns the same ordered term array. The generic
paged-dictionary theorem depends on its supplied term codec's admission
and round-trip contract. IBK3's whole-block theorem needs only successful
`encode?`: decoding returns the same dictionary and ID-row arrays, and
therefore the same denoted graph. Equality of rebuilt hash maps is not
part of that statement. These theorems do not prove the full persisted
query or selective range-read path. IBK1/IBK2 executable regression
coverage does not establish their general codec inverses.

Indexed candidate scans and predicate segments have executable
regressions. A general theorem connecting indexed selective scanning
to `tripleMatchesBound` has not been established by this migration.

Artifact and Merkle operations take an explicit `Hasher`; their
unsuffixed forms use pure Lean SHA-256. A supplied native hash must
agree with that function. This migration does not prove that
agreement or supply a native hash realization. The Merkle inclusion
checks are regressions, with no general inclusion-proof theorem.

## Validation record

Existing regression modules were added before their implementations;
focused builds first failed on the missing imports. Final guard
groups contain 19 block-foundation, 42 indexed-block, and 10
paged-dictionary checks: 71 guards. `DeltaLogTests` contains 52 guards,
giving 123 across these groups, separate from the core SPARQL suite
and guards embedded in `DeltaLog.lean`.

Before the directional-literal repair, four new refusal guards failed
for `serializeTerm?`, `serializeDeltaEntryPayload?`,
`serializeDeltaBatch?`, and `serializeLog?`. After the repair the
delta-log regression build passed seven jobs. The subsequent focused
proof/dependency build passed 13 jobs:

```text
workdir: formal/lean4/
lake build L4Factoidal.Storage.DeltaLogTests L4Factoidal.Storage.TermCodecTheorems
```

Checked framed-entry refusal is also covered in the final regression
module. The focused log is
`/private/tmp/factoidal-core-checked-frame-build.log`.

The block-foundation command passed 17 jobs:

```text
workdir: formal/lean4/
lake build L4Factoidal.NatBounds L4Factoidal.Storage.BlockArtifactTests L4Factoidal.Storage.BlockMvpTests L4Factoidal.Storage.BlockWireV0Tests
```

Its four scan-theorem axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The initial eight block-foundation
files were byte-identical to the inspected source; the hash-boundary
documentation was then corrected as described above.

The final full Lean library check, repeated after the review fixes, passed
439 jobs:

```text
workdir: formal/lean4/
lake build L4Factoidal
```

Recorded logs are `/private/tmp/factoidal-core-storage-final-build.log`,
`/private/tmp/factoidal-core-delta-direction-red.log`, and
`/private/tmp/factoidal-core-delta-direction-green.log`. The final
library build includes the shared-code and whole-codec proofs and
their axiom reports. Seven added shared-code audits cover the u32
inverse, byte-array CRC, u64 inverse, raw and checked DLE1 frames,
CEP1 marker, and epoch-filter split soundness. They use only the allowed
foundations `propext`, `Classical.choice`, and `Quot.sound`. The focused
IBK3 regression and unchanged whole-codec theorem build also passes
48 jobs after the range fixes:

```text
lake build L4Factoidal.Storage.IndexedBlockWireV3Tests L4Factoidal.Storage.IndexedBlockWireV3Theorems
```

## Native codec baseline

`Bench/StorageCodecBench.lean` provides a bounded native smoke test and
codec benchmark. The standalone build passes 90 jobs without linking the
absent HACL* dependency:

```text
workdir: formal/lean4/
lake -f Bench/lakefile.lean build l4storage-codec-bench
.lake/build/bin/l4storage-codec-bench 500,1000,10000 3
```

Measured on Darwin arm64 with Lean 4.33.1. Fixtures have one predicate,
blank-node subjects and distinct UTF-8 literal objects. Graph/block creation,
exact dictionary/row/graph validation and canonical re-encoding are outside
the timed regions. Each phase has one excluded warmup and three timed runs;
each timed result is checked afterward. Generated C inspection confirms
the codec calls occur between the timestamps. Invalid zero rows and zero
runs fail visibly with nonzero status.

| Rows | Terms | Encoded bytes | Median encode ms | Median decode ms |
|---:|---:|---:|---:|---:|
| 500 | 751 | 43,873 | 3.60 | 2.23 |
| 1,000 | 1,501 | 87,897 | 6.83 | 4.33 |
| 10,000 | 15,001 | 893,321 | 70.92 | 46.45 |

Exact results: `docs/20261010-shardborough-storage-codec.csv`. These are
single-process, synthetic codec baselines, not a measured speed improvement
or a full database benchmark.

Peak RSS was not measured: `/usr/bin/time -l` completed an earlier native
run but its resource wrapper failed on sandbox-denied `sysctl kern.clockrate`.
The recorded snapshot comes from a direct native run, not that wrapper.

No pack/activate/query/update/compact lifecycle is exercised by this
increment. Native harnesses, manifests, sidecars, and their remaining
dependencies still need integration into core. No representative
corpus, cold/warm read, ingestion-throughput, peak-memory, QLever, or
Virtuoso comparison has been measured here. The performance-parity
goal remains active.
