# Shardborough native runtime in factoidal-core

- The JSON record `20261010-shardborough-native-baseline.json` is in commit 906527b of danbri/factoidal-core (https://github.com/danbri/factoidal-core/blob/906527bae7a741780bb4bab8ccb0f8eb890c85ad/docs/20261010-shardborough-native-baseline.json) and is not in this tree.

Date: 2026-10-10. Core base: `6c7fa10c`.

Factoidal-core now contains the Lean dependency chain and native targets
for Shardborough publication, activation, persisted SPARQL queries,
durable updates, compaction and quad export. The implementation remains
experimental. This change does not establish QLever/Virtuoso performance
parity or full persisted SPARQL conformance.

## Source freshness

The migration source is fetched `danbri/factoidal` commit
`e505f643297922f195e940eb432d4f3ddf2c2a63` (`origin/claude/main`). The sibling
checkout at `/Users/danbri/working/factoidal` remains at `0c331255b3a0fec0306b5459a944749364db891f`,
125 commits behind, with local changes. A requested safe fast-forward was
attempted and Git refused it because local `CLAUDE.md` and
`docs/theorem-registry.md` changes would be overwritten. No reset, stash or
forced merge was used. Source reads use `git show` at the fetched commit,
not locally modified shared Lean files.

The fetched 125-commit difference contains no changes under `formal/lean4`
or `third_party/hacl`. Thus the clean Lean/runtime/vendor files used for
the migration agree with the fetched remote, without discarding the
sibling's unrelated work. Destination changes listed below are separate
from that source snapshot.

## Implementation and proof scope

| Responsibility | Destination | Scope |
| --- | --- | --- |
| Manifest, artifact and generation admission | `Storage/ShardManifest*`, `ChunkedArtifact`, `GenerationVerify` | SBM versions 0–10; checked manifest round trip; parameterised hash operations; generation checks |
| Predicate/quad packing | `Storage/PredicateBlocks`, `PredicateQuadBlocks*`, `PackStream*`, `QuadDataset` | Executable Lean layouts and pure streaming-state invariants; not a bounded-memory claim for every artifact |
| Subject/object/term indexes | `Storage/SubjectRowIndex*`, `TermLocalIndex*` | SRI1/SRI2 and TLI1 codecs, range admission and round-trip proofs; object-index role remains distinct |
| Literal/geometry indexes and planning | `Storage/Literal*`, `Geo*`, `BlockV5Plan`, `PlannerSoundness` | Candidate plans, codecs and stated predicate/dataset restriction theorems; no universal efficient-executor refinement |
| RDF 1.2 wire formats | `Storage/TermWireV2*`, `PagedTermDictionaryV2*`, `IndexedBlockWireV4*`, `IndexedBlockWireV5*` | Directional/triple terms and out-of-line literals; checked codec round trips |
| Parsing and stream state | `Syntax/Utf8Stream*`, `TurtleStatementScan*`, `TurtleChunkFold*`, `NQuadsFast*`, small `Turtle` helpers | Total parsers/folds and local refinements; underscore chunk composition and exact old-prefix/initial-state agreement |
| Shared query runtime | `SPARQL/Query*`, `StoreDataset`, `StoreFastPath`, `DatasetRestriction`, `SharedSubjectTriple*`, `UpdateDelta*` | Active-graph evaluation, physical admission, projection/order/distinct and dataset restriction; core cached-BGP refinements retained |
| Geometry and datatypes | `Geo/Topology`, `BBox`, `BBoxSound`, `Fn/String`, `XSD/Datatypes*`, `SimpleType` | Required runtime definitions, decidable box equality, datatype guards and geometry bounds proofs |
| Native crypto | `Crypto/SHA2Native`, `Harness/NativeHasher`, `ffi/hacl_ed25519.c`, `third_party/hacl` | Restored unmodified HACL* source closure, two SHA-256 externs and differential native checks |
| Native storage lifecycle | `Harness/PredicateShardPack`, `ShardActivate`, `IndexedBlockV3Query`, `QuadQuery`, `DeltaLogTool`, `ShardDeltaCompact`, `QuadDump`, supporting Harness modules | Real file I/O over Lean codecs/query evaluation, not a substitute in-memory database |

The F* lineage for RDF terms, SPARQL algebra/query/update, syntax, datatypes,
geometry, SHA-2 and DLOG remains the corresponding existing F* modules in
the source repository. SBM/IBK/SRI/TLI and their quad/blob extensions are
Lean-native storage formats; no exact F* wire counterpart or newly run F*
verification is claimed. `formal/lean4/L4Factoidal.lean` explicitly includes
all 57 new library modules and their tests/proofs. Native IO executables
remain under `Harness`, outside the pure library boundary.

## Destination repairs

Tests were added or migrated before their required implementation or fix.

- Merkle chunk verification now checks the supplied proof's orientation and
  depth against the requested index and committed chunk count. A proof for
  chunk zero no longer admits the same-size chunk at a different position.
- SRI1 admission rejects a last/singleton offset outside the declared row
  count and offsets repeated across subject entries.
- Legacy V3 selective materialization calls `decodeRowRange?` with the
  actual row offset. It does not misuse a prefix decoder for non-prefix
  subject or object selections. The public range helper still requires
  independently authenticated artifact/header/dictionary admission.
- Language-tagged object equality is not a byte-key equality. Exact-object
  index admission refuses those terms and uses the complete predicate path.
- The new XSD calendar helper is named `calendarDaysFromCivil` so its Nat
  month/day API can coexist with the older Facets Int helper. The full
  library import exposed the source namespace collision; neither algorithm
  is changed by the rename.
- COUNT candidate counting refuses repeated-variable triple patterns.
  LIMIT pushdown refuses expression projections that its variable-only
  projection cannot evaluate. Additional backend/reference regressions
  cover empty named-graph grouping and hidden blank-node rewrite variables.
- Direct subject joins refuse sequence-sensitive modifiers and aggregate
  projections unless a separately admitted finishing rule applies. Actual
  persisted LIMIT, OFFSET, SAMPLE and GROUP_CONCAT probes exposed a target
  row order different from the repository's reference list contract. The
  ordinary evaluator is retained for those shapes; a fast bag-equivalent
  result alone does not license slicing or order-sensitive aggregation.
- The packer's source `partial` handle loop is replaced by structurally
  recursive fuel from observed input byte size, with explicit refusal on
  exhaustion. UTF-8 decoding and parser state stay in Lean.
- POSIX range admission rejects truncating Nat-to-UInt64 conversions,
  signed-offset/end overflow, and file extents too short for the request
  before allocating the requested buffer. The C adapter mirrors the bounds.
- Migrated quad smoke tests use actual whole-output absence checks; the
  source's `grep -vq` accepted output containing a leaked named-graph row.
  Temporary directories use the host's `TMPDIR`, not a missing repo `tmp`.

The shared source Query changes preserve active graphs in EXISTS-containing
projection, HAVING and ORDER expressions. EXISTS inside GROUP BY keys or
aggregate arguments remains a stated unsupported refinement boundary. The
native direct-join paths retain conservative admission; general exact-order
reconstruction/refinement remains open. Neither bag equality nor a
successful parse establishes list equality.

## Validation

Final destination validation passes on macOS arm64 with Lean 4.33.1:

- `lake build L4Factoidal`: 496 jobs, including the 57 new library modules,
  existing cache refinements, and all imported proofs/guards.
- Build of all ten native targets listed in the Lean README: 288 jobs.
- `l4native-crypto-smoke`: 107 pass, zero fail (61 whole/stream SHA-256,
  30 raw compression, 16 Ed25519 checks).
- `l4native-range-smoke`: 38 pass, zero fail, against the actual linked C
  reader, conditional durable append and atomic control-file replacement.
- All five retained disk smoke scripts pass: IBK3 persistence, compaction,
  direct SELECT admission, IBK4 quads and IBK5 quads.
- Direct SELECT tests compare eight actual persisted query/reference pairs,
  plus two plain fast-path positives. Six unsafe query shapes fail before
  the repair. All result sequences in these differential cases fit within
  the CLI preview, unlike the larger baseline joins.
- IBK4/5 tests cover TriG/N-Quads byte agreement, named/default graph
  selection, dataset clauses, RDF 1.2 triple/directional terms, 70,000-byte
  literal and geometry blobs, dump/repack, and artifact/blob corruption
  refusal. IBK3 tests cover unactivated-generation refusal, non-prefix row
  windows, selective modes, delta replay and changed-source compaction
  activation refusal.
- Restored HACL* source/header/license hashes all match `SHA256SUMS`;
  Bash syntax and staged nonvendored `git diff --check` pass. Three
  unmodified upstream C files retain a blank line at EOF reported by Git's
  whitespace check; their pinned hashes are preserved. The benchmark
  rejects zero run counts and nonfinite timeouts.

Headline proof axiom reports use only the accepted Lean foundations
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or
`ofReduceBool` appears in the full build log. Existing linter/deprecation
warnings remain. No new custom axioms, `sorry`, `native_decide` or partial
definitions are added; crypto and host IO externs remain explicit.

Initial integration red logs include absent native executables and missing
imports. A deliberately failing dependency guard removes its `.olean`;
dependent integration builds must wait for the repaired green dependency.
This build-order lesson is recorded in the Lean basics skill. Final runs
use serialized, stable-source library and executable builds.

## Performance measurement

`python3 tools/blockengine-core-baseline.py` measures publication,
activation, LIMIT zero, COUNT, object lookup and two joins on the checked-in
368-triple Wikidata binding-site fixture. Every sample checks the expected
physical mode and row cardinality (plus the COUNT scalar). The CLI prints
only ten preview rows, so this is not complete answer-bag validation.
The report includes fixture/binary hashes, host,
toolchain, raw samples and subsequent-process median/min/max times. Each
sample starts a fresh native process; the OS page cache is not evicted.
These times include process startup, artifact admission and printed output.

Recorded output: [native baseline JSON](20261010-shardborough-native-baseline.json).
On macOS 15.6.1 arm64, Lean 4.33.1, five subsequent fresh processes give:

| Workload | Median ms | Min ms | Max ms |
| --- | ---: | ---: | ---: |
| Pack 368 triples | 38.019 | 37.887 | 38.151 |
| Activate | 34.539 | 34.400 | 34.610 |
| LIMIT zero | 26.432 | 26.316 | 26.521 |
| Predicate COUNT | 26.917 | 26.844 | 27.212 |
| Object lookup | 27.408 | 27.269 | 27.488 |
| Subject join | 30.468 | 30.206 | 32.303 |
| Object/subject join | 30.707 | 30.527 | 30.906 |

Peak RSS and steady-state server throughput are not measured here.

This is a small persisted-route baseline, not a speedup measurement, a
large-data scaling result, or a comparison with another database. The local
Podman connection refused connections when checked outside the sandbox; no
QLever/Virtuoso run is reported.

## Remaining assurance and product work

- Native/pure SHA-256 agreement is checked on finite vectors, not proved
  for all inputs. Positioned/chunked pure hashing also needs a general
  equivalence theorem, beyond existing padding/empty-state lemmas.
- POSIX IO, locking, fsync, rename, C marshalling and the compiler remain
  host trust boundaries. Tests do not establish universal crash recovery.
- Merkle proof soundness and authenticated partial-page admission still
  need general proofs. Byte/layout round trips do not establish them.
- A source snapshot or successful library build is not a fresh W3C corpus
  run. Browser/WASM and other platforms require their own validation.
- Large real corpora, bounded memory, sustained ingestion, concurrent
  readers/writers and same-host QLever/Virtuoso comparisons remain open.
