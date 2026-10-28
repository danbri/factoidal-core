# LWS storage on disk: one file per body and a journal (stage 1), bodies out of memory (stage 2) (2026-10-22)

Issue: https://github.com/danbri/factoidal/issues/918 (stages 1 and 2; stage 2
is the section "Stage 2" at the end).
Skill: `skills/lws-solid/SKILL.md`. Overview: `docs/designissues/2026-10-21-lws-overview.md`.

## Problem

`factoidal lws-serve DIR` keeps the storage in an engine handle and, after each
request that changed it, writes ALL of it to `DIR/lws-state.json`
(`L4Factoidal/LWS/Snapshot.lean`, `npm/factoidal/lws/persist.mjs`). The cost of
one write is linear in the size of the whole storage. Measured 2026-10-22 on
this VM (wasm in Node, small resources, minimum of 3 repeats of 20 PUTs):

| resources in the store | PUT, in memory only | PUT, writes `lws-state.json` |
| ---: | ---: | ---: |
| 1,000 | 1.02 ms | 42.4 ms |
| 2,000 | 0.87 ms | 81.5 ms |
| 4,000 | 1.19 ms | 168.2 ms |

The in-memory step is flat at these sizes; the snapshot write is the cost.

## Stage 1 goal

The cost of one write does not grow with the size of the storage, and every
answer is the same as with the snapshot. The default stays `snapshot`; the new
mode is the configuration member `storage: "files"` (`lws-serve --storage
files`). The Solid server (`solid-serve`) keeps the snapshot in stage 1.

## What stays in memory in stage 1

Everything that is in memory today: the entries with their bodies, the type
index, the Merkle data, the notification, access, search results and redirect
state. Stage 1 changes only what is WRITTEN after a step, and what is READ at
start. Reasons for keeping the bodies in memory in stage 1:

- `Operations.step` reads `Entry.body` for the entity tag of every data
  resource (`Binding.etagFor`, FNV-1a of the bytes), for `size` in listings,
  for ranges, for JSON Patch, and `Notifications.classify` compares the bytes
  before and after a step. A body that is not in memory needs these values in
  the metadata (size and digest) and a protocol that reads a body before the
  step that needs it. That is a change of `Entry` and of every module above
  it: stage 2.
- The per-write cost, the stage 1 goal, comes from the snapshot write, not
  from the memory (table above).

Stage 2 (memory independent of the storage size, the "done when" of issue
918): bodies out of memory and read on GET (size and digest in the metadata),
the metadata in an on-disk index instead of `MemState.entries` (a list, so a
lookup is linear; it is below 1 ms at 4,000 resources, but not at 400,000), and
the start without reading every body.

## Directory layout (`storage: "files"`)

```
DIR/lws-files.json        metadata of every resource and the other state, as of journal record SEQ
DIR/lws-journal           append-only: records SEQ+1, SEQ+2, ... since lws-files.json
DIR/bodies/XX/NNNNNNNNNNNNNNNN
                          one file per body VERSION; N = body number (16 hex digits),
                          XX = its last two hex digits (256 directories)
DIR/lws-state.json.migrated   the snapshot of an earlier start, after migration
```

- A body file is written once and never changed. A new body of a path gets a
  new number (`nextBody`, kept in the metadata). The old file is removed after
  the journal record that replaces it is on disk. So a crash never leaves a
  metadata record that names bytes of another version.
- Body files are named by number, not by a hash of the path: the name gives
  nothing away about the path (also without a key), and a file is never
  replaced in place.
- A resource with no bytes (a container, an empty file) has no body file.
- The numbers that a torn step used are given out again by the next step, so
  the body files of a torn step are written over; they do not accumulate.

## Metadata file and journal

`lws-files.json` (format `lws-files-1`):

```
{"format":"lws-files-1","seq":S,"clock":C,"nextBody":B,
 "entries":[{"path","kind","contentType","mtime","links"?,"size","fnv","body"?}, ...],
 "notifications":{...},"access":{...},"searchResults"?:{...},"moved"?:[...],
 "pendingRemoves"?:["bodies/..", ...]}
```

`entries` keep the order of `MemState.entries`; `size` and `fnv` (FNV-1a 32 of
the bytes, hex) are checked against the body file at start. The other members
are the ones the snapshot has (`notifications`, `access`, `searchResults`,
`moved`), read by the same functions.

A journal record (one per step that changed the storage):

```
{"seq":S,"clock":C,"nextBody":B,
 "ops":[{"put":{entry as above}} | {"remove":"/path"}, ...],
 "side"?:{"notifications","access","searchResults"?,"moved"?},
 "dead"?:["bodies/..", ...]}
```

- `ops`: one per path that the step wrote or removed, in the order of the
  LAST write of each path. Replayed with `memPut`/`memRemove`, they give the
  same list of entries in the same order.
- `side`: only when that state changed (its JSON text differs from the last
  one written).
- `dead`: body files that this record makes unused; removed after the record
  is on disk, and removed again at start (a remove of a missing file is not an
  error).

Frame of one record in `lws-journal`: `"LWJ1"` (4 bytes), the payload length
(4 bytes, big-endian), SHA-256 of the payload (32 bytes), the payload. A record
is valid only when the whole frame is there and the digest matches. Replay
stops at the first frame that is not valid (a torn last record) and the start
then writes a new journal without it. A valid frame whose `seq` is not the next
number stops the start with a message.

Compaction: when the journal would be larger than max(1 MiB, the size of the
last `lws-files.json`), the step writes a new `lws-files.json` in place of a
journal record, then an empty journal. The cost of one compaction is linear in
the store, and it happens after at least as many journal bytes as the store
has metadata bytes, so the cost per write, averaged, does not grow with the
store. The start always compacts when the journal holds a record.

## Crash safety

Lean gives every file operation; the host performs it exactly:

- `write {path, temp, offset, length}`: create the parent directory if it is
  missing, write the bytes to `temp`, fsync, close, rename `temp` to `path`,
  fsync the directory.
- `append {path, offset, length}`: open for append, write, fsync.
- `remove {path}`: remove the file; a missing file is not an error.
- `rename {from, to}`: rename; fsync the directory. Used once, for migration.
- `read`: at start, Lean names the files to read; the host gives the bytes or
  says the file is absent.

Order of one write: the new body files; then the journal record (or the
compaction: `lws-files.json`, then the empty journal); then the removes of
`dead`. The HTTP answer goes out after the plan is done, as with the snapshot.
A crash before the journal record is complete leaves the record torn (ignored
at start) and new body files that nothing names (written over later). A crash
after it leaves dead body files that the start removes.

## Encryption at rest (`FACTOIDAL_LWS_KEY`)

The same key and the same AEAD (ChaCha20-Poly1305, HACL*,
`L4Factoidal/LWS/SnapshotSeal.lean`), per file:

- `lws-files.json`: sealed as a whole with `Seal.sealSnapshot` (format
  `lws-snapshot-sealed-1`); opened with `Seal.openSnapshot`, so a clear file
  with a key, a sealed file without one, and a wrong key are refused as for the
  snapshot.
- Each body file and each journal payload: binary format `"LWE1"`, the 8-byte
  key id, the 12-byte nonce, then ciphertext and tag. The associated data is
  the format id, the key id, the nonce and the CONTEXT: the body file's own
  name, or `lws-journal`. So a body file moved to another name does not open.
- Nonces: the host gives 32 random bytes with each persist and load call; the
  i-th nonce of that call is the first 12 bytes of SHA-256 of
  (`lws-files-nonce:`, i, the bytes). A body file name, a size of a file and
  the time of a write are visible on disk.

## Migration from `lws-state.json`

When `lws-files.json` is absent and `lws-state.json` is present, the start
reads the snapshot as before (sealed or clear), writes every body file,
`lws-files.json` (seq 0) and an empty journal, then renames `lws-state.json` to
`lws-state.json.migrated`. If both files are present (a crash after the
metadata file and before the rename), the metadata file wins and the rename is
done again. A snapshot is never written in files mode.

## Theorems (Lean, `L4Factoidal/LWS/Journal.lean`, `FileLayout.lean`)

- `journalStoreLaws`: the store that records the paths each write touches
  (`JournalStore`, under the Merkle store and the type index) satisfies
  `StoreLaws`; its state carries a proof that every path not recorded has the
  value it had at the last persist.
- `replay_record`, `replay_jstate`, `replay_records`: replaying the records
  written by a sequence of steps gives, at every path, the metadata of the
  store after the steps.
- `persist_replay`, `assignBodies_refs` (stage 1; stage 2 replaced both by
  `bodiesOut_journal` and a new `persist_replay`): the operations `persist` writes are
  `js.record` under the new body references, and a body reference changes only
  at a touched path, so `replay_jstate` applies to the records it writes.
- `recordOfJson_recordJson`, `fileMetaOfJson_fileMetaJson`,
  `metaOfJson_metaJson`: the JSON forms of a record, of one resource's
  metadata, and of the metadata file (record number, clock, next body number,
  entries in order, pending removals) read back. The other state in the
  metadata file is read by the same functions as the snapshot's members.
- `decodeFrames_encodeFrames`, `decodeFrames_torn`: frames read back; a journal
  whose last frame is cut at any byte reads back as the records before it.
- `openBin_sealBin`, `openBin_keyId`: as for the snapshot seal, over any AEAD
  with RFC 8439 correctness.

Not proved: that `Json.toString` and `parseJson` are inverse (the same trusted
layer as the snapshot); checked by the round trip tests.

## Tests

`L4Factoidal/LWS/FileLayoutTests.lean` (`#guard`s, positive and negative);
`tests/lws/storage-files.mjs` (round trip across a restart; the journal cut at
every byte of its last record; encryption on and off; migration from
`lws-state.json`); `tests/lws/scaling.mjs` rows "storage files" (PUT time at
n, 2n, 4n resources, ratio at most 1.5, peak memory reported); every LWS suite
and Touchstone with `--storage files`.

`FACTOIDAL_LWS_STORAGE=files` makes every `listen` with a DIR and no
`storage` option keep the storage in files, so the restart checks of the
other suites (index rebuild, search results records, redirect table,
notifications, binary bodies, Merkle hashes) run on a storage kept in files.
`tests/lws/encryption.mjs` deletes the variable: it tests the sealed snapshot.

## Measured (2026-10-22, this VM, wasm in Node)

`node tests/lws/scaling.mjs`, rows "storage": a storage of s small resources,
then 20 PUTs of new resources per repeat, minimum of three repeats, per PUT;
peak RSS of the child process (it also built the storage in memory).

| resources | snapshot PUT | snapshot peak RSS | files PUT | files peak RSS |
| ---: | ---: | ---: | ---: | ---: |
| 1,000 | 42.6 ms | 318 MiB | 2.70 ms | 302 MiB |
| 2,000 | 83.9 ms | 320 MiB | 2.40 ms | 355 MiB |
| 4,000 | 170.4 ms | 399 MiB | 2.89 ms | 291 MiB |

Ratio 4s/s: snapshot 4.00, files 1.07 (bound 1.5; an earlier run of the same
row gave 2.18, 2.43, 2.75 ms, ratio 1.26). The peak RSS figures are noisy
(the child builds the storage in memory first, and wasm memory does not
shrink); the expected-failure row measures memory separately: a start of a
storage of 1,000 resources of 16 KiB peaks at 258 MiB, of 4,000 at 515 MiB,
because stage 1 reads every body into memory.

Where the remaining time of one files-mode write goes, measured with direct
engine calls (60 PUTs, mean): the step 0.21 ms at 1,000 resources, 0.56 ms at
4,000, 2.8 to 3.7 ms at 16,000; `lwsPersist` 0.14, 0.18, 0.46 to 0.65 ms; the
host's file operations (two fsyncs and a rename) 0.9, 1.2, 1.5 ms. The step is
linear in the store: `MemState.entries` is a list (`memPut` filters it,
`memLookup` scans it), and the handle table holds the previous state during a
step, so the hash sets of the type index are copied on update. Both are
in-memory costs that stage 1 does not change and the snapshot mode has too;
stage 2 removes them with the on-disk metadata index.

Touchstone (`tools/lws-touchstone.sh`), the same totals in both modes:
`--config both` open 76 pass, 0 fail, 145 inapplicable; authorization 215
pass, 0 fail, 6 inapplicable (out of 221 each). `--config all
--unstable-search-results`: 220 passed in at least one configuration, 0
failed, 1 never applied (out of 221). With `--storage files` the stores in
the work directory hold `lws-files.json`, `lws-journal` and `bodies/`, and one
of them (the authorization store, 179 body files, a journal of 932,881 bytes)
reopened with its journal compacted.

## What stage 2 had to do (the list written with stage 1)

1. Bodies out of memory: `Entry` carries the size and the digests (FNV-1a for
   the entity tag, SHA-256 when Merkle is on) instead of the bytes, and a step
   that needs bytes (GET, a range, JSON Patch, a Turtle body for the type
   index, the notification classification) names the body file it needs
   first, as `fetch` names a document today; the host reads it and steps
   again.
2. The metadata in an on-disk index (keyed by path, with the containment
   listing per container), so neither the start nor a step is linear in the
   store; then the step's list scans and the copies of shared state go.
3. A start that reads no body, and the expected failure in
   `tests/lws/scaling.mjs` (peak RSS of a start) turned into an assertion.
4. The same for `solid-serve`, which keeps the snapshot.

## Stage 2 (landed 2026-10-22)

Items 1 and 3 are done, item 2 is done for the step and partly for the start
(see "What is left"), item 4 is an expected failure.

### Bodies out of memory

`Entry` has one more field, `stub : Option BodyStub`
(`L4Factoidal/LWS/Model.lean`). A stub holds the body file number, the
length, FNV-1a 32 of the bytes, the SHA-256 when the Merkle option is on, and
the `rdf:type` objects of a Turtle body with the IRI they were read against.
An entry with a stub has no bytes in memory, except:

- for one step that needs them (`Entry.hydrated`: the body holds the bytes of
  the file), and
- ACL resources (paths that end in `.acl`, `Bodies.keepsBytes`): every access
  decision reads the effective ACL resource (`Solid.Server.allowed`), so they
  keep their bytes; they also have a body file and a stub.

Every function that reads a fact of the bytes reads it through an accessor:
`Entry.size` (listings, search results, ranges), `Entry.fnv` (`etagFor`),
`Merkle.leafDigest` (the Merkle leaf: `.recorded d` for a stub with a 32-byte
SHA-256, else the hash of the bytes), `TypeIndex.contentTypes` (the stub's
types when they were read against the same IRI, else the bytes again: after
a move). `Bodies.dehydrate` makes the stub from these same functions, so the
entry with its stub answers what the entry with its bytes answers. Theorems
(`L4Factoidal/LWS/Bodies.lean`): `size_dehydrate`, `fnv_dehydrate`,
`etagFor_dehydrate`, `itemJson_dehydrate`, `entryFacts_dehydrate`,
`leafDigest_dehydrate` (a 32-byte leaf), and for putting bytes back in for a
step, `entryFacts_withBody` and `leafDigest_withBody`.

`IxState.stubAt` (the bytes go to their body file) and `IxState.withBodyAt`
(the bytes come back for a step, or leave again) replace one entry under the
type index and the Merkle store and do not record the path in the journal.
They build the invariants of the new state from the theorems above:
`IndexOk.congr` (`TypeIndex.lean`: the same facts at every path keep the
index), `Merkle.MkOk.congr_key` (the same kind and leaf at every path keep the
hashes), `Journal.JState.replaceAt` with `replaceAt_prior` (the state at the
last persist gets the same entry unless the path is recorded). A replacement
that the theorems do not cover (a leaf that is not 32 bytes; a stub whose
types were read against another IRI) is not made.

### The read protocol

`Bodies.bodiesNeeded` names the body files a step reads before it runs:

| request | body file read first |
|---|---|
| GET of a data resource | the resource (body or range) |
| PATCH of a data resource | the resource (JSON Patch) |
| PUT of a data resource, when a subscription exists | the resource (`Notifications.sameBytes` compares the bytes before and after) |
| PUT or PATCH of a linkset, with moves and the type index on | every Turtle resource at and below the path (a move reads their types again against the new IRI) |

`lwsStep` then answers `{"ok":true,"read":[PATH,...]}`; the host reads those
files and passes them to the new op `lwsRead`; `Files.readBodies` opens each
one under the storage key (the file's own name is in the associated data),
checks the length, the FNV-1a digest and, when recorded and the option is
on, the SHA-256, and puts the bytes in; the host steps the same request
again. After the step, `Files.unhydrate` drops the bytes of every path the
step did not change; `Files.persist` drops the others. A GET of an entry whose
bytes were not read answers 500 (`Operations.stepPath`), so no response can
carry bytes that are not the resource's. A HEAD reads no body.

A body file changed on disk is found when it is read, not at start: the read
answers an error and the request 500 (`tests/lws/storage-files.mjs`). Stage 1
checked every body at start.

### Persist

`Files.bodiesOut` takes the touched paths in the order of the last writes:
an entry written by the step (bytes, no stub) gets a new body file and its
stub; an entry that has a stub (a move, a change of links or time, bytes read
for the step) gets its stub made again with the same body file; a removed
path gives up its body file. The same bytes as at the last persist keep their
body file only when they were read for the step; otherwise a new file is
written and the old one removed (stage 1 compared the bytes in memory). A
body file is unused, and removed after the record, when a touched path had it
before and no touched path has it after (a move keeps it). The journal record
is `s1.journal.record projE`: the metadata of each touched entry with its
stub. Theorems: `bodiesOut_journal`, `persist_replay` (the record, replayed
onto the metadata at the last persist, gives the metadata after the step).
The handle keeps no table of body files any more (stage 1: `refs`); the stubs
are the table.

### A start that reads no body

A metadata record carries the stub's facts: `sha256` (base64) and `types`
with `typesIri` (format `lws-files-1`, members added; a stage 1 file reads,
and its first start records the missing facts). `Files.needsRead` names a body
file at start only for an ACL resource, for a record with no SHA-256 when the
Merkle option is on, and for a Turtle record whose types were read under
another base IRI. Those entries get a stub made from their bytes; then the
start writes a new metadata file, so the next start reads none
(`tests/lws/storage-files.mjs`: "with the Merkle option a start reads each
body once to record its SHA-256, then none"). `projE_toEntry`: a record read
back as an entry with its stub gives the same record.

### The step in a logarithm of the store

The list store (`MemStore`) found and replaced an entry by a walk over a list.
The LWS handles now run `TreeStore` (`Store.lean`): a `Std.TreeMap` keyed by
path, with a proof that every entry is stored under its own path. Theorems:
`treeStoreLaws` (every law of `StoreLaws`), `treeLookup_ofMem`,
`lwsBase_lookup_ofMem`. `MemStore` and `memStoreLaws` stay as the reference
instance. The type index keeps its tables in `Std.TreeMap` and `Std.TreeSet`
(`TypeIndex.lean`): a step holds the state from before it (the notification
comparison), so a table that a write updates is shared at that moment, and a
shared hash set is copied whole by an insert; a tree copies one path. Two more
linear costs went: a POST computed the bound of its name search from the
number of paths in the store (now `nameTries`, 2^30), and a DELETE of a data
resource listed every path (now only for a container).

`paths` of the tree store are in path order (the list store: newest first).
No response depends on it: listings and search results are put in path order.
The order of the activities of a recursive DELETE in one notification, and
the order of the entries in a snapshot and in `lws-files.json`, are now path
order.

### Measured (2026-10-22, this VM, wasm in Node)

The engine's step and persist, no file I/O (`tests/lws/scaling.mjs`, row
"engine step and persist", a fresh engine per size, minimum of three repeats
of 60 PUTs):

| resources | stage 1 (step only) | stage 2 (step and persist) |
| ---: | ---: | ---: |
| 1,000 | 0.21 ms | 0.304 ms |
| 2,000 | | 0.267 ms |
| 4,000 | 0.56 ms | 0.278 ms |
| 16,000 | 2.8 to 3.7 ms | 0.285 ms |

The step alone in memory (`lwsStep` of a PUT, before and after the tree
store and the persistent index): 0.128, 0.444, 2.191 ms at 1,000, 4,000,
16,000 resources before; 0.118, 0.070, 0.070 ms after; a GET 0.071, 0.088,
0.221 ms before and 0.058 ms at 16,000 after.

One PUT through the HTTP host with `--storage files` (median of five repeats
of 20 PUTs; fsync of the body file and the journal is most of it): 5.75,
4.65, 4.39, 4.46 ms at 1,000, 2,000, 4,000, 16,000 resources (stage 1: 2.70,
2.40, 2.89 ms at 1,000 to 4,000 with the minimum of three; the machine was
under more load on 2026-10-22 afternoon). Snapshot mode: 78.0, 159.7,
278.3 ms.

Peak RSS of a start and one GET of a storage of 16 KiB resources:

| resources | bodies | stage 1 | stage 2 |
| ---: | ---: | ---: | ---: |
| 1,000 | 15.6 MiB | 258 MiB | 230.3 MiB |
| 2,000 | 31.3 MiB | | 229.6 MiB |
| 4,000 | 62.5 MiB | 515 MiB | 210.5 MiB |

The assertion is growth(s to 4s) <= 16 MiB; it measured -19.9 MiB (noise of
the wasm heap). About 200 MiB is Node with the engine loaded.

`lws scaling`: 21 pass, 0 fail (out of 21), 288 s. Host suites, each with and
without `FACTOIDAL_LWS_STORAGE=files`: storage-files 14 pass, 0 fail (out of
14); server 8 pass (out of 8); draft-binding 81 pass (out of 81);
authorization 29 pass (out of 29); binary-bodies 20 pass (out of 20);
encryption 28 pass (out of 28); merkle 18 pass, 1 xfail (out of 19); Solid
protocol 12 pass, 1 xfail (out of 13); Solid OIDC 21 pass (out of 21); Solid
client 7 pass (out of 7); 0 fail in each.

### What is left

- `solid-serve` keeps the snapshot: an expected failure in
  `tests/solid/server/protocol.mjs` names
  https://github.com/danbri/factoidal/issues/918.
- The metadata of every resource is still in memory (a few hundred bytes per
  resource: the entry, its stub, the index facts); a start reads all of
  `lws-files.json`. An on-disk index keyed by path (a start in time
  independent of the number of resources) is not done.
- A container listing filters every path of the store (`containedPaths`),
  and a recursive DELETE and a move list every path: linear in the store.
  The tree store keeps paths in order, so a range of keys would do; the
  `Store` interface has no range operation yet.
- The Merkle data (`MkData`) are hash maps; with the option on, a write to a
  state that the step still holds copies them (linear in the store).
- A PUT of the same bytes writes a new body file unless the old bytes were
  read for the step.

## Summary: what the LWS server offers and assumes about its state (2026-10-28)

Written after the owner asked, 2026-10-28, verbatim: "So our lws server
implentation: what offerings/assumptions does it make about storage / keeping
its state".

Offers:

- One abstract store (`LWS/Store.lean`: `lookup`, `put`, `remove`, `paths`,
  clock) with laws (`StoreLaws`). `Operations.step` is written against it, so
  every backend that satisfies the laws gives the same answers. The reference
  instance is in memory (`MemStore`, `memStoreLaws`).
- Two durable forms for `lws-serve DIR`:
  - `snapshot` (default): all state in `DIR/lws-state.json`, written whole
    after each changing request (temporary file, fsync, rename, fsync of
    `DIR`). The cost of a write is linear in the storage size.
  - `files` (`--storage files` or `FACTOIDAL_LWS_STORAGE=files`):
    `lws-files.json` (metadata), `lws-journal` (one framed record per
    changing request) and `bodies/XX/N` (one file per body version, written
    once). The cost of a write does not grow with the storage size, and
    bodies are not kept in memory. Replay is proved (`persist_replay`), and a
    torn last journal frame is ignored (`decodeFrames_torn`).
- The durable state includes the resources and also notification
  subscriptions, access requests and grants, search results and move
  redirects.
- Encryption at rest is optional and off by default (`FACTOIDAL_LWS_KEY`,
  ChaCha20-Poly1305 from HACL*; a key from `factoidal lws-keygen`). The file
  is authenticated before any of it is used. Every start says on standard
  error whether the storage is sealed (and the key id) or clear text (owner,
  2026-10-28: "For our lws encourage attention to encryption at rest also").
  No re-key and no seal-in-place of a clear storage:
  https://github.com/danbri/factoidal/issues/1136.
- Merkle data is optional and off by default.

Assumes:

- One process writes `DIR`. Since 2026-10-28 this is enforced for the
  servers of this package: `lws-serve`, `solid-serve` and every
  `webdav-serve` local mount hold the lock file `DIR/lws.lock` (format
  `lws-lock-1`: process id, command, start time, host name and a random
  token of the process) while they run and remove it at a clean exit. A
  start refuses a `DIR` whose lock names a process that runs on this host,
  a lock of another host, and a file that is not a lock; a lock whose process
  does not run (after a crash) is taken over with a warning. The engine
  decides the file, its contents and every refusal (`LWS/DirLock.lean`,
  wasm op `lwsDirLock`; theorems `decide_alive_refuses`,
  `decide_otherHost_refuses`, `decide_sameInstance_refuses`,
  `decide_replace_dead`, `decide_create_absent`); the host does the
  exclusive create (`O_EXCL`), the liveness probe (`kill(pid, 0)`) and the
  removal (https://github.com/danbri/factoidal/issues/1135, row C11 of
  `2026-10-28-feature-combination-safety.md`, test `tests/lws/dir-lock.mjs`).
  Still assumed: a program that does not take the lock (another tool, an
  older Factoidal build) does not write `DIR`; the remove-then-create of a
  take-over is not atomic, so two starts that take over the same stale lock
  at the same moment are not excluded.
- A request finishes (state in memory, then the files written) before its
  answer goes out. One request changes state at a time.
- The local file system honours fsync and rename. No replication, backup or
  remote store is built in. A store on another system is reached only as an
  LWS client (`webdav-serve` `kind: lws` mount).
- The metadata of every resource stays in memory in both modes, and a start
  reads all of it. Container listings, recursive DELETE and moves are linear
  in the number of resources.
- The clock comes from the host before each request. Within one request,
  `tick` keeps `Last-Modified` values apart. Across requests, two values can
  be the same (https://github.com/danbri/factoidal/issues/911).
- `solid-serve` keeps the snapshot form only.
