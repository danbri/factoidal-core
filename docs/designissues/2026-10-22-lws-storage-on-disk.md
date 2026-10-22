# LWS storage on disk, stage 1: one file per body and a journal (2026-10-22)

Issue: https://github.com/danbri/factoidal/issues/918 (stage 1 only).
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
- `replay_record`, `replay_records`: replaying the records written by a
  sequence of steps gives, at every path, the metadata of the store after the
  steps.
- `recordOfJson_recordJson`, `metaOfJson_metaJson`: the JSON forms read back.
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
