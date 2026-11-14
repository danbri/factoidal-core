# Client-side storage: one core, IndexedDB, the File System API, StorageManager (2026-11-14)

Status: on branch `wip/storage`. Measured numbers are in "Measured" below; a line without a cloud run says so.

## What this is

Foafnaut had Web Storage (`Net/Storage.lean`) and no other storage API. This adds one storage core that the
storage APIs share, and on it IndexedDB 3.0, the File System Standard's origin private file system, and
`StorageManager`. Everything is in memory for the session. **Nothing is written to disk**: the persistence
policy is not decided (see "Questions").

| Module (`formal/lean4/L4Factoidal/ClientStorage/`) | What it holds |
|---|---|
| `Core.lean` | storage key, `Backend` (load and save of a shelf) with its laws, `Backend.act` (the one way in), the in-memory `Shed`, quota guard |
| `IdbKey.lean` | IndexedDB keys, "compare two keys", key ranges, the token form of a key |
| `Sorted.lean` | records in key order for any strict total order; the cursor step and the cursor run |
| `IdbValue.lean` | a stored value (the tokens of its structured serialisation), key paths, key injection |
| `IdbStore.lean` | object stores, indexes, databases; `applyEffect`: the only function that changes a database |
| `IdbOps.lean` | connections, transactions, requests, cursors, open and delete, the commands of `web_api` op 200 |
| `IdbTests.lean` | scenario `#guard`s through the commands |
| `FileSystem.lean` | the origin private file system, writables with a swap buffer, access handles, locks; op 201 |
| `Manager.lean` | `StorageManager`: estimate, persist, persisted; op 202 |

Page side: `tools/wasmvm/quickjs/prelude.js`, blocks "IndexedDB" and "File System API". They hold the WebIDL
surface only (classes, argument conversion, promises, event dispatch of what Lean hands over).

## Design

### Storage keys and the one way in

A storage key is an origin and, for a third-party context, the top-level site. Each API keeps one shelf per
key. An API reads or changes storage only through `Backend.act s k f refused`: `f` gets the shelf of `k` and
answers the shelf after it and a result. The key is the engine's (`WebApi.run` gives the session's page
origin); no command takes an origin from the page. An opaque origin is refused.

The privacy property is proved once, for every `f` and every lawful backend: an action for one key changes no
other key's shelf (`act_partition`), its result is a function of its own shelf (`act_answer_local`), and so
what one key does never changes what another key is answered (`act_noninterference`). IndexedDB and the file
system instantiate it (`Idb.opFor_noninterference`, `Fs.opFor_noninterference`). Ids of connections,
transactions, requests, cursors and writables are counted inside the key's shelf, so they tell nothing about
another key.

### Backends

`Backend σ β` is two functions, `load : σ → Key → β` and `save : σ → Key → β → σ`, and `Backend.Laws` is two
laws: a saved shelf is read back, and a save under one key changes no other key. The theorems above need only
those laws. `Shed` (a list in memory) is the reference backend, with the laws proved (`Shed.laws`).

To put a disk or a pod behind storage, write another `Backend` and prove the two laws for it. What goes to the
backend is the durable half of a shelf: for IndexedDB `Idb.Shelf.dbs` (the databases; `live` is session
state and is never persisted), for the file system `Fs.Shelf.tree`. Both change at few, named points
(`Idb.applyEffect` at a commit or a database deletion; in the file system a create, remove, move, a
writable's close and an access handle's write), which is where a backend writes.

**A pod as the backend.** The project's pod specifications are `LWS/Store.lean` (`Store σ` with `StoreLaws`:
`lookup`, `put`, `remove`, `paths` by path; `MemStore`, `TreeStore`), `LWS/Model.lean` (containers by trailing
slash, `Entry` with content type, bytes and modification time), `LWS/PodKinds.lean` (retention, encryption at
rest, versioning), `Identity/Binding.lean` and `LWS/Authorization.lean` (who may act). The mapping:

- The file system maps directly: an `Fs.Path` is the segments of an LWS path; a directory is a container
  (`/a/b/`), a file a data resource (`/a/b`) whose `Entry.body` is the file's bytes and whose `mtime` is the
  file's `lastModified`. `validName` already refuses `/`, so a name is one path segment. The storage key picks
  the container the tree is rooted at (for example `/apps/<origin>/files/`). The law `loadSaveOther` then
  follows from `StoreLaws.lookupPutOther` when the roots of two keys are disjoint paths: that injectivity (key
  to root path) is what the pod backend has to prove.
- IndexedDB maps as one data resource per database (its records in a serialisation of `Idb.Db`), or as one
  container per object store with one resource per record. The first is simple and keeps a commit one `put`
  (so atomic by `StoreLaws`); the second lets other pod clients read records, and needs a commit over several
  resources (the LWS journal, `LWS/Journal.lean`).
- A swap buffer and a transaction's working copy stay in the engine: only `close` and `commit` reach the
  backend, each as one write.

Not built: the pod backend, a disk backend, and a byte serialisation of `Idb.Db` (the stored value is already
bytes: tokens).

### IndexedDB

- **Keys.** A key is a number, date, string, binary or array. A number is held as the order image of its
  double (magnitude bits as an integer, negated for a set sign bit; NaN is not a key), a string as its UTF-16
  code units. `Key.cmp` is "compare two keys". Proved a strict total order (`cmp_refl`, `eq_of_cmp`, `cmp_swap`,
  `cmp_trans`) with the specification's type order (`cmp_rank`). Arrays are read to a nesting of 64.
- **Values.** The page side writes a value as the tokens of its structured serialisation and reads them back
  into a new object. Lean stores the tokens and reads only what a key path needs. So key paths are evaluated
  on the clone, as the specification requires, and no getter of the page's object runs during extraction.
- **Transactions.** A transaction works on a copy taken when it starts. Requests change the copy. The
  databases change only when `pump` commits a transaction (`applyEffect`): a read-write commit replaces the
  stores of its scope, a version-change commit replaces the database. An abort drops the copy. Which
  transaction may start is `canStart` (creation order; overlapping scopes wait unless both only read). A
  commit that would pass the quota is an abort with `QuotaExceededError`.
- **Requests and events.** The page side calls `pump` for the next event (one a task), dispatches it, and
  calls `done` with what the listeners did (threw, or left an error event's default). Lean decides the order
  of requests, when a transaction is active, auto-commit, the events of open and delete requests
  (`versionchange`, `blocked`, `upgradeneeded`, `success`, `error`), and the order of listener calls on the
  path request, transaction, connection (`EventLoop.Dispatch.plan`).
- **Cursors.** A step is the first record in range after the cursor's position (`Sorted.next`), so a cursor
  sees changes made between its steps as the specification says.

### File System API

- No host file system. A tree maps a path (names from the root) to a directory or a file's bytes, in memory.
  No command takes or answers a host path. `showOpenFilePicker` and the other pickers of file-system-access
  are not provided.
- A handle is a path and a kind. `isSameEntry` is equality of both. A handle whose entry is gone finds nothing.
- `createWritable` copies the file into a swap buffer. `write`, `seek`, `truncate` change the buffer only;
  `close` replaces the file's bytes in one step, or fails and changes nothing; `abort` drops the buffer.
- Locks: siloed writables share a file; an exclusive writable and a `readwrite` access handle hold it alone;
  `read-only` and `readwrite-unsafe` access handles share with their own mode. A locked file is not removed
  or moved.
- `lastModified` is a change counter, not a clock (no clock is read).

### StorageManager

`estimate()` answers the sum of what IndexedDB and the file system hold for the caller's key and a constant
quota (512 MiB for each API). Neither number comes from the host. `persisted()` and `persist()` answer false.

### Web Locks

One lock manager for each storage key (`ClientStorage/Locks.lean`, `web_api` op 203): the held locks and the
queue of requests, in request order. A request is granted when it is compatible with every held lock and no
earlier queued request for the same name waits (no overtaking); `ifAvailable` is granted or answered null at
once and never queued; `steal` drops the held locks of its name and is granted alone. `query()` answers the
held and pending lists of the caller's key only.

### File pickers

`showOpenFilePicker`, `showSaveFilePicker` and `showDirectoryPicker` (File System Access) check their options
in Lean (`ClientStorage/Picker.lean`, `web_api` op 201 command `picker`): every accepted MIME type parses by
`WHATWG.MimeType.parse` and has no parameters, every suffix is a valid suffix (starts with `.`, does not end
with `.`, at most 16 code points of ASCII alphanumerics, `+`, `.`), `excludeAcceptAllOption` needs an accepted
type, `startIn` is a well-known directory or a handle, `id` is a valid path id. A malformed call is a
`TypeError`; a well-formed one is refused with `SecurityError` (no transient activation is modelled). No host
file or directory is ever handed to a page (`answer_never_ok`).

### Storage buckets

`navigator.storageBuckets` (`ClientStorage/Buckets.lean`, `web_api` op 205): the buckets of a storage key,
names checked (`validName`), listed in code point order (`op_sorted`), each with a generation so that an object
of a deleted bucket answers `UnknownError` even after its name is reused (`delete_unknown`). `persisted()` is
false; `durability()` and `expires()` answer what was given. A bucket's own `indexedDB`, `caches` and
`getDirectory()` are not provided yet (`NotSupportedError`): the storage key would gain the bucket name, so the
partition theorems would carry over unchanged.

### Cookie Store

`cookieStore` (`ClientStorage/CookieStore.lean`, `web_api` op 204; windows in secure contexts) reads and
writes the one jar of `document.cookie` (`Net.Cookies`) through that module's own steps: `admit`, `store`
(proved to be `document.cookie`'s storage step: `setFromScript_store`), `visibleCookies`. The host is the
session's page origin, never an argument. The checks of "set a cookie" (names, values, prefixes, domain,
path, sizes) and of the `url` option are Lean's. A write answers the changes the document sees (`changes`),
fired as a `CookieChangeEvent`. Not modelled: `SameSite`, `Partitioned`, domain cookies (the jar is host-only),
change events for writes by `document.cookie` or HTTP.

### Cache API

`caches`, `CacheStorage` and `Cache` (`ClientStorage/CacheStorage.lean`, `web_api` op 206; windows and
workers in secure contexts). Caches are kept by id with a name map, so `caches.delete(name)` removes the name
while a `Cache` object of it keeps its entries. "Query cache" is Lean's: URLs without fragments (and without
queries for `ignoreSearch`), `GET` only unless `ignoreMethod`, the response's `Vary` headers compared on both
requests unless `ignoreVary`. `put` refuses non-`http(s)` URLs, methods other than `GET`, status 206 and
`Vary: *`, then replaces every matching entry and appends. The response is stored as opaque bytes written by
the page side (status, headers, URL, type, body). `estimate()` counts the stored responses
(`usageDetails.caches`), and IndexedDB's store descriptions (a name and a constant per store and index).

## Proved, tested only, open

Proved (Lean 4.33.1, no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`; each theorem's doc
comment has its "Says" and "Does not say"):

- Partition: `act_partition`, `act_answer_local`, `act_noninterference`, `act_opaque`, `act_load`, `Shed.laws`,
  `actQuota_bound`, `actQuota_partition`; `Idb.opFor_noninterference`, `Fs.opFor_noninterference`;
  `Manager.op_local` (an estimate is a function of the caller's own shelves).
- Key order: `Key.cmp_refl`, `Key.eq_of_cmp`, `Key.cmp_swap`, `Key.cmp_trans`, `Key.cmp_rank`, `Key.isOrder`,
  `ecmp_isOrder`, `IsOrder.lex`, `Range.only_includes`.
- Sorted records: `insert_sorted`, `erase_sorted`, `find_insert_self`, `find_erase_self`.
- Cursor: `walk_eq_filter` (a cursor run from no position visits exactly the records in its range, each once,
  in key order), `walkRev_eq_filter` (descending for `prev`).
- Exception order of finished transactions' handles: `reqGuard_ended_deleted`, `reqGuard_ended_inactive`,
  `schemaGuard_ended_upgrade` ("has been deleted" before "not active"; "not active" before the name checks).
- Transactions: `run_effect`, `op_dbs` (every command but `pump` leaves the databases as they were: what an
  aborted transaction did was never in them), `effect_none`, `commit_visible` (a later transaction reads what
  was committed), `commit_other_store`, `effect_other_db`, `commit_last_wins` (commit order).
- Quota accounting: `sizeSum_split`, `sizeSum_insert`, `sizeSum_erase`; `Store.put_wf`, `delete_wf`,
  `deleteRange_wf`, `clear_wf` (records stay strictly sorted and the byte count equals the sum of the record
  sizes); `Fs.usage_eq`; `Manager.usageOf_sum`.
- File system: `writable_tree` (writes are invisible until close), `close_atomic`, `lookup_put_same`,
  `lookup_put_other`, `resolve_iff`, `removeAll_lookup_other`, `removeAll_lookup_under`, `get_invalid_name`,
  `same_iff`.
- Web Locks: `op_excl` (every command keeps mutual exclusion: any two held locks are of different names or
  both shared), `settle_excl`, `settleStep_no_overtake`, `ifAvailable_no_wait`, `steal_alone`,
  `Locks.opFor_noninterference`.

- File pickers: `answer_refuses`, `answer_never_ok`, `valid_security`, `invalid_type`, `validSuffix_spec`,
  `validId_length`.
- Storage buckets: `validName_spec`, `open_mem`, `delete_not_mem`, `delete_unknown`, `insert_sorted`,
  `op_sorted`, `Buckets.opFor_noninterference`.
- Cookie Store: `setFromScript_store`, `store_keeps`, `set_keeps_host` (a set never adds a cookie for another
  host), `read_host` (a read answers only the page's host's cookies, never `HttpOnly`), `changes_sub`,
  `set_refuses_eq`.

- Cache API: `hits_self` (a GET request matches the entry stored with it, under any options), `put_matches`,
  `putCheck_method`, `Caches.opFor_noninterference`; `Manager.op_local` now over the three APIs.

Tested only (`#guard`):

- The order image of doubles against IEEE order (the standard property of sign-and-magnitude bits; not
  proved against a model of doubles); code-unit order; token round trips of keys.
- Key paths, key extraction, key injection, key path validity.
- Index maintenance (`Store.indexOk` is the decidable statement; unique and multiEntry cases).
- `nextunique` and `prevunique` cursors; `continue(key)` and `continuePrimaryKey`.
- The command layer: exception order, scheduling of transactions, auto-commit, open/upgrade/blocked/delete,
  key generators (`IdbTests.lean`); the file system's commands and lock modes.

Open:

- That `pump` commits exactly when the specification says (a statement over the whole command machine).
- That an index's entries equal the index keys of the store's records, as an invariant of every operation.
- The store invariant `Store.wf` carried through `exec` for every reachable transaction.
- That the tree stays well-formed (every entry's parent is a directory) under every command.
- A round-trip theorem for the key tokens (`Key.ofToks (k.toToks) = some k` for keys nested at most 64).

## Privacy and risk flags

- No API here reads the host: quotas are constants, `lastModified` is a counter, the file system has no host
  path. `estimate()` is proved a function of the caller's own shelves.
- Storage key: `Key.site` is always empty today (the engine passes the page's origin). A third-party frame
  with a session of its own therefore shares its origin's first-party shelf. Partitioning by top-level site
  needs the frame session to know its top-level origin; until then this is **not** third-party partitioned
  (WPT `idb-partitioned-*`). Flagged as open.
- A dedicated worker is a session with its own `web_api` state: its storage is separate from its page's
  (stricter than the standards, not a leak; pages that share data with a worker through IndexedDB do not work).
- Timing is not covered by any theorem here.
- No risk token (`skills/lean-risk-flags`) is taken: nothing here is crypto, and no fallback path exists (an
  engine without the ops leaves the globals undefined).

## Transaction activity and promise jobs

HTML runs a microtask checkpoint after each event listener callback, so the jobs a listener queues (the
continuation of an `await` on a request) run while the transaction is still active. The page side has no
synchronous checkpoint, so after dispatching an event of a transaction it tells Lean `done` (inactive) only
after eight promise-job hops: a continuation queued by a listener, and continuations up to eight jobs deep,
run first; a timer callback queued by a listener runs after, with the transaction inactive. The exact
statement (inactive after the checkpoint, whatever its depth) is open.

## Performance

A page that names none of these globals pays nothing: the prelude defines them lazily, and the `web_api`
state holds three empty lists. Object store and index operations are single passes over a sorted list
(insert, delete, each cursor step are linear in the store's size). That is the specification form; a tree
with the same answers, proved equal to it, is the follow-up, and matters from some thousands of records.
No timing was measured: the engine was not built locally (cloud check only).

## Blocked on other work

- Shared worker and service worker variants (IndexedDB 2,682 Chrome subtests, fs 413, storage 180,
  cookiestore 273, web-locks 219): the engine skips them; they need SharedWorker and service workers.
- Storage shared between a page and its dedicated workers, and between same-origin frames with their own
  sessions: needs one storage state per browsing context group.
- `FileSystemWritableFileStream` as a `WritableStream` (`getWriter`, `pipeTo`): used when the engine has
  `WritableStream`; else only its own methods.
- Storing a `FileSystemHandle` in IndexedDB or sending one by `postMessage`: needs structured serialisation of
  platform objects across the boundary.

## Not done in this change

A bucket's own storage (IndexedDB, CacheStorage, file system, locks) is not routed to the bucket.

## Questions for the owner

1. Persistence: should any of this be written to disk, and under what policy (per origin, with a user
   prompt, never for third parties, cleared with history)? Until decided it stays in memory.
2. If persistent: a local disk backend, a pod backend, or both? For a pod: which container holds an origin's
   data, and may other pod clients read it (one resource per database, or one per record)?
3. What should `navigator.storage.persist()` answer once storage can persist: granted silently, by a prompt,
   or by a browser setting?
4. Quota: 512 MiB for each API and key is an arbitrary constant. Is a fixed constant the wanted policy
   (it reveals nothing about the host), and which value?
5. Should a dedicated worker share its page's storage (the standards say so), given that today each is a
   separate session?

## Measured

(filled in from the cloud checks)
