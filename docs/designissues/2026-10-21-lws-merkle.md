# LWS Merkle hashes: the first part of issue 919 (2026-10-21)

Tracking: https://github.com/danbri/factoidal/issues/919 ("Explore Merkle
trees in Factoidal's data management (LWS server and beyond)").

Owner, 2026-10-21, verbatim: "After, yes. As an optional, probably default
off until we settle on stronger motivating usecase but good to have the
fundamentals there and I believe we have Merkel in the codebase somewhere
already."

The LWS drafts (w3c/lws-protocol 9a08ff65) define no integrity mechanism, so
everything here is an option of this server, off by default, and every
member it adds names the issue.

## What is built

| part | where | what |
|---|---|---|
| hashes | `formal/lean4/L4Factoidal/LWS/Merkle.lean` | resource: SHA-256 of the stored bytes. Container: SHA-256 of tag 2, the member count (8 bytes, big-endian) and the root of the `Storage/BlockMerkle.lean` tree whose leaves are `leafWith h (digest ++ path)` over the listed members in increasing path order |
| hasher | `Merkle.haclHasher`, `BlockMerkle.pureHasher` | HACL* SHA-256 (`Crypto.sha256Hacl`, the vendored C, in the native build and in the wasm module) at run time; pure Lean FIPS 180-4 SHA-256 in every `#guard`; every theorem holds for any hasher |
| maintenance | `MerkleStore S L` | a store wrapper whose state carries the invariant `MkOk` as a proof; it sits under `TypeIndex.IndexedStore` (`LwsBackend` in `MerkleHttp.lean`), so the two wrappers compose and neither repeats the other |
| write | `putData`, `removeData`, `walk` | the digest of the written path, then of each container above it, stopping at the first container whose digest does not change; a container entry written again (a new modification time) keeps its digest |
| open | `rebuild`, `IxState.ofMerkle` | one pass after one sort by path length: members before containers. No hash is in a snapshot |
| HTTP | `formal/lean4/L4Factoidal/LWS/MerkleHttp.lean`, `decorate` | `Repr-Digest` (RFC 9530) on a 200 or 206 GET or HEAD of a resource with its stored media type; `Factoidal-Merkle-Root`, the listing member `…/919#merkleRoot` and the same Turtle statement on a container; the storage description member `…/919#storageMerkleRoot` |
| switch | config `merkle`, `listen({ merkle: true })`, `lws-serve --merkle`, `tools/lws-touchstone.sh --merkle` | off: `MkState.hasher = none`, nothing computed, `decorate_off` |

Decisions, each with its reason:

* The members of a container are the members its listing shows (direct
  members, not auxiliary). An ACL or `.meta` resource has a digest but changes
  no root. The tree membership also requires the member's path to be longer
  than the container's (`mcontains`). That holds for every path `validTarget`
  admits (it starts with `/`, and `parent?` drops the last segment), and it
  gives the proofs a well-founded order with no reasoning about `splitOn`.
* The count is bound beside the root. A Bitcoin-style tree repeats an
  unpaired last digest, so `[a, b, c]` and `[a, b, c, c]` have one root with
  no collision (CVE-2012-2459). With the count, `rootWith_inj` needs lists of
  equal length only.
* A leaf is `digest ++ path`: the digest has a fixed size (32 bytes), so the
  two parts are recovered from the bytes (`memberBytes_inj`).
* Under authorization the roots go to the storage controller only. A root is
  computed from the digests of resources a reader of the listing may not read;
  with a small container a reader could confirm a guess of such a resource's
  bytes offline. `Repr-Digest` is shown with every 200 or 206: its reader has
  the bytes.
* Entity tags do not change in this step (coordinator, 2026-10-21: "Do NOT
  change ETags in this step (they stay as they are), so Touchstone is
  unaffected"). The cost is a stated shortfall: a listing that carries a root
  member can change while its strong ETag stays (RFC 9110 §8.8.1). It is an
  expected failure in `tests/lws/merkle.mjs` naming issue 919; use case 1
  below removes it.

## Theorems

All in `L4Factoidal/LWS/Merkle.lean` unless named otherwise; `#print axioms`
gives only `propext`, `Classical.choice`, `Quot.sound`.

* `MkOk.dig_eq_recompute`, `MkState.dig_eq_recompute`: the maintained digests
  equal `recompute`, a recomputation from the store alone (`lookup` and
  `paths`), at every path, for every state of `MerkleStore` (every state the
  server reaches, since each state carries its proof).
* `MkOk.upd`, `walk_ok`, `putData_ok`, `removeData_ok`, `merkleStoreLaws`: one
  write keeps the invariant; the wrapper satisfies every store law.
* `rebuild_ok`: the one-pass build at open satisfies the invariant.
* `dataDigest_changes`: different bytes give a different digest.
  `containerDigest_inj`: a container's digest binds its member list.
  `parent_digest_changes`, `change_reaches_ancestor`: a changed digest of a
  member reaches every container above it. Each states the collision-freedom
  of SHA-256 as the hypothesis `BlockMerkle.NoCollision` over the byte strings
  hashed at one path in the two states, and a fixed output size (32 bytes,
  `pureHasher_size` from `Crypto.sha256_size`). A global injectivity of a
  hash with 32-byte outputs cannot hold, so a theorem that assumed it would
  prove nothing; the hypothesis here is over finite sets.
* `Storage/BlockMerkle.lean`: `nextLevelWith_inj`, `rootWith_inj` (equal roots
  of equal-length leaf lists give equal lists unless two hashed inputs
  collide), and `nextLevelWith_eq_nextLevelWithTR` (`@[csimp]`, a loop in place
  of one stack frame per two members).
* `MerkleHttp.lean`: `decorate_off`.

## Tests and measurements

* `#guard`s: `L4Factoidal/LWS/MerkleTests.lean` (FIPS 180-4 vectors; a deep
  write changes the digests of the resource and of every container above it
  and of no sibling; create, delete, move; an auxiliary resource changes no
  root; `recompute` and `rebuild` agree with the maintained digests; off keeps
  no data) and the checks at the end of `MerkleHttp.lean` (`Repr-Digest` of
  "hello", off adds nothing, no digest for another media type, a query, a
  write or a 404; roots only for a visible requester).
* `node tests/lws/merkle.mjs`, 2026-10-21: 18 pass, 0 fail, 1 xfail,
  0 skipped (out of 19). The xfail is the ETag shortfall above.
* `node tests/lws/scaling.mjs`, 2026-10-21 (wasm in Node, 4 vCPUs, another
  wasm build running on the machine): 16 pass, 0 fail (out of 16). The Merkle
  rows, one container of k members, 20 updates of one member per repeat,
  minimum of three repeats:

  | k | 20 updates, merkle on | 20 updates, merkle off | reopen, merkle on (hashes rebuilt) |
  |---|---|---|---|
  | 500 | 45.6 ms | 15.8 ms | 39.6 ms |
  | 1,000 | 55.9 ms | 15.4 ms | 101.2 ms |
  | 2,000 | 125.9 ms | 17.7 ms | 245.6 ms |

  Ratios 4k/k (bound 6.0; linear 4, quadratic 16): updates 2.52, reopen
  4.91. One write into a container of 2,000 members costs about 6.3 ms with
  the option on against 0.9 ms off: the extra cost is linear in the members
  of the container (about 3 microseconds per member per write), because the
  container's digest is recomputed from its member list (a sort, one leaf
  hash per member, one node hash per pair). A write to a resource in a small
  container costs a few hashes per level above it.

* Touchstone (`tools/lws-touchstone.sh`, pinned commit 10608723, 2026-10-21,
  after the merge of the alternative configurations):
  `--config both`: open 76 pass, 0 fail, 145 inapplicable; authorization 215
  pass, 0 fail, 6 inapplicable (out of 221 each), unchanged by this work.
  `--config both --merkle`: the same totals (76 and 215 pass, 0 fail).
  `--config all --unstable-search-results`: 220 passed in at least one
  configuration, 0 failed, 1 never applied (out of 221).
* Other gates on the same build: `lake build` exit 0;
  `tools/lean-unbuilt-modules.py --gate` exit 0 (832 of 832 modules reached);
  `Wasm/native-smoke.sh` 375 pass, 0 fail (out of 375); `npm test` 536 pass,
  0 fail, 2 skipped (out of 538); host-purity-lint 35 pass, 0 fail (out of 35).

## What remains of issue 919's seven use cases

| use case | status after this step |
|---|---|
| 1. Container ETags from child hashes | the root of every container is maintained and proved to change with any change below it (`change_reaches_ancestor`); ETags are not yet derived from it (the xfail in `tests/lws/merkle.mjs`). Remaining: an ETag from the root when the option is on, and the Touchstone run with it |
| 2. Sync and copy between storages | the roots are visible per container (to the controller), so a client can compare and go down only where they differ. Remaining: a sync client or op, and a cheaper container digest for very large containers (below) |
| 3. Snapshot and backup check | not built. The snapshot holds no hash by design; a check value (the storage root) could be written beside it and compared after the rebuild at open |
| 4. Tamper-evident change log | not built (a hash chain or an RFC 9162 log over the write log) |
| 5. Representation digests | built: `Repr-Digest` on GET and HEAD |
| 6. RDF content (RDFC-1.0 hashes as leaves) | not built; the leaves are the stored bytes |
| 7. Inclusion proofs for clients | the tree inside a container is `BlockMerkle`'s, whose `Tree.proof?` gives log-size inclusion proofs, and the containers chain to the storage root; no endpoint serves a proof yet |

Cost that remains open: a container's digest is recomputed from its whole
member list on each write below it (a sort of the member set, one leaf hash
per member and one node hash per pair), so a write into a container of k
members costs time linear in k. An incremental tree per container (a balanced
tree keyed by path, so one write updates log k nodes) would remove it.
