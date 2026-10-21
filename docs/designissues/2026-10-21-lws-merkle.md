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

MEASUREMENTS

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
