# Independent state-witness checks

Tracking: https://github.com/danbri/factoidal-core/issues/1043 (canonical RLP,
secure MPT proofs and authenticated initial state for the transaction-list runner).

The implementation under test is compiled Lean. These JavaScript files only
construct fixtures, call independent test libraries and invoke the actual native
CLIs. No EthereumJS, JavaScript trie, host proof result or recovered sender is
imported by the Lean implementation. Existing experimental Keccak still requires
the explicit `--dangerously-enable-unverified-keccak` option.

## Run

Install the existing exact oracle lock with `npm ci --ignore-scripts` in
`formal/lean4/evm-cleanroom/scripts/differential`. This does not change any package
or Lake dependency. From this directory, after the two native binaries are built:

```sh
node run.mjs --output /tmp/mpt-native-results.json
node transaction-lists.mjs --output /tmp/mpt-authenticated-list-results.json
```

`--proof-bin PATH` and `--list-bin PATH` override the default binaries in the
cleanroom's `.lake/build/bin` directory. The transaction-list harness additionally
accepts `--baseline-bin PATH`, which runs a separately built previous decoded-list
binary and compares its complete output with both current modes. Without that
option it performs 78 native calls; with it the count is 114.

Either harness accepts `--oracle-only` for fixture preparation without a native
binary. These reports explicitly record zero native calls and zero native passes.
`--fixtures PATH` writes reproducible requests and expectations, labelled as test
fixtures rather than execution results. `run.mjs` checks the exact complete
inventory; it does not silently skip failures or unknown fixture kinds.

All primitive requests have `schemaVersion:1`. RLP requests carry `encoding` and
optional `integerBytes`. MPT requests carry `root`, an already hashed 32-byte
`key`, and `proof`. State requests carry `stateRoot` and accounts with `address`,
`codeHex`, `accountProof`, and `storage` entries containing `key` and `proof`.
Addresses and storage keys are unsigned decimal strings. Proof nodes and roots
are hexadecimal byte strings. RLP does not need the cryptographic opt-in; MPT and
account admission do. Authenticated transaction-list requests have schema version
2 and the existing headers and decoded transactions plus those proof accounts.

## Measured inventory

The current native run has **189 cases passed, 0 failed**. Comparator mutation
checks are counted separately: **20 detected corruptions**.

| Group | Cases | What each group checks |
| --- | ---: | --- |
| Official RLP | 54 | All 28 positive and 26 negative upstream vectors |
| Additional RLP | 22 | Canonical scalars, widths, trailing items, nested malformation and length boundaries |
| Official secure tries | 15 | All 12 entries and 3 absences after reproducing all 3 published roots |
| Historical Frontier | 4 | Three real account proofs and their combined state admission |
| MPT structure | 10 | Leaf/extension/branch absence, inline children, 31/32-byte threshold, one-nibble extension |
| Proof bags | 5 | Unordered, redundant and unused nodes, including unused malformed bytes |
| Malformed MPT | 24 | Missing references, bad roots, HP flags/padding, arity, reference widths, malformed used bytes |
| MPT resources | 5 | A valid 65-node path, 128/129-node bags and 4,096/4,097-byte unused nodes |
| State binding | 5 | Account/storage/code binding, order independence, present-empty account, empty trie, scalar maxima |
| Malformed state | 28 | Code/root/proof changes, duplicate accounts/slots, scalar and tuple errors, zero storage leaves |
| Transport | 17 | Required opt-in, forbidden host overrides, malformed hex, duplicate/escaped keys and lexical limits |

The separate execution integration has **36 lists passed, 0 failed**: 30 complete
execution matches, 5 matching first-rejection results and 1 matching local
execution boundary. There are 344 retained signed transaction occurrences in
those lists; the accepted lists contain 327 transactions. Five witness-tampering
controls fail before a deliberately zero-fuel transaction can run. A sixth native
control preserves the distinction between an authenticated present-empty account
and the runner's current unsupported empty-account profile. An additional
comparator control rejects changed reference indexes and categories.

The 2026-11-24 Geth/EthereumJS results remain dated evidence. The integration
harness does **not** claim to rerun those execution clients. It reuses their
retained signed bytes, recovers each sender using an independent test library,
and reconstructs all 30 executed requests with exactly the original SHA256 before
replacing the parent state root and recomputing the child's parent hash. It builds
the new account/storage proofs independently, compares both current native modes,
and checks every receipt field and the final state commitment against that
retained evidence. The optional previous binary supplies a third regression check.

The six rejection/boundary fixtures did not retain their declared final execution
gas. Their reconstruction uses the valid block-gas limit as that declaration, so
it cannot introduce an earlier prefix-gas refusal. Their signed transactions,
prestate, expected first index and reason remain fixed. An initial zero declaration
did introduce an earlier refusal for the seven-blob list; the joined comparator
caught it, and the generator now records the distinction explicitly.

## Sources and independent reference

`evidence/mpt-sources.json` records exact upstream commits, file hashes, licences
and normative sections. The three `mpt-upstream-*.json` files are byte-exact copies
from `ethereum/tests` commit `c67e485ff8b5be9abc8ad15345ec21aa22e290d9`, with the
MIT notice in `mpt-upstream-LICENSE.txt`. The generator checks their SHA256 and Git
blob hashes before using them. It also checks the existing differential lock.

The independent trie/RLP libraries are `@ethereumjs/mpt` and `@ethereumjs/rlp`
10.1.3, resolved from the existing test-only lock. Before generated proofs qualify,
the trie constructor must reproduce all three published secure-trie roots. The
same library independently checks the generated membership/nonmembership and
account/storage values. Hand-built invalid nodes are normative negative controls,
not claims that every invalid form is refused by that reference library.

There are three explicit reference API adaptations:

- EthereumJS RLP treats empty input as an API sentinel. Requiring an exact
  canonical decode/encode round trip rejects that sentinel as an encoded item,
  as the published negative vector requires.
- The convenience proof API requires the root node first. The public
  `updateMPTFromMerkleProof` API can populate an unordered bag under an explicitly
  supplied root; lookup then uses that root. No reference implementation is
  copied or translated.
- `get(key, true)` also treats the canonical empty root as a missing node. Only
  for the exact empty root independently obtained from a new reference trie does
  the adapter use the library's normal empty lookup. Every other missing node
  remains an error.

## Semantics and limits of the claim

Canonical RLP consumes the whole used item and all nested payloads. Byte `00` is
valid RLP bytes but is not canonical integer zero; integer zero is the empty
payload. Account nonce/balance are bounded by 8/32 bytes, and storage values by 32
bytes. A zero storage value must be proved absent. The account key is Keccak of
the 20-byte address; the storage key is Keccak of the 32-byte big-endian slot.
Storage proofs use the root decoded from the authenticated account. Code bytes
must match the code hash in that account; no supplied balance, nonce, existence,
storage value, storage root or code hash can replace a derived value.

Nodes shorter than 32 encoded bytes are embedded; longer nodes use a hash
reference. A hash child cannot point to a short node. HP flags are 0 through 3,
even padding is zero, extension paths are nonempty, and a leaf's remaining length
must fit the fixed 64-nibble key. A one-nibble extension and an empty-suffix leaf
are valid. Missing a referenced hash never becomes absence. A divergent valid
leaf/extension path or an empty selected branch proves nonmembership.

Proof arrays are bounded bags. Input order and redundant entries do not change
the result. Unused bytes are not interpreted as trie nodes, but still count
towards resource limits. Every used node must have a canonical complete RLP
encoding. Local MPT bounds are 128 supplied nodes, 4,096 bytes per node and 65
traversal steps. State admission also has aggregate node/byte, account and slot
limits; transport bounds input bytes, nesting and numeric work. Local resource
refusal is distinct from malformed witness and from an invalid Ethereum
transaction. The present tests exercise the reachable CLI bounds; they do not
claim to exercise every pure-admission budget through the smaller JSON envelope.

An authenticated witness is relative to the caller's declared state root. This
does not prove that the root belongs to the canonical chain or that the entire
unseen trie is globally canonical. In particular the local verifier does not
check global branch occupancy or the global absence of shorter keys. It does not
authenticate signed senders, compute the poststate/receipt/transaction commitment
in Lean, implement all block system operations, or prove Keccak refinement.
Those remain obligations of the full Ethereum implementation. The account and
storage proof checks are executed on the actual transaction-list entry point;
the scripts do not supply derived balances, nonces or storage to that mode.
