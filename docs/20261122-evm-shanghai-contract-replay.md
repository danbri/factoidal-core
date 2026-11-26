# Authenticated Ethereum mainnet contract transaction replay

Lean executed the signed index-zero 1CAT transfer in Ethereum mainnet block
19,100,013 under Shanghai rules. It reproduced the authenticated receipt's
status, exact 33,987 gas and ordered Transfer log. The host derived the bloom
and checked the resulting receipt bytes against the published header. The
execution returned the ABI word 1 and applied a 4,800-gas refund. EthereumJS 10.1.3
and Geth 1.17.10 independently reproduced the same receipt and account
effects. [Transaction replay issue](https://github.com/danbri/factoidal-core/issues/796) ·
[Mainnet transaction](https://etherscan.io/tx/0xe02eb8e49aa4385b3fac6ccc5a061b5aded14f9f6dd674a4e7a8b7ad55ad85d0)

The fixture contains the signed RLP for
`0xe02eb8e49aa4385b3fac6ccc5a061b5aded14f9f6dd674a4e7a8b7ad55ad85d0`,
the parent and containing execution headers, and two-node inclusion proofs
for the transaction and receipt at index zero. The replay recomputes both
header hashes, recovers the transaction sender, and checks exact receipt
and transaction bytes against their respective header roots.
[Offline fixture](../formal/lean4/evm-cleanroom/evidence/historical-1cat-shanghai-19100013.json)

## State and provenance

Blast and MEV Blocker supplied matching EIP-1186 proofs against the parent
state root
`0x7c77a193bfb11effde3324d0ad44010bd84e60f361e5b65c6cb8aa0ffa19d334`.
The fixture authenticates the sender, contract and fee beneficiary, the full
6,583-byte contract runtime, and every touched storage slot. The four
slots include the omitted whitelist key proved absent, packed slot five
and both token balance slots. The sender's token slot is deleted and the
recipient's balance increases. An EthereumJS trace checks that every
executed storage read and write is from the authenticated set.

During acquisition PublicNode supplied
`eth_getBlockByNumber("0x123716d", true)` and the exact signed bytes from
`eth_getRawTransactionByHash`. MEV Blocker supplied the 127 block receipts
with `eth_getBlockReceipts("0x123716d")`. Building the full transaction
and receipt tries reproduced both published roots. Only the index-zero
proofs are needed in the offline fixture. Blast, MEV Blocker and BlockReq
independently returned the same receipt for the selected transaction.
Both archive providers supplied the parent proofs with
`eth_getProof(address, slots, "0x123716c")` and the same code for the
contract at that block.

The sparse trie updater begins from the authenticated parent root and
uses each engine's returned account effects. Lean, EthereumJS and Geth
give the same derived intermediate world root
`0x4ec90276be487d2567d41039696e1bb75b3fa8cb796fc9705f5d83c606a17000`.
The target storage root
`0x4fb8888e09be2dd7e1b31f7e39e670b7820adf8d179f382c34481a632ba0a08a`
also matches the target account's independently proven storage root in the
final block. The global intermediate root is derived for transaction zero.
Canonical chain selection comes from the providers. Signed envelope decoding,
signature recovery, receipt encoding, and header and trie verification use
the pinned EthereumJS host libraries.

## Run the offline check

Use the EELS dependencies pinned by the workflow. From `formal/lean4`,
build the replay entry point with `lake -d evm-cleanroom build evm-call-transaction`.
From `formal/lean4/evm-cleanroom`, run this command with the pinned Linux amd64
Geth 1.17.10 `evm` executable for the additional Geth comparison.

```sh
EVM_GETH_EXE=/path/to/geth/evm node scripts/eels/replay-authenticated-contract.mjs \
  evidence/historical-1cat-shanghai-19100013.json "$PWD/.lake/build/bin/evm-call-transaction"
```

The replay explicitly opts in to Lean's unverified Keccak implementation.
The controls reject the same execution without that opt-in, a missing
authenticated slot, a changed runtime byte, a changed storage claim, an
altered receipt gas count and an incorrect sparse-trie key transform.
[Checkpoint and CI](https://github.com/danbri/factoidal-core/pull/798)
