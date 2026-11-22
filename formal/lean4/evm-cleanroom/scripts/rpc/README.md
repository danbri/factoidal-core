# Read-only RPC captures and Lean call comparisons

Run with Node 22 or later from `formal/lean4/evm-cleanroom`. The host reads public
chain data through seven allowlisted JSON-RPC methods. It can save the block and
its parent, target runtime code, `eth_call` output, and a selected transaction
and receipt. The capture preserves chain-specific fields such as OP deposit
metadata. A capture can be made without building the Lean executable.

| `--network` | Chain ID | Chain type | Default RPC |
| --- | ---: | --- | --- |
| `amoy` | 80002 | Polygon PoS sidechain testnet | `https://polygon-amoy.drpc.org` |
| `polygon` | 137 | Polygon PoS sidechain mainnet | `https://polygon.drpc.org` |
| `op-sepolia` | 11155420 | OP Stack rollup testnet | `https://sepolia.optimism.io` |

[Polygon RPC endpoints](https://docs.polygon.technology/pos/reference/rpc-endpoints) ·
[Optimism Superchain Registry](https://github.com/ethereum-optimism/superchain-registry/blob/main/chainList.json)

After building `evm-subset`, this example asks the provider to run synthetic
runtime code at a test address. The code loads the first calldata word, writes
it to memory and returns 32 bytes. Public RPC reads need no signer or wallet.
With the sample calldata, both executions should return
`0x1234567800000000000000000000000000000000000000000000000000000000`.

```sh
node scripts/rpc/capture.mjs --network op-sepolia \
  --address 0x1111111111111111111111111111111111111111 --data 0x12345678 \
  --code-override 0x60003560005260206000f3 \
  --lean-exe "$PWD/.lake/build/bin/evm-subset" --out op-sepolia-call.json
```

- Use `--block` with a number or hash to target a particular block. The default
  `latest` is resolved once. State queries ask for the canonical block by hash
  and the capture checks its hash by height before and after acquisition. A
  provider that rejects the [EIP-1898](https://eips.ethereum.org/EIPS/eip-1898)
  selector cannot supply those reads through this tool.
- Use `--tx HASH` to include a transaction and receipt from that block. Their
  identities and indices must agree with the block's transaction list. Archive
  access may be needed for older state.
- Use `--rpc URL` to select a provider with the same chain ID. Evidence records
  its origin without the URL credentials, path or query. On a Node version
  with `--use-env-proxy`, that flag before the script path enables configured
  environment proxies. The logged transport peer can be the proxy.
- Omit `--code-override` to call the deployed runtime at the address. The
  state override feature depends on the provider. An override is supplied
  only to the simulation and stored with the `synthetic-state-override` label.
- Use `--timeout-ms` to change the 10-second deadline for each RPC request and
  the local subprocess. Each RPC response has a 4 MiB body limit. The host
  records method and parameters, timing, transport details and body SHA-256 for
  successful responses. RPC errors retain their integer code and exact revert
  bytes when the provider uses a recognised format. The provider's free-form
  error text is discarded.

With `--lean-exe`, the host compares the halt kind and complete return or revert
bytes from `--frame-call`. It admits only a conservative context-free bytecode
subset, scanning the runtime with PUSH data skipped. Contracts that read block
or account context, storage, or call other code still yield provider evidence
when the capture succeeds. Local comparison remains `unverified` for them,
for exceptional or unsupported executions, or for truncated observations. The
local executable has a 32 KiB stdout and stderr buffer limit. `--gas` and `--fuel`
set local budgets only. A match covers one call output and leaves protocol gas,
state roots, block hashes, transaction execution, and chain consensus unverified.
The provider supplies the chain observations and canonicality assertions.

The CLI creates a new evidence file with exit `0` for a successful capture or a
requested comparison that matches. Exit `2` leaves the captured evidence with an
unverified or mismatching comparison. Exit `1` indicates a capture, file or RPC
call error. A validated `eth_call` error without recognised revert data can leave
an evidence file labelled `call-error`.

```sh
node --test scripts/rpc/capture.test.mjs
EVM_RPC_TEST_LEAN_EXE="$PWD/.lake/build/bin/evm-subset" node --test scripts/rpc/capture.test.mjs
```

The tests use a deterministic local mock. The second command exercises the
local comparison with the built Lean executable as well as the test stubs.

The suite also replays two captures from 22 November 2026 through the host
without contacting the original providers. The saved assertions include the
exact synthetic code, calldata, output and request times. The OP Sepolia
capture includes a type-`0x7e` deposit transaction and its receipt. The replay
checks the saved request IDs and parameters, block relationships, and comparison
output. It pins the files by SHA-256. Local proxy loopback addresses were
omitted from the saved samples. The receipts and block data remain provider
assertions. [OP Sepolia block 51770430](evidence/op-sepolia-51770430.json) ·
[Polygon PoS block 97758671](evidence/polygon-97758671.json)

[Ethereum implementation tracking](https://github.com/danbri/factoidal-core/issues/734)
