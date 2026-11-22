# Read-only RPC captures and Lean call comparisons

Run with Node 22 or later from `formal/lean4/evm-cleanroom`. The host reads public
chain data through seven allowlisted JSON-RPC methods. It can save the block and
its parent, target runtime code, `eth_call` output, and a selected transaction
and receipt. The capture preserves chain-specific fields such as OP deposit
metadata. A capture can be made without building the Lean executable.

| `--network` | Chain ID | Chain type | Default RPC |
| --- | ---: | --- | --- |
| `ethereum-mainnet` | 1 | Ethereum L1 mainnet | `https://ethereum-rpc.publicnode.com` |
| `ethereum-sepolia` | 11155111 | Ethereum L1 testnet | `https://ethereum-sepolia-rpc.publicnode.com` |
| `amoy` | 80002 | Polygon PoS sidechain testnet | `https://polygon-amoy.drpc.org` |
| `polygon` | 137 | Polygon PoS sidechain mainnet | `https://polygon.drpc.org` |
| `op-sepolia` | 11155420 | OP Stack rollup testnet | `https://sepolia.optimism.io` |

[Ethereum RPC endpoints](https://ethereum.publicnode.com/) ·
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
  Every `eth_call` includes an explicit zero value.
- Use `--timeout-ms` to change the 10-second deadline for each RPC request and
  the local subprocess. Each RPC response has a 4 MiB body limit. The host
  records method and parameters, timing, transport details and body SHA-256 for
  successful responses. RPC errors retain their integer code and exact revert
  bytes when the provider uses a recognised format. The provider's free-form
  error text is discarded.

With `--lean-exe`, the host compares the halt kind and complete return or revert
bytes from `--pure-frame-call`. Lean checks each opcode as it executes in a
read-only frame with zero call value. The full runtime is passed through,
including compiler metadata. A comparison requires the
`zero-value-context-free-v1` marker from the executable. If the execution
reaches a storage, external-call, or context-dependent opcode outside the policy,
the provider observation can still be captured and the comparison remains
`unverified`. Exceptional, unsupported and truncated executions also remain
unverified. The local executable has a 32 KiB stdout and stderr buffer limit.
`--gas` and `--fuel`
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
local comparison with the built Lean executable as well as the test stubs. The
native test calls `ge(uint256,uint256)` at the `2^255` boundary and checks an
unknown selector's empty revert. It uses the full compiled Solidity runtime
and pins its SHA-256. [Source and compiler fixture](../differential/fixtures/solidity-pure/fixture.json)

The suite pins two earlier captures from 22 November 2026 by SHA-256. The
assertions include the exact synthetic code, calldata, output and request
times. The OP Sepolia capture includes a type-`0x7e` deposit transaction and
its receipt. Offline tests recheck the recorded output with the current
comparison policy and verify the expected change from an implicit to an
explicit zero value in the call parameters. The saved transcripts retain the
original request parameters. Local proxy loopback addresses were omitted from
the saved samples. The receipts and block data remain provider assertions.
[OP Sepolia block 51770430](evidence/op-sepolia-51770430.json) ·
[Polygon PoS block 97758671](evidence/polygon-97758671.json)

## Live Solidity calls

On 22 November 2026, PublicNode and guarded Lean both returned the official
Uniswap V3 factory address `0x1f98431c8ad98523631ae4a59f267346ea31f984` for
`factory()` (`0xc45a0155`) on the deployed Ethereum mainnet SwapRouter
`0xe592427a0aece92de3edee1f18e0157c05861564`. The call used zero value and
the provider's deployed runtime at block `26473707`, hash
`0x46ec7e5fad2d4fe2588f1ea1ce8983156fbb7ab78a3fce0c56a46a61dbea06ef`.
The saved capture retains all 12,070 code bytes and the exact RPC response.
[Mainnet capture](evidence/ethereum-mainnet-26473707-swaprouter-factory.json) ·
[Uniswap deployment addresses](https://developers.uniswap.org/docs/protocols/v3/deployments/v3-ethereum-deployments)

A separate dRPC EIP-1186 proof supplied eight account trie nodes for that
block and address. The verifier re-encodes the header and checks its hash,
verifies the account path from that header's state root, and matches the
proven code hash to Keccak-256 of the captured runtime. The code hash is
`0xbb90113d2f9a5e9b7feb15a1d1fff06c1ee1575b3f9b1181778ffd0cf633e7ea`.
The check rejects a changed byte and a changed state root. The providers
supply chain selection and canonicality. The local execution comparison
covers the getter's return bytes.
[Account proof](evidence/ethereum-mainnet-26473707-swaprouter-code-proof.json)

On Ethereum Sepolia, PublicNode and guarded Lean returned
`0x0227628f3f023bb0b980b67d528571c95c6dac1c` from `factory()` on the
deployed SwapRouter02 at block `12191766`.
[Ethereum Sepolia capture](evidence/ethereum-sepolia-12191766-swaprouter02-factory.json)

Both captures used the native build at local source revision
`254c8329a8cd7da95b51901ba2091fa3ce43a97e`, executable SHA-256
`64a6f3a563bdec24a7516d5a2a6698891ee193efa843ed68bb9e838fca6aad77`,
and capture source Git blob `427d0f65b83fc195f17bc0a1cb1f021f89a2ee14`.
The public baseline uses the same Lean package sources and toolchain.
The offline test suite replays the saved response parameters and complete
runtime with the currently built executable. [Public Lean baseline](https://github.com/danbri/factoidal-core/commit/d3843c42d3b9c6fea8e96c3d0eebd65890dbea4b)

```sh
node scripts/rpc/capture.mjs --network ethereum-mainnet \
  --address 0xe592427a0aece92de3edee1f18e0157c05861564 --data 0xc45a0155 \
  --block 0x46ec7e5fad2d4fe2588f1ea1ce8983156fbb7ab78a3fce0c56a46a61dbea06ef \
  --lean-exe "$PWD/.lake/build/bin/evm-subset" --out ethereum-mainnet-factory.json

# Install the EELS witness dependencies with the resolution pinned by the CI workflow.
node scripts/eels/verify-rpc-code-witness.mjs \
  scripts/rpc/evidence/ethereum-mainnet-26473707-swaprouter-factory.json \
  scripts/rpc/evidence/ethereum-mainnet-26473707-swaprouter-code-proof.json
```

See [the L1 replay issue](https://github.com/danbri/factoidal-core/issues/796)
for work on signed contract transactions, receipts and state transitions.

On 22 November 2026, the OP Sepolia provider and guarded Lean executable
returned the ABI word `6` for `decimals()` (`0x313ce567`) at the deployed
Jovian GasPriceOracle implementation `0x4f1db3c6abd250ba86e0928471a8f7db3afd88f1`.
The zero-value call used the runtime read from block `51771054`, hash
`0x4fa96dd7ac9bac264d2dcad1399e5b2ed422cd8bd21a6d1fb56c51f928407bbe`.
The full 7,848 bytes of captured code give Keccak-256
`0xe9fc7c96c4db0d6078e3d359d7e8c982c350a513cb2c31121adf5e1e8a446614`
using `@noble/hashes` 2.4.0, the runtime hash specified for the Jovian deployment.
This compares one call and identifies the captured bytes. State authentication
and the other methods of the contract are outside this check.
[Capture](evidence/op-sepolia-jovian-decimals-51771054.json) ·
[OP Stack Jovian specification](https://specs.optimism.io/protocol/jovian/derivation.html#gaspriceoracle-deployment)

The same day, OP Sepolia block `51771081` and Polygon PoS block `97759492`
returned the ABI word `1` for `ge(2^255 + 1, 2^255)` from the compiler fixture.
Those calls used state overrides containing all 123 bytes of the compiled
runtime, including metadata. Both outputs matched guarded Lean. The offline
suite pins and replays all three capture files with their explicit zero-value
parameters. [OP Sepolia override](evidence/op-sepolia-solidity-ge-51771081.json) ·
[Polygon PoS override](evidence/polygon-solidity-ge-97759492.json)

[RPC implementation tracking](https://github.com/danbri/factoidal-core/issues/734) ·
[Solidity call tracking](https://github.com/danbri/factoidal-core/issues/736)
