# Ethereum L1 deployed-code calls, 22 November 2026

The read-only capture tool matched guarded Lean against two deployed Uniswap
getters on Ethereum L1. The new profiles check the provider's chain ID before
requesting blocks, code or calls. Both comparisons use the full deployed
runtime and explicit zero value.

| Network | Block | Call | ABI address returned |
| --- | ---: | --- | --- |
| Ethereum mainnet | 26,473,707 | Uniswap V3 SwapRouter `factory()` | `0x1f98431c8ad98523631ae4a59f267346ea31f984` |
| Ethereum Sepolia | 12,191,766 | Uniswap V3 SwapRouter02 `factory()` | `0x0227628f3f023bb0b980b67d528571c95c6dac1c` |

PublicNode supplied the captured blocks, bytecode and call responses. On
mainnet, dRPC supplied an eight-node EIP-1186 path at the exact same block
hash. The verifier recomputed the execution header hash and authenticated
the SwapRouter account against the header's state root. Keccak-256 of the
full 12,070-byte runtime matched the proven account code hash
`0xbb90113d2f9a5e9b7feb15a1d1fff06c1ee1575b3f9b1181778ffd0cf633e7ea`.
A changed runtime byte and a changed state root both failed verification.
[Capture commands and proof report scope](../formal/lean4/evm-cleanroom/scripts/rpc/README.md#live-solidity-calls) ·
[Uniswap deployment addresses](https://developers.uniswap.org/docs/protocols/v3/deployments/v3-ethereum-deployments)

The captures used the native Lean build at local revision
`254c8329a8cd7da95b51901ba2091fa3ce43a97e` with executable SHA-256
`64a6f3a563bdec24a7516d5a2a6698891ee193efa843ed68bb9e838fca6aad77`.
The public baseline has identical Lean package sources and toolchain. Its
Git tree `8cefef908c65d6832363e52a9109d2ef51765f4d` matches local revision
`75810b566`. The extended offline RPC suite passed 46 of 46 tests against
the same native executable. CI independently repeats the capture comparisons
and the code-witness verification from pinned inputs.
[Public baseline](https://github.com/danbri/factoidal-core/commit/d3843c42d3b9c6fea8e96c3d0eebd65890dbea4b) ·
[Implementation PR](https://github.com/danbri/factoidal-core/pull/798)

Lean compares the admitted getter path's halt kind and full return bytes.
The header and MPT verifier uses the pinned EthereumJS dependencies.
Providers supply canonical chain selection. Signed modern contract
transaction replay, receipt generation and authenticated transaction state
updates remain separate work.
[Mainnet contract replay](https://github.com/danbri/factoidal-core/issues/796)
