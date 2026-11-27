import EthereumWallet.Abi.Hash

/-!
# Pinned contract addresses (public data) and EIP-55 display

Addresses of well-known deployments on Ethereum mainnet (chain id 1) and
Sepolia (chain id 11155111), each with where it was taken from. They are
data, not code: nothing here is copied from the contracts.

The strings are EIP-55 mixed-case checksummed. The vector executable checks
every entry against `checksumAddress`, so a mistyped digit fails the build's
tests.
-/

namespace EthereumWallet.Calls

open EthereumWallet.Abi

def mainnet : Nat := 1
def sepolia : Nat := 11155111

/-- A 20-byte address as a number below `2^160`. -/
def addrOfHex (s : String) : Nat :=
  match unhex s with
  | some b => natOfBytes b
  | none => 0

/-- EIP-55 mixed-case checksum form, with `0x`. -/
def checksumAddress (a : Nat) : String :=
  let hex := (hexOf (beBytes 20 a)).toList
  let h := keccak256 (hex.map fun c => UInt8.ofNat c.toNat)
  let nibble (i : Nat) : Nat :=
    let b := (h.getD (i / 2) 0).toNat
    if i % 2 == 0 then b / 16 else b % 16
  "0x" ++ String.ofList (hex.zipIdx.map fun ci => if nibble ci.2 ≥ 8 then ci.1.toUpper else ci.1)

/-- True for a `0x` string of 40 hex digits whose letter case is the EIP-55 checksum. -/
def validChecksum (s : String) : Bool :=
  s.length == 42 && checksumAddress (addrOfHex s) == s

structure Pinned where
  name : String
  chainId : Nat
  address : String
  source : String

/-- Uniswap's v3 deployment table, read on 2026-11-27. The page gives the Sepolia WETH
    address in lower case; the checksum form here is computed. -/
def uniswapDeployments : String :=
  "https://developers.uniswap.org/docs/protocols/v3/deployments/v3-ethereum-deployments"

/-- Circle's USDC address table, read on 2026-11-27. -/
def circleAddresses : String :=
  "https://developers.circle.com/stablecoins/usdc-contract-addresses"

def pinned : List Pinned := [
  ⟨"WETH9", 1, "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2", uniswapDeployments⟩,
  ⟨"WETH9", 11155111, "0xfFf9976782d46CC05630D1f6eBAb18b2324d6B14", uniswapDeployments⟩,
  ⟨"UniswapV3SwapRouter02", 1, "0x68b3465833fb72A70ecDF485E0e4C7bD8665Fc45", uniswapDeployments⟩,
  ⟨"UniswapV3SwapRouter02", 11155111, "0x3bFA4769FB09eefC5a80d6E87c3B9C650f7Ae48E",
    uniswapDeployments⟩,
  ⟨"UniswapV3Factory", 1, "0x1F98431c8aD98523631AE4a59f267346ea31F984", uniswapDeployments⟩,
  ⟨"UniswapV3Factory", 11155111, "0x0227628f3F023bb0B980b67D528571c95c6DaC1c", uniswapDeployments⟩,
  ⟨"UniswapV3QuoterV2", 1, "0x61fFE014bA17989E743c5F6cB21bF9697530B21e", uniswapDeployments⟩,
  ⟨"UniswapV3QuoterV2", 11155111, "0xEd1f6473345F45b75F8179591dd5bA1888cf2FB3", uniswapDeployments⟩,
  ⟨"Permit2", 1, "0x000000000022D473030F116dDEE9F6B43aC78BA3", uniswapDeployments⟩,
  ⟨"Permit2", 11155111, "0x000000000022D473030F116dDEE9F6B43aC78BA3", uniswapDeployments⟩,
  ⟨"USDC", 1, "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48", circleAddresses⟩,
  ⟨"USDC", 11155111, "0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238", circleAddresses⟩
]

def pinnedAddress? (name : String) (chainId : Nat) : Option Nat :=
  (pinned.find? fun p => p.name == name && p.chainId == chainId).map fun p => addrOfHex p.address

/-- Permit2 is deployed at the same address on every chain. -/
def permit2Address : Nat := 0x000000000022D473030F116dDEE9F6B43aC78BA3

/-- Largest `uint256`. -/
def maxUint256 : Nat := 2 ^ 256 - 1
/-- Largest `uint160`. -/
def maxUint160 : Nat := 2 ^ 160 - 1
/-- Largest `uint48`. -/
def maxUint48 : Nat := 2 ^ 48 - 1

end EthereumWallet.Calls
