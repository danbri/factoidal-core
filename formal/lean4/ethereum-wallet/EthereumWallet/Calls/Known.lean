import EthereumWallet.Abi.Event
import EthereumWallet.Calls.Addresses

/-!
# Known functions and events, and builders for their calldata

ERC-20, ERC-721, WETH9 and the Uniswap v3 `SwapRouter02` single-pool swaps.
Signatures are written from the published interfaces (EIP-20, EIP-721, the
WETH9 and SwapRouter02 ABIs), as public data.

`SwapRouter02` swap structs carry no deadline: the deadline is the first
argument of `multicall(uint256 deadline, bytes[] data)`, which reverts after
it. `swapWithDeadline` wraps swap calls that way.

Nothing here sends anything: these functions return bytes.
-/

namespace EthereumWallet.Calls

open EthereumWallet.Abi

/-! ## ERC-20 -/

def sigTransfer : FunctionSig := ⟨"transfer", [.address, .uint 256]⟩
def sigApprove : FunctionSig := ⟨"approve", [.address, .uint 256]⟩
def sigTransferFrom : FunctionSig := ⟨"transferFrom", [.address, .address, .uint 256]⟩
def sigBalanceOf : FunctionSig := ⟨"balanceOf", [.address]⟩
def sigAllowance : FunctionSig := ⟨"allowance", [.address, .address]⟩

def erc20Transfer (to amount : Nat) : List UInt8 :=
  encodeCall sigTransfer [.address to, .uint amount]
def erc20Approve (spender amount : Nat) : List UInt8 :=
  encodeCall sigApprove [.address spender, .uint amount]
def erc20TransferFrom (src dst amount : Nat) : List UInt8 :=
  encodeCall sigTransferFrom [.address src, .address dst, .uint amount]
def erc20BalanceOf (owner : Nat) : List UInt8 :=
  encodeCall sigBalanceOf [.address owner]
def erc20Allowance (owner spender : Nat) : List UInt8 :=
  encodeCall sigAllowance [.address owner, .address spender]

/-- Return data that is one `uint256` (`balanceOf`, `allowance`). -/
def decodeUintReturn (d : ByteArray) : Except Err Nat :=
  match decodeArgs [.uint 256] d with
  | .ok [.uint n] => .ok n
  | .ok _ => .error .nonCanonical
  | .error e => .error e

/-- What `transfer`/`approve`/`transferFrom` returned. Some deployed tokens return nothing. -/
inductive Erc20Return where
  | succeeded
  | failed
  | noData
  | malformed
  deriving Repr, DecidableEq

def decodeErc20Return (d : ByteArray) : Erc20Return :=
  if d.size == 0 then .noData
  else
    match decodeArgs [.bool] d with
    | .ok [.bool true] => .succeeded
    | .ok [.bool false] => .failed
    | _ => .malformed

def evTransfer : EventSig :=
  { name := "Transfer"
    params := [⟨"from", .address, true⟩, ⟨"to", .address, true⟩, ⟨"value", .uint 256, false⟩] }
def evApproval : EventSig :=
  { name := "Approval"
    params := [⟨"owner", .address, true⟩, ⟨"spender", .address, true⟩, ⟨"value", .uint 256, false⟩] }

/-! ## ERC-721 -/

def sigSafeTransferFrom : FunctionSig := ⟨"safeTransferFrom", [.address, .address, .uint 256]⟩
def sigSafeTransferFromData : FunctionSig :=
  ⟨"safeTransferFrom", [.address, .address, .uint 256, .bytes]⟩
def sigSetApprovalForAll : FunctionSig := ⟨"setApprovalForAll", [.address, .bool]⟩
def sigOwnerOf : FunctionSig := ⟨"ownerOf", [.uint 256]⟩
def sigGetApproved : FunctionSig := ⟨"getApproved", [.uint 256]⟩
def sigIsApprovedForAll : FunctionSig := ⟨"isApprovedForAll", [.address, .address]⟩

def erc721TransferFrom (src dst tokenId : Nat) : List UInt8 :=
  encodeCall sigTransferFrom [.address src, .address dst, .uint tokenId]
def erc721SafeTransferFrom (src dst tokenId : Nat) : List UInt8 :=
  encodeCall sigSafeTransferFrom [.address src, .address dst, .uint tokenId]
def erc721Approve (to tokenId : Nat) : List UInt8 :=
  encodeCall sigApprove [.address to, .uint tokenId]
def erc721SetApprovalForAll (operator : Nat) (approved : Bool) : List UInt8 :=
  encodeCall sigSetApprovalForAll [.address operator, .bool approved]
def erc721OwnerOf (tokenId : Nat) : List UInt8 :=
  encodeCall sigOwnerOf [.uint tokenId]

/-- ERC-721 `Transfer` has the same signature as ERC-20's but indexes the token id, so its
    logs have four topics and no data. -/
def evTransfer721 : EventSig :=
  { name := "Transfer"
    params := [⟨"from", .address, true⟩, ⟨"to", .address, true⟩, ⟨"tokenId", .uint 256, true⟩] }
def evApprovalForAll : EventSig :=
  { name := "ApprovalForAll"
    params := [⟨"owner", .address, true⟩, ⟨"operator", .address, true⟩, ⟨"approved", .bool, false⟩] }

/-! ## WETH9 -/

def sigDeposit : FunctionSig := ⟨"deposit", []⟩
def sigWithdraw : FunctionSig := ⟨"withdraw", [.uint 256]⟩

/-- Wrap: call with the ether to wrap as the transaction value. -/
def wethDeposit : List UInt8 := encodeCall sigDeposit []
def wethWithdraw (amount : Nat) : List UInt8 := encodeCall sigWithdraw [.uint amount]

def evDeposit : EventSig :=
  { name := "Deposit", params := [⟨"dst", .address, true⟩, ⟨"wad", .uint 256, false⟩] }
def evWithdrawal : EventSig :=
  { name := "Withdrawal", params := [⟨"src", .address, true⟩, ⟨"wad", .uint 256, false⟩] }

/-! ## Uniswap v3 SwapRouter02 -/

/-- `(tokenIn, tokenOut, fee, recipient, amountIn | amountOut, amountOutMinimum |
    amountInMaximum, sqrtPriceLimitX96)`. -/
def swapParams : AbiType :=
  .tuple [.address, .address, .uint 24, .address, .uint 256, .uint 256, .uint 160]

def sigExactInputSingle : FunctionSig := ⟨"exactInputSingle", [swapParams]⟩
def sigExactOutputSingle : FunctionSig := ⟨"exactOutputSingle", [swapParams]⟩
def sigMulticallDeadline : FunctionSig := ⟨"multicall", [.uint 256, .array .bytes]⟩
def sigUnwrapWETH9 : FunctionSig := ⟨"unwrapWETH9", [.uint 256, .address]⟩
def sigRefundETH : FunctionSig := ⟨"refundETH", []⟩

/-- Sell exactly `amountIn` of `tokenIn`; revert unless at least `amountOutMinimum` of
    `tokenOut` comes out. -/
structure ExactInputSingle where
  tokenIn : Nat
  tokenOut : Nat
  fee : Nat
  recipient : Nat
  amountIn : Nat
  amountOutMinimum : Nat
  sqrtPriceLimitX96 : Nat := 0

/-- Buy exactly `amountOut` of `tokenOut`; revert if it would cost more than
    `amountInMaximum` of `tokenIn`. -/
structure ExactOutputSingle where
  tokenIn : Nat
  tokenOut : Nat
  fee : Nat
  recipient : Nat
  amountOut : Nat
  amountInMaximum : Nat
  sqrtPriceLimitX96 : Nat := 0

def exactInputSingle (s : ExactInputSingle) : List UInt8 :=
  encodeCall sigExactInputSingle [.seq [.address s.tokenIn, .address s.tokenOut, .uint s.fee,
    .address s.recipient, .uint s.amountIn, .uint s.amountOutMinimum, .uint s.sqrtPriceLimitX96]]

def exactOutputSingle (s : ExactOutputSingle) : List UInt8 :=
  encodeCall sigExactOutputSingle [.seq [.address s.tokenIn, .address s.tokenOut, .uint s.fee,
    .address s.recipient, .uint s.amountOut, .uint s.amountInMaximum, .uint s.sqrtPriceLimitX96]]

def unwrapWETH9 (amountMinimum recipient : Nat) : List UInt8 :=
  encodeCall sigUnwrapWETH9 [.uint amountMinimum, .address recipient]

def refundETH : List UInt8 := encodeCall sigRefundETH []

/-- Wrap router calls so that the whole transaction reverts after `deadline` (Unix seconds). -/
def swapWithDeadline (deadline : Nat) (calls : List (List UInt8)) : List UInt8 :=
  encodeCall sigMulticallDeadline [.uint deadline, .seq (calls.map .bytes)]

/-! ## Slippage -/

/-- Least output to accept, given a quoted output and a tolerance in basis points
    (1 bp = 0.01%), rounded down. A tolerance over 10000 bp is treated as 10000. -/
def minOutForSlippage (quoteOut bps : Nat) : Nat :=
  quoteOut * (10000 - bps) / 10000

/-- Most input to pay, given a quoted input and a tolerance in basis points, rounded up. -/
def maxInForSlippage (quoteIn bps : Nat) : Nat :=
  (quoteIn * (10000 + bps) + 9999) / 10000

/-- Kind: bound. Says: the least accepted output never exceeds the quote.
    Does not say: that the quote was accurate. -/
theorem minOutForSlippage_le (quoteOut bps : Nat) : minOutForSlippage quoteOut bps ≤ quoteOut := by
  simp only [minOutForSlippage]
  have h : quoteOut * (10000 - bps) ≤ quoteOut * 10000 := Nat.mul_le_mul_left _ (by omega)
  exact Nat.div_le_of_le_mul (by omega)

/-- Kind: bound. Says: the loss allowed below the quote is at most the tolerance: with
    `bps ≤ 10000`, `quoteOut * (10000 - bps) < (minOut + 1) * 10000`.
    Does not say: anything about price movement before the quote. -/
theorem minOutForSlippage_tight (quoteOut bps : Nat) :
    quoteOut * (10000 - bps) < (minOutForSlippage quoteOut bps + 1) * 10000 := by
  simp only [minOutForSlippage]
  generalize quoteOut * (10000 - bps) = x
  omega

/-- Kind: bound. Says: the most input allowed is at least the quote.
    Does not say: that the quote was accurate. -/
theorem le_maxInForSlippage (quoteIn bps : Nat) : quoteIn ≤ maxInForSlippage quoteIn bps := by
  simp only [maxInForSlippage]
  have h : quoteIn * 10000 ≤ quoteIn * (10000 + bps) := Nat.mul_le_mul_left _ (by omega)
  generalize quoteIn * (10000 + bps) = x at h
  omega

end EthereumWallet.Calls
