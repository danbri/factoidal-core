import EthereumWallet.Calls.Known
import EthereumWallet.Eip712.TypedData

/-!
# "What this does": summaries for the confirmation screen

`describeCall` turns a transaction's target, value and calldata into an
`Action` and a list of `Warning`s. `describeTypedData` does the same for an
EIP-712 signing request, `describePersonalSign` for `personal_sign`, and
`describeAuthorization` for an EIP-7702 authorization.

Rules these functions keep:

* Every field shown comes from the strict decoders. Calldata with a known
  selector that is not the canonical encoding of its arguments is reported as
  `Action.malformed`, never as a decoded action.
* Nothing is hidden for being unrecognised: unknown calldata is
  `Action.unknown` with `Warning.unknownFunction`.
* The cases that commonly mislead people each raise a named warning; see
  `docs/designissues/2026-11-27-wallet-misleading-signing-cases.md`.
-/

namespace EthereumWallet.Calls

open EthereumWallet.Abi EthereumWallet.Eip712

/-- What kind of token the target is, when the wallet knows. `approve` and `transferFrom` have
    the same selector for ERC-20 and ERC-721, and the number means an amount in one and a token
    id in the other. -/
inductive TokenKind where
  | erc20
  | erc721
  | unknown
  deriving Repr, DecidableEq

inductive Warning where
  /-- An ERC-20 allowance of `2^256 - 1`: the spender can take the whole balance, now and later. -/
  | unlimitedApproval
  /-- `setApprovalForAll(operator, true)`: the operator can move every token of the collection. -/
  | approvalForAll
  /-- An ERC-20 allowance of `2^128` or more: beyond any balance, so unlimited in effect. -/
  | veryLargeApproval
  /-- The spender or operator being approved is not a contract this wallet has pinned for the
      chain. Approvals to unknown spenders are how most token thefts start. -/
  | unknownSpender
  /-- A function of a known protocol (WETH9, SwapRouter02) called on an address that is not
      that protocol's pinned deployment on the chain. -/
  | unverifiedTarget
  /-- The token kind is not known, so the number may be an amount or a token id. -/
  | amountOrTokenId
  /-- A swap with no minimum output (or no maximum input): any price is accepted. -/
  | noSlippageProtection
  /-- A swap whose output goes to an address other than the sender. -/
  | recipientNotSender
  /-- A swap that is not wrapped in a deadline. -/
  | noDeadline
  /-- Ether is sent along with calldata that could not be decoded. -/
  | valueWithUnknownCall
  /-- The selector is not one this wallet knows. -/
  | unknownFunction
  /-- A known selector, but the calldata is not the canonical encoding of its arguments. -/
  | malformedCalldata
  /-- Tokens are being sent to the token contract itself, or to the zero address. -/
  | suspectRecipient
  /-- A call inside a multicall that was not decoded. -/
  | innerCallNotDecoded
  /-- Ether sent to a function that does not take it. -/
  | unexpectedValue
  deriving Repr, DecidableEq

inductive Action where
  | nativeTransfer (to value : Nat)
  | erc20Transfer (token to amount : Nat)
  /-- `approve(spender, n)`: an ERC-20 allowance of `n`, or ERC-721 approval of token `n`. -/
  | approve (token spender amountOrTokenId : Nat)
  | transferFrom (token src dst amountOrTokenId : Nat)
  | safeTransferFrom (token src dst tokenId : Nat)
  | setApprovalForAll (token operator : Nat) (approved : Bool)
  | wethDeposit (weth amount : Nat)
  | wethWithdraw (weth amount : Nat)
  | swapExactInput (router : Nat) (p : ExactInputSingle)
  | swapExactOutput (router : Nat) (p : ExactOutputSingle)
  | unwrapWETH9 (amountMinimum recipient : Nat)
  | refundETH
  /-- `multicall(deadline, calls)` on the router. -/
  | multicall (deadline : Nat) (calls : List Action)
  | malformed (function : String)
  | unknown (selector : List UInt8)

structure CallSummary where
  action : Action
  warnings : List Warning

/-- `SwapRouter02` reads these two recipient values as "the caller" and "the router itself". -/
def routerMsgSender : Nat := 1
def routerAddressThis : Nat := 2

structure Known where
  tag : String
  sig : FunctionSig
  selector : List UInt8

def mkKnown (tag : String) (sig : FunctionSig) : Known := ⟨tag, sig, sig.selector⟩

/-- Functions `describeCall` recognises. The selectors are computed once. -/
def knownFunctions : List Known := [
  mkKnown "transfer" sigTransfer,
  mkKnown "approve" sigApprove,
  mkKnown "transferFrom" sigTransferFrom,
  mkKnown "safeTransferFrom" sigSafeTransferFrom,
  mkKnown "safeTransferFromData" sigSafeTransferFromData,
  mkKnown "setApprovalForAll" sigSetApprovalForAll,
  mkKnown "deposit" sigDeposit,
  mkKnown "withdraw" sigWithdraw,
  mkKnown "exactInputSingle" sigExactInputSingle,
  mkKnown "exactOutputSingle" sigExactOutputSingle,
  mkKnown "unwrapWETH9" sigUnwrapWETH9,
  mkKnown "refundETH" sigRefundETH,
  mkKnown "multicall" sigMulticallDeadline
]

def when (c : Bool) (w : Warning) : List Warning := if c then [w] else []

def suspect (token to : Nat) : Bool := to == token || to == 0

/-- A decoded known call other than `multicall`. `inMulticall` says a deadline wrapper is present. -/
def describeArgs (sender to value : Nat) (kind : TokenKind) (inMulticall : Bool) (tag : String)
    (args : List AbiValue) : CallSummary :=
  let noValue := when (value != 0) .unexpectedValue
  match tag, args with
  | "transfer", [.address dst, .uint amount] =>
    ⟨.erc20Transfer to dst amount, when (suspect to dst) .suspectRecipient ++ noValue⟩
  | "approve", [.address spender, .uint n] =>
    ⟨.approve to spender n,
      when (kind != .erc721 && n == maxUint256) .unlimitedApproval
        ++ when (kind != .erc721 && n != maxUint256 && n ≥ 2 ^ 128) .veryLargeApproval
        ++ when (kind == .unknown) .amountOrTokenId ++ noValue⟩
  | "transferFrom", [.address src, .address dst, .uint n] =>
    ⟨.transferFrom to src dst n,
      when (kind == .unknown) .amountOrTokenId ++ when (suspect to dst) .suspectRecipient
        ++ noValue⟩
  | "safeTransferFrom", [.address src, .address dst, .uint tokenId] =>
    ⟨.safeTransferFrom to src dst tokenId, when (suspect to dst) .suspectRecipient ++ noValue⟩
  | "safeTransferFromData", [.address src, .address dst, .uint tokenId, .bytes _] =>
    ⟨.safeTransferFrom to src dst tokenId, when (suspect to dst) .suspectRecipient ++ noValue⟩
  | "setApprovalForAll", [.address operator, .bool approved] =>
    ⟨.setApprovalForAll to operator approved, when approved .approvalForAll ++ noValue⟩
  | "deposit", [] => ⟨.wethDeposit to value, []⟩
  | "withdraw", [.uint amount] => ⟨.wethWithdraw to amount, noValue⟩
  | "exactInputSingle", [.seq [.address tokenIn, .address tokenOut, .uint fee, .address recipient,
      .uint amountIn, .uint amountOutMinimum, .uint limit]] =>
    ⟨.swapExactInput to ⟨tokenIn, tokenOut, fee, recipient, amountIn, amountOutMinimum, limit⟩,
      when (amountOutMinimum == 0) .noSlippageProtection
        ++ when (recipient != sender && recipient != routerMsgSender
              && recipient != routerAddressThis) .recipientNotSender
        ++ when (!inMulticall) .noDeadline⟩
  | "exactOutputSingle", [.seq [.address tokenIn, .address tokenOut, .uint fee,
      .address recipient, .uint amountOut, .uint amountInMaximum, .uint limit]] =>
    ⟨.swapExactOutput to ⟨tokenIn, tokenOut, fee, recipient, amountOut, amountInMaximum, limit⟩,
      when (amountInMaximum == maxUint256) .noSlippageProtection
        ++ when (recipient != sender && recipient != routerMsgSender
              && recipient != routerAddressThis) .recipientNotSender
        ++ when (!inMulticall) .noDeadline⟩
  | "unwrapWETH9", [.uint amountMinimum, .address recipient] =>
    ⟨.unwrapWETH9 amountMinimum recipient,
      when (amountMinimum == 0) .noSlippageProtection
        ++ when (recipient != sender && recipient != routerMsgSender) .recipientNotSender⟩
  | "refundETH", [] => ⟨.refundETH, []⟩
  | _, _ => ⟨.malformed tag, [.malformedCalldata]⟩

def findKnown (data : ByteArray) : Option Known :=
  knownFunctions.find? fun k => windowB data 0 k.selector

/-- One call that is not a multicall. -/
def describeLeaf (sender to value : Nat) (kind : TokenKind) (inMulticall : Bool)
    (data : ByteArray) : CallSummary :=
  if data.size == 0 then ⟨.nativeTransfer to value, []⟩
  else
    match findKnown data with
    | none =>
      ⟨.unknown (takeBytes data 0 (min 4 data.size)),
        .unknownFunction :: when (value != 0) .valueWithUnknownCall⟩
    | some k =>
      if k.tag == "multicall" then
        ⟨.unknown k.selector, [.innerCallNotDecoded]⟩
      else
        match decodeArgsAt k.sig.inputs data 4 with
        | .error _ => ⟨.malformed k.tag, [.malformedCalldata]⟩
        | .ok args => describeArgs sender to value kind inMulticall k.tag args

/-- The calls inside a multicall, when every element is a byte string. A loop, not a
    recursion: the number of elements comes from the calldata. -/
def innerBytes (inner : List AbiValue) : Option (List (List UInt8)) :=
  inner.mapM fun v =>
    match v with
    | .bytes b => some b
    | _ => none

/-- What a transaction from `sender` to `to` with `value` wei and calldata `data` does.
    `kind` is what the wallet knows about `to` as a token. -/
def describeCall (sender to value : Nat) (kind : TokenKind) (data : ByteArray) : CallSummary :=
  match findKnown data with
  | some k =>
    if k.tag == "multicall" && data.size != 0 then
      match decodeArgsAt k.sig.inputs data 4 with
      | .ok [.uint deadline, .seq inner] =>
        match innerBytes inner with
        | some calls =>
          let subs := calls.map fun c => describeLeaf sender to 0 kind true (toBytes c)
          ⟨.multicall deadline (subs.map (·.action)), subs.flatMap (·.warnings)⟩
        | none => ⟨.malformed k.tag, [.malformedCalldata]⟩
      | _ => ⟨.malformed k.tag, [.malformedCalldata]⟩
    else describeLeaf sender to value kind false data
  | none => describeLeaf sender to value kind false data

/-- Contracts pinned for a chain, by address. -/
def pinnedName? (chainId addr : Nat) : Option String :=
  (pinned.find? fun p => p.chainId == chainId && addrOfHex p.address == addr).map (·.name)

def isPinned (chainId : Nat) (name : String) (addr : Nat) : Bool :=
  pinnedAddress? name chainId == some addr

/-- Warnings that need the chain: a protocol function on an address that is not the pinned
    deployment, and an approval to a spender that is not pinned. -/
def chainWarnings (chainId to : Nat) : Action → List Warning
  | .approve _ spender _ => when (pinnedName? chainId spender).isNone .unknownSpender
  | .setApprovalForAll _ operator approved =>
    when (approved && (pinnedName? chainId operator).isNone) .unknownSpender
  | .wethDeposit _ _ => when (!isPinned chainId "WETH9" to) .unverifiedTarget
  | .wethWithdraw _ _ => when (!isPinned chainId "WETH9" to) .unverifiedTarget
  | .swapExactInput _ _ => when (!isPinned chainId "UniswapV3SwapRouter02" to) .unverifiedTarget
  | .swapExactOutput _ _ => when (!isPinned chainId "UniswapV3SwapRouter02" to) .unverifiedTarget
  | .unwrapWETH9 _ _ => when (!isPinned chainId "UniswapV3SwapRouter02" to) .unverifiedTarget
  | .refundETH => when (!isPinned chainId "UniswapV3SwapRouter02" to) .unverifiedTarget
  | .multicall _ _ => when (!isPinned chainId "UniswapV3SwapRouter02" to) .unverifiedTarget
  | _ => []

/-- `describeCall` for a transaction on a known chain: the same action, with the warnings that
    depend on which contracts are pinned for that chain. -/
def describeTx (chainId sender to value : Nat) (kind : TokenKind) (data : ByteArray) :
    CallSummary :=
  let s := describeCall sender to value kind data
  ⟨s.action, s.warnings ++ chainWarnings chainId to s.action⟩

/-- Kind: display rule. Says: `describeTx` shows the same action as `describeCall` and keeps
    every one of its warnings.
    Does not say: that a pinned contract is safe to approve. -/
theorem describeTx_keeps (chainId sender to value : Nat) (kind : TokenKind) (data : ByteArray) :
    (describeTx chainId sender to value kind data).action
        = (describeCall sender to value kind data).action
      ∧ ∀ w, w ∈ (describeCall sender to value kind data).warnings →
          w ∈ (describeTx chainId sender to value kind data).warnings := by
  refine ⟨rfl, fun w hw => ?_⟩
  simp only [describeTx, List.mem_append]
  exact Or.inl hw

/-! ## Signing requests -/

inductive SignWarning where
  /-- The signature is an approval: whoever holds it can spend the tokens, with no transaction
      from the signer. -/
  | approvalBySignature
  /-- The approved amount is the largest the type allows. -/
  | unlimitedAmount
  /-- The approval never expires (the deadline or expiration is the largest value). -/
  | noExpiry
  /-- A Permit2 message whose verifying contract is not the Permit2 deployment. -/
  | notCanonicalPermit2
  /-- The spender is not a contract this wallet has pinned for the chain. -/
  | unknownSpender
  /-- The domain names a chain other than the active one. -/
  | chainMismatch
  /-- The domain names no chain: the signature is not bound to one. -/
  | noChainBinding
  /-- The domain names no verifying contract. -/
  | noVerifyingContract
  /-- Typed data this wallet has no specific reading for. It may still authorise transfers
      (marketplace orders do). -/
  | unrecognisedTypedData
  /-- A 32-byte message that is not text: it may be the hash of anything. -/
  | opaqueHash
  /-- The message is not valid UTF-8 text and is shown as hex. -/
  | notText
  /-- The text has control or direction-override characters that can change how it reads. -/
  | hiddenCharacters
  deriving Repr, DecidableEq

inductive SignAction where
  /-- EIP-2612 `Permit(owner, spender, value, nonce, deadline)`; the token is the verifying
      contract. -/
  | permit (token owner spender value nonce deadline : Nat)
  /-- The DAI-style `Permit(holder, spender, nonce, expiry, allowed)`: all or nothing. -/
  | permitAllowed (token holder spender nonce expiry : Nat) (allowed : Bool)
  /-- Permit2 `PermitSingle`. -/
  | permit2Single (token amount expiration nonce spender sigDeadline : Nat)
  /-- Another Permit2 message (batch or signature transfer). -/
  | permit2Other (primaryType : String)
  | other (primaryType : String)

structure SignSummary where
  action : SignAction
  warnings : List SignWarning
  chainId : Option Nat
  verifyingContract : Option Nat

def signWhen (c : Bool) (w : SignWarning) : List SignWarning := if c then [w] else []

def classifyTypedData (r : SignRequest) : SignAction × List SignWarning :=
  let token := r.verifyingContract?.getD 0
  let m := r.message
  if r.primaryType == "Permit" then
    match m.addr? "owner", m.addr? "spender", m.uint? "value", m.uint? "nonce",
        m.uint? "deadline" with
    | some owner, some spender, some value, some nonce, some deadline =>
      (.permit token owner spender value nonce deadline,
        .approvalBySignature :: signWhen (value == maxUint256) .unlimitedAmount
          ++ signWhen (deadline == maxUint256) .noExpiry)
    | _, _, _, _, _ =>
      match m.addr? "holder", m.addr? "spender", m.uint? "nonce", m.uint? "expiry",
          m.bool? "allowed" with
      | some holder, some spender, some nonce, some expiry, some allowed =>
        (.permitAllowed token holder spender nonce expiry allowed,
          .approvalBySignature :: signWhen allowed .unlimitedAmount
            ++ signWhen (allowed && expiry == 0) .noExpiry)
      | _, _, _, _, _ => (.other r.primaryType, [.unrecognisedTypedData])
  else if r.primaryType == "PermitSingle" then
    match m.field? "details", m.addr? "spender", m.uint? "sigDeadline" with
    | some d, some spender, some sigDeadline =>
      match d.addr? "token", d.uint? "amount", d.uint? "expiration", d.uint? "nonce" with
      | some tok, some amount, some expiration, some nonce =>
        (.permit2Single tok amount expiration nonce spender sigDeadline,
          .approvalBySignature :: signWhen (amount == maxUint160) .unlimitedAmount
            ++ signWhen (expiration == maxUint48) .noExpiry
            ++ signWhen (token != permit2Address) .notCanonicalPermit2)
      | _, _, _, _ => (.other r.primaryType, [.unrecognisedTypedData])
    | _, _, _ => (.other r.primaryType, [.unrecognisedTypedData])
  else if r.primaryType == "PermitBatch" || r.primaryType == "PermitTransferFrom"
      || r.primaryType == "PermitBatchTransferFrom"
      || r.primaryType == "PermitWitnessTransferFrom"
      || r.primaryType == "PermitBatchWitnessTransferFrom" then
    (.permit2Other r.primaryType,
      .approvalBySignature :: signWhen (token != permit2Address) .notCanonicalPermit2)
  else (.other r.primaryType, [.unrecognisedTypedData])

/-- What signing this typed-data request does. `activeChainId` is the wallet's current chain. -/
def describeTypedData (activeChainId : Nat) (r : SignRequest) : SignSummary :=
  let c := classifyTypedData r
  let spender? : Option Nat :=
    match c.1 with
    | .permit _ _ spender _ _ _ => some spender
    | .permitAllowed _ _ spender _ _ _ => some spender
    | .permit2Single _ _ _ _ spender _ => some spender
    | _ => none
  let spenderWarn : List SignWarning :=
    match spender? with
    | some spender => signWhen (pinnedName? activeChainId spender).isNone .unknownSpender
    | none => []
  let chainWarn : List SignWarning :=
    match r.chainId? with
    | some id => signWhen (id != activeChainId) .chainMismatch
    | none => [.noChainBinding]
  { action := c.1
    warnings := c.2 ++ spenderWarn ++ chainWarn
      ++ signWhen r.verifyingContract?.isNone .noVerifyingContract
    chainId := r.chainId?
    verifyingContract := r.verifyingContract? }

/-- Characters that can hide or reorder text: C0/C1 controls other than tab, line feed and
    carriage return, zero-width characters and the Unicode direction controls. -/
def isHiddenChar (c : Char) : Bool :=
  let n := c.toNat
  (n < 0x20 && n != 9 && n != 10 && n != 13) || (0x7f ≤ n && n < 0xa0)
    || (0x200b ≤ n && n ≤ 0x200f) || (0x202a ≤ n && n ≤ 0x202e) || (0x2066 ≤ n && n ≤ 0x2069)
    || n == 0xfeff

structure PersonalSummary where
  /-- The message as text, when it is valid UTF-8. -/
  text : Option String
  hex : String
  digest : List UInt8
  warnings : List SignWarning

/-- What a `personal_sign` request shows. -/
def describePersonalSign (risk : MessageHashing) (msg : List UInt8) : PersonalSummary :=
  let text := String.fromUTF8? (toBytes msg)
  let hidden : Bool :=
    match text with
    | some s => s.toList.any isHiddenChar
    | none => false
  { text := text
    hex := "0x" ++ hexOf msg
    digest := personalSignDigest risk msg
    warnings := signWhen text.isNone .notText
      ++ signWhen (msg.length == 32 && (text.isNone || hidden)) .opaqueHash
      ++ signWhen hidden .hiddenCharacters }

/-! ## EIP-7702 authorizations -/

/-- The signed tuple of an EIP-7702 authorization: the account's code becomes a pointer to
    `address` until it is replaced. -/
structure Authorization where
  chainId : Nat
  address : Nat
  nonce : Nat

inductive AuthWarning where
  /-- Always raised: the delegate's code runs as the account and can move everything it holds. -/
  | fullAccountControl
  /-- Chain id 0: the authorization is valid on every chain. -/
  | validOnAllChains
  /-- The authorization names a chain other than the active one. -/
  | chainMismatch
  /-- The delegate is not on the wallet's list of known delegate contracts. -/
  | unknownDelegate
  deriving Repr, DecidableEq

inductive AuthAction where
  | delegate (to : Nat)
  /-- Delegating to the zero address clears the delegation. -/
  | clearDelegation
  deriving Repr, DecidableEq

structure AuthSummary where
  action : AuthAction
  warnings : List AuthWarning

def describeAuthorization (activeChainId : Nat) (knownDelegates : List Nat) (a : Authorization) :
    AuthSummary :=
  let chain : List AuthWarning :=
    if a.chainId == 0 then [.validOnAllChains]
    else if a.chainId != activeChainId then [.chainMismatch]
    else []
  if a.address == 0 then ⟨.clearDelegation, chain⟩
  else
    ⟨.delegate a.address,
      .fullAccountControl :: chain
        ++ (if knownDelegates.contains a.address then [] else [.unknownDelegate])⟩

/-- Kind: display rule. Says: every authorization that sets a delegate carries the
    full-account-control warning, whatever the chain or the delegate.
    Does not say: that a known delegate is safe. -/
theorem describeAuthorization_warns (activeChainId : Nat) (knownDelegates : List Nat)
    (a : Authorization) (h : a.address ≠ 0) :
    AuthWarning.fullAccountControl ∈ (describeAuthorization activeChainId knownDelegates a).warnings := by
  simp [describeAuthorization, h]

/-- The delegate an account's code points to, if the code is an EIP-7702 delegation
    designator (`0xef0100` then 20 bytes). -/
def delegationDesignator? (code : List UInt8) : Option Nat :=
  match code with
  | 0xef :: 0x01 :: 0x00 :: rest => if rest.length == 20 then some (natOfBytes rest) else none
  | _ => none

/-- Kind: display rule. Says: an `approve` of `2^256 - 1` on a target not known to be an ERC-721
    is flagged as an unlimited approval.
    Does not say: that smaller approvals are safe. -/
theorem describeArgs_unlimited (sender to value : Nat) (kind : TokenKind) (inMc : Bool)
    (spender : Nat) (hk : kind ≠ .erc721) :
    Warning.unlimitedApproval ∈
      (describeArgs sender to value kind inMc "approve" [.address spender, .uint maxUint256]).warnings := by
  cases kind <;> simp_all [describeArgs, when]

/-- Kind: display rule. Says: `setApprovalForAll(operator, true)` is always flagged.
    Does not say: anything about revoking (`false`), which is not flagged. -/
theorem describeArgs_approvalForAll (sender to value : Nat) (kind : TokenKind) (inMc : Bool)
    (operator : Nat) :
    Warning.approvalForAll ∈
      (describeArgs sender to value kind inMc "setApprovalForAll"
        [.address operator, .bool true]).warnings := by
  simp [describeArgs, when]

/-- Kind: display rule. Says: a swap with a zero minimum output is flagged.
    Does not say: that a nonzero minimum is a fair price. -/
theorem describeArgs_noSlippage (sender to value : Nat) (kind : TokenKind) (inMc : Bool)
    (tokenIn tokenOut fee recipient amountIn limit : Nat) :
    Warning.noSlippageProtection ∈
      (describeArgs sender to value kind inMc "exactInputSingle"
        [.seq [.address tokenIn, .address tokenOut, .uint fee, .address recipient,
          .uint amountIn, .uint 0, .uint limit]]).warnings := by
  simp [describeArgs, when]

/-! ## Permit2 `PermitSingle` typed data -/

structure PermitSingle where
  token : Nat
  amount : Nat
  expiration : Nat
  nonce : Nat
  spender : Nat
  sigDeadline : Nat

/-- The types of Permit2's `PermitSingle` message and its domain (which has a name, a chain id
    and a verifying contract, and no version). -/
def permit2Types : List TypeDef := [
  ⟨"EIP712Domain", [("name", "string"), ("chainId", "uint256"), ("verifyingContract", "address")]⟩,
  ⟨"PermitSingle", [("details", "PermitDetails"), ("spender", "address"),
    ("sigDeadline", "uint256")]⟩,
  ⟨"PermitDetails", [("token", "address"), ("amount", "uint160"), ("expiration", "uint48"),
    ("nonce", "uint48")]⟩
]

def jsonAddress (a : Nat) : Json := .str ("0x" ++ hexOf (beBytes 20 a))
def jsonNat (n : Nat) : Json := .str (toString n)

def permit2TypedData (chainId : Nat) (p : PermitSingle) : TypedData :=
  { types := permit2Types
    primaryType := "PermitSingle"
    domain := .obj [("name", .str "Permit2"), ("chainId", jsonNat chainId),
      ("verifyingContract", jsonAddress permit2Address)]
    message := .obj [
      ("details", .obj [("token", jsonAddress p.token), ("amount", jsonNat p.amount),
        ("expiration", jsonNat p.expiration), ("nonce", jsonNat p.nonce)]),
      ("spender", jsonAddress p.spender), ("sigDeadline", jsonNat p.sigDeadline)] }

/-- The signing request for a Permit2 `PermitSingle`, through the same typed-data path as any
    other request. -/
def permit2Request (risk : MessageHashing) (chainId : Nat) (p : PermitSingle) :
    Except Err712 SignRequest :=
  hashTypedData risk (permit2TypedData chainId p)

end EthereumWallet.Calls
