# Wallet: what is shown before signing, and the cases that mislead people

2026-11-27. Implemented in `formal/lean4/ethereum-wallet` (`EthereumWallet/Abi`,
`EthereumWallet/Eip712`, `EthereumWallet/Calls`). Acceptance epic:
[issue 725](https://github.com/danbri/factoidal-core/issues/725). Nothing in
this code sends anything to a network.

## Rule

Everything a person is shown before signing (function, arguments, token
amounts, spender, typed-data fields) is produced by the Lean decoders, from
the same bytes that will be signed. There is no second reading of calldata or
JSON for display.

- **Calldata.** `Calls.describeCall` shows a decoded action only when the
  strict decoder accepts the calldata. `Abi.decodeArgsAt_sound` proves that
  accepted bytes are exactly the selector followed by the canonical encoding
  of the values shown: no trailing bytes, no gaps, no shared or reordered
  tails, no bits outside a value's width. Anything else with a known selector
  is `Action.malformed` with `Warning.malformedCalldata`; an unknown selector
  is `Action.unknown` with `Warning.unknownFunction`. Lenient decoders accept
  several byte strings for one value, which lets a page and a contract
  disagree about what the bytes mean; this one accepts one.
- **Typed data.** `Eip712.encodeField` computes each field's hash and its
  `Shown` entry in one walk, so the tree that is displayed has exactly the
  fields that went into the digest. A member of the JSON that no declared
  field covers is refused, as is a repeated key, a number that another JSON
  reader would round, and a type name that is not canonical.

## Cases and their flags

| Case | Why it misleads | Flag |
| --- | --- | --- |
| Unlimited ERC-20 approval | `approve(spender, 2^256 - 1)` looks like one harmless step of a swap; the spender can take the whole balance at any later time | `Warning.unlimitedApproval` (theorem `describeArgs_unlimited`) |
| Approval that is unlimited in effect | An allowance of `2^128` or more is past any balance, but is not the one value people know to look for | `Warning.veryLargeApproval` |
| Approval to an unknown spender | The call is an ordinary `approve` or `setApprovalForAll`; what matters is who is approved | `Warning.unknownSpender` from `describeTx` when the spender or operator is not a contract pinned for the chain; `SignWarning.unknownSpender` for permits |
| A known function on the wrong contract | `deposit()`, `exactInputSingle(...)` or `multicall(...)` on an address that only imitates WETH9 or the router | `Warning.unverifiedTarget` from `describeTx` when the target is not the pinned deployment on that chain |
| `approve` and `transferFrom` on an unknown token | ERC-20 and ERC-721 share the selectors; the number is an amount in one and a token id in the other | `Warning.amountOrTokenId` unless the wallet knows the token's kind |
| `setApprovalForAll(operator, true)` | One call hands over every token of a collection, present and future; it carries no amount to look at | `Warning.approvalForAll` (theorem `describeArgs_approvalForAll`); revoking is not flagged |
| EIP-2612 `Permit` and DAI-style permit | An off-chain signature that costs no gas and looks like a login, but is an approval anyone can submit | `SignWarning.approvalBySignature`, plus `unlimitedAmount` and `noExpiry` when the value or deadline is the largest possible |
| Permit2 `PermitSingle`, batch and signature-transfer messages | One signature can cover any token already approved to Permit2; the token is inside the message, not the verifying contract | `SignAction.permit2Single` or `permit2Other` with `approvalBySignature`; `notCanonicalPermit2` when the verifying contract is not the Permit2 deployment (a look-alike domain); `unlimitedAmount` for `2^160 - 1`; `noExpiry` for `2^48 - 1` |
| Typed data on another chain, or bound to none | A signature made while viewing one chain is valid on another | `SignWarning.chainMismatch`, `noChainBinding`, `noVerifyingContract` |
| Typed data with no specific reading | Marketplace orders and similar messages authorise transfers | `SignWarning.unrecognisedTypedData`; all fields are still shown from `Shown` |
| `personal_sign` of 32 opaque bytes | It can be the hash of a transaction or of typed data, signed blind | `SignWarning.opaqueHash`, `notText` |
| Text with direction overrides or zero-width characters | The text reads differently from its bytes | `SignWarning.hiddenCharacters` |
| EIP-7702 authorization | It is not a transaction and has no amount, but it makes the account run the delegate's code, which can move everything the account holds | `AuthWarning.fullAccountControl` on every delegation (theorem `describeAuthorization_warns`); `validOnAllChains` for chain id 0; `chainMismatch`; `unknownDelegate` unless the delegate is on the wallet's list; a zero delegate is shown as clearing the delegation |
| Swap with no price protection | `amountOutMinimum = 0` (or `amountInMaximum = 2^256 - 1`) accepts any price, which is what sandwiching needs | `Warning.noSlippageProtection` (theorem `describeArgs_noSlippage`) |
| Swap output sent elsewhere | The recipient field is a third party | `Warning.recipientNotSender` (the router's own "caller" and "router" markers are not flagged) |
| Swap with no deadline | SwapRouter02 swap structs have no deadline; without the `multicall(deadline, ...)` wrapper a held transaction can execute much later | `Warning.noDeadline` |
| Tokens sent to the token contract or the zero address | A common way to lose tokens | `Warning.suspectRecipient` |
| Ether attached to undecoded calldata, or to a call that takes none | The value is easy to overlook next to the call | `Warning.valueWithUnknownCall`, `Warning.unexpectedValue` |
| Multicall hiding an inner call | Only the outer function is recognised | inner calls are decoded one level down; any that is not is `Warning.innerCallNotDecoded` |

`describeCall` needs no chain; `describeTx` adds the warnings that depend on
which contracts are pinned for a chain and keeps all the others
(`describeTx_keeps`). A confirmation screen should use `describeTx`.

## Bounds on untrusted input

| Input | Bound | At the bound |
| --- | --- | --- |
| ABI data, any read | within the array (`readWord`) | `Err.outOfBounds` (`readWord_out_of_bounds`) |
| Array count | `count * headSize ≤ bytes left`, tested before the element decoders are built | `Err.lengthOutOfBounds` (`decodeAt_array_count_refused`, `decodeAt_array_length_le`) |
| Dynamic offset | must equal the end of the previous tail | `Err.badOffset` (`runFields_bad_offset`) |
| ABI type widths | at most 256 bits, at most 32 bytes | `Err.badType`, before the width is used as a size |
| ABI type nesting | `maxTypeDepth` = 32; no zero-size element type | `Err.badType` (`decodeArgsAt_bad_type`, `parseType_ok`) |
| Type string | `maxSigChars` = 2048 | `Err.badType` (`parseType_too_long`) |
| Typed-data JSON | 1 MiB, nesting 64, 256 members per object, no repeated key | `jsonTooLong` (`parseJson_too_long`), `jsonTooDeep`, `tooManyMembers`, `duplicateKey` |
| Typed-data nesting | `maxDataDepth` = 32 (struct types may be recursive; the data may not be deep) | `dataTooDeep` (`encodeField_depth_refused`) |
| Log topics | at most 4, each 32 bytes | `Err.badTopics` (`decodeEvent_too_many_topics`) |

The size of a decoded value is bounded by the input: by `decodeArgsAt_sound`
its canonical encoding is exactly the input bytes.

## Decisions, and what is open

- Strict decoding re-encodes the decoded value and compares it with the
  input. That adds a second pass to a decode and is what makes the
  canonical-form theorem a short proof. The second pass uses a byte-array
  encoder that is proved equal to the list specification (`encBA_eq`).
  Proving that the single pass alone accepts only canonical input would let
  the comparison go.
- Decoded `bytes` and `string` values are lists of bytes, and single words
  are still written through the list form; both are places to gain speed
  later, each with an equality proof.
- Refusing extra typed-data members is stricter than common wallets, which
  drop them silently. If real sites need it, the alternative is to ignore
  and flag them; they never reach the digest either way.
- `fixed`, `ufixed` and `function` ABI types are not accepted yet.
- Open risk, flagged: typed-data values and `personal_sign` messages are
  hashed by the pure Lean Keccak-256, whose timing depends on the data and
  whose digests are tested, not proved. Every function that does so takes the
  token `HashRisk.pureKeccakOnMessages`; only the test tool accepts it, under
  `--dangerously-enable-pure-keccak-on-messages`. A wallet entry point that
  signs real messages needs the owner's decision or a verified Keccak-256
  (register: `skills/lean-risk-flags/SKILL.md`).
- Proved: round trip, canonical form, injectivity of the encoding, the
  refusals above. Tested only: that the encoding is Solidity's (specification
  examples and differential runs against ethers and viem in CI), that the
  hash is Keccak-256, JSON grammar coverage, and that every accepted JSON
  document is within the depth bound.
- The chain of trust for display still needs the screen itself: these
  functions return data, and the confirmation UI must render every warning
  and every `Shown` field. That is later work with its own tests.
