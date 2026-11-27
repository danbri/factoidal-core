import EthereumWallet.Calls.Summary
import EthereumWallet.Calls.Deploy

/-!
# Vectors and negative controls for the ABI, typed-data and call code

Run by the `wallet-abi-vectors` executable (compiled, so the hash runs at
native speed). Each check is a name and a boolean. Sources of the expected
values:

* Solidity "Contract ABI Specification": the `baz`, `bar`, `sam`, `f` and `g`
  examples (selectors and full encodings);
* EIP-712: the "Mail" example (type string, type hash, domain separator,
  struct hash and digest);
* EIP-55: the checksum test addresses; EIP-1014: the `CREATE2` examples;
* EIP-20, EIP-721, WETH9, SwapRouter02 and Permit2: published selectors,
  event topics, type hashes and the mainnet Permit2 domain separator;
* negative controls written for this suite: every refusal the decoders define.
-/

namespace EthereumWallet.AbiVectors

open EthereumWallet.Abi EthereumWallet.Eip712 EthereumWallet.Calls

def hx (s : String) : List UInt8 := (unhex s).getD []

def isErr {α : Type} (r : Except Err α) (e : Err) : Bool :=
  match r with
  | .error e' => e' == e
  | .ok _ => false

def isOk {ε α : Type} (r : Except ε α) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

def isErr712 {α : Type} (r : Except Err712 α) (e : Err712) : Bool :=
  match r with
  | .error e' => e' == e
  | .ok _ => false

def ty (s : String) : AbiType := (parseType s).toOption.getD .bool
def sig (s : String) : FunctionSig := (parseSignature s).toOption.getD ⟨"", []⟩
def sel (s : String) : String := hexOf (sig s).selector

/-- Encode, compare with the expected hex, and decode back to the same encoding. -/
def callIs (s : String) (args : List AbiValue) (expect : String) : Bool :=
  let f := sig s
  let enc := encodeCall f args
  checkL f.inputs args && hexOf enc == expect
    && (match decodeCall f (toBytes enc) with
        | .ok vs => encodeCall f vs == enc
        | .error _ => false)

def roundTrips (types : List String) (args : List AbiValue) : Bool :=
  let ts := types.map ty
  let enc := encodeArgs ts args
  checkL ts args
    && (match decodeArgs ts (toBytes enc) with
        | .ok vs => encodeArgs ts vs == enc && vs.length == args.length
        | .error _ => false)

def refuses (types : List String) (data : List UInt8) (e : Err) : Bool :=
  isErr (decodeArgs (types.map ty) (toBytes data)) e

def zeros (n : Nat) : List UInt8 := List.replicate n 0

def rep (n : Nat) (s : String) : String := String.join (List.replicate n s)

def specVectors : List (String × Bool) := [
  ("spec selector baz", sel "baz(uint32,bool)" == "cdcd77c0"),
  ("spec selector bar", sel "bar(bytes3[2])" == "fce353f6"),
  ("spec selector sam", sel "sam(bytes,bool,uint256[])" == "a5643bf2"),
  ("spec selector f", sel "f(uint256,uint32[],bytes10,bytes)" == "8be65246"),
  ("spec selector g", sel "g(uint256[][],string[])" == "2289b18c"),
  ("spec baz(69,true)", callIs "baz(uint32,bool)" [.uint 69, .bool true]
    ("cdcd77c0" ++ "0000000000000000000000000000000000000000000000000000000000000045"
      ++ "0000000000000000000000000000000000000000000000000000000000000001")),
  ("spec bar([abc,def])", callIs "bar(bytes3[2])" [.seq [.bytes (utf8 "abc"), .bytes (utf8 "def")]]
    ("fce353f6" ++ "6162630000000000000000000000000000000000000000000000000000000000"
      ++ "6465660000000000000000000000000000000000000000000000000000000000")),
  ("spec sam(dave,true,[1,2,3])", callIs "sam(bytes,bool,uint256[])"
    [.bytes (utf8 "dave"), .bool true, .seq [.uint 1, .uint 2, .uint 3]]
    ("a5643bf2" ++ "0000000000000000000000000000000000000000000000000000000000000060"
      ++ "0000000000000000000000000000000000000000000000000000000000000001"
      ++ "00000000000000000000000000000000000000000000000000000000000000a0"
      ++ "0000000000000000000000000000000000000000000000000000000000000004"
      ++ "6461766500000000000000000000000000000000000000000000000000000000"
      ++ "0000000000000000000000000000000000000000000000000000000000000003"
      ++ "0000000000000000000000000000000000000000000000000000000000000001"
      ++ "0000000000000000000000000000000000000000000000000000000000000002"
      ++ "0000000000000000000000000000000000000000000000000000000000000003")),
  ("spec f(0x123,[0x456,0x789],1234567890,Hello, world!)",
    callIs "f(uint256,uint32[],bytes10,bytes)"
    [.uint 0x123, .seq [.uint 0x456, .uint 0x789], .bytes (utf8 "1234567890"),
      .bytes (utf8 "Hello, world!")]
    ("8be65246" ++ "0000000000000000000000000000000000000000000000000000000000000123"
      ++ "0000000000000000000000000000000000000000000000000000000000000080"
      ++ "3132333435363738393000000000000000000000000000000000000000000000"
      ++ "00000000000000000000000000000000000000000000000000000000000000e0"
      ++ "0000000000000000000000000000000000000000000000000000000000000002"
      ++ "0000000000000000000000000000000000000000000000000000000000000456"
      ++ "0000000000000000000000000000000000000000000000000000000000000789"
      ++ "000000000000000000000000000000000000000000000000000000000000000d"
      ++ "48656c6c6f2c20776f726c642100000000000000000000000000000000000000")),
  ("spec g([[1,2],[3]],[one,two,three])", callIs "g(uint256[][],string[])"
    [.seq [.seq [.uint 1, .uint 2], .seq [.uint 3]],
      .seq [.bytes (utf8 "one"), .bytes (utf8 "two"), .bytes (utf8 "three")]]
    ("2289b18c" ++ "0000000000000000000000000000000000000000000000000000000000000040"
      ++ "0000000000000000000000000000000000000000000000000000000000000140"
      ++ "0000000000000000000000000000000000000000000000000000000000000002"
      ++ "0000000000000000000000000000000000000000000000000000000000000040"
      ++ "00000000000000000000000000000000000000000000000000000000000000a0"
      ++ "0000000000000000000000000000000000000000000000000000000000000002"
      ++ "0000000000000000000000000000000000000000000000000000000000000001"
      ++ "0000000000000000000000000000000000000000000000000000000000000002"
      ++ "0000000000000000000000000000000000000000000000000000000000000001"
      ++ "0000000000000000000000000000000000000000000000000000000000000003"
      ++ "0000000000000000000000000000000000000000000000000000000000000003"
      ++ "0000000000000000000000000000000000000000000000000000000000000060"
      ++ "00000000000000000000000000000000000000000000000000000000000000a0"
      ++ "00000000000000000000000000000000000000000000000000000000000000e0"
      ++ "0000000000000000000000000000000000000000000000000000000000000003"
      ++ "6f6e650000000000000000000000000000000000000000000000000000000000"
      ++ "0000000000000000000000000000000000000000000000000000000000000003"
      ++ "74776f0000000000000000000000000000000000000000000000000000000000"
      ++ "0000000000000000000000000000000000000000000000000000000000000005"
      ++ "7468726565000000000000000000000000000000000000000000000000000000"))
]

def selectorVectors : List (String × Bool) := [
  ("selector transfer", hexOf sigTransfer.selector == "a9059cbb"),
  ("selector approve", hexOf sigApprove.selector == "095ea7b3"),
  ("selector transferFrom", hexOf sigTransferFrom.selector == "23b872dd"),
  ("selector balanceOf", hexOf sigBalanceOf.selector == "70a08231"),
  ("selector allowance", hexOf sigAllowance.selector == "dd62ed3e"),
  ("selector safeTransferFrom/3", hexOf sigSafeTransferFrom.selector == "42842e0e"),
  ("selector safeTransferFrom/4", hexOf sigSafeTransferFromData.selector == "b88d4fde"),
  ("selector setApprovalForAll", hexOf sigSetApprovalForAll.selector == "a22cb465"),
  ("selector ownerOf", hexOf sigOwnerOf.selector == "6352211e"),
  ("selector getApproved", hexOf sigGetApproved.selector == "081812fc"),
  ("selector isApprovedForAll", hexOf sigIsApprovedForAll.selector == "e985e9c5"),
  ("selector deposit", hexOf sigDeposit.selector == "d0e30db0"),
  ("selector withdraw", hexOf sigWithdraw.selector == "2e1a7d4d"),
  ("selector exactInputSingle", hexOf sigExactInputSingle.selector == "04e45aaf"),
  ("selector exactOutputSingle", hexOf sigExactOutputSingle.selector == "5023b4df"),
  ("selector multicall(uint256,bytes[])", hexOf sigMulticallDeadline.selector == "5ae401dc"),
  ("selector unwrapWETH9", hexOf sigUnwrapWETH9.selector == "49404b7c"),
  ("selector refundETH", hexOf sigRefundETH.selector == "12210e8a"),
  ("canonical swap signature", sigExactInputSingle.canonical
    == "exactInputSingle((address,address,uint24,address,uint256,uint256,uint160))"),
  ("topic Transfer", hexOf evTransfer.topic0
    == "ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef"),
  ("topic Transfer (721) is the same", evTransfer721.topic0 == evTransfer.topic0),
  ("topic Approval", hexOf evApproval.topic0
    == "8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925"),
  ("topic ApprovalForAll", hexOf evApprovalForAll.topic0
    == "17307eab39ab6107e8899845ad3d59bd9653f200f220920489ca2b5937696c31"),
  ("topic Deposit", hexOf evDeposit.topic0
    == "e1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c"),
  ("topic Withdrawal", hexOf evWithdrawal.topic0
    == "7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65"),
  ("keccak empty", hexOf (keccak256 [])
    == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
]

def typeVectors : List (String × Bool) :=
  let printsBack (s : String) : Bool :=
    match parseType s with
    | .ok t => t.canonical == s
    | .error _ => false
  let bad (s : String) : Bool := !isOk (parseType s)
  [ ("type uint256", printsBack "uint256"),
    ("type int8", printsBack "int8"),
    ("type bytes32", printsBack "bytes32"),
    ("type nested", printsBack "(uint256,(bytes,int8)[2],string[])[]"),
    ("type uint is uint256", (parseType "uint").toOption.map (·.canonical) == some "uint256"),
    ("type int is int256", (parseType "int").toOption.map (·.canonical) == some "int256"),
    ("type depth 32 accepted", printsBack ("uint256" ++ rep 32 "[]")),
    ("type depth 33 refused", bad ("uint256" ++ rep 33 "[]")),
    ("type 40 nested tuples refused", bad (rep 40 "(" ++ "uint256" ++ rep 40 ")")),
    ("type string over the length limit refused",
      bad ("(" ++ rep 400 "uint256," ++ "uint256)")),
    ("type wide tuple accepted", isOk (parseType ("(" ++ rep 200 "uint256," ++ "uint256)"))),
    ("type uint7 refused", bad "uint7"),
    ("type uint264 refused", bad "uint264"),
    ("type uint08 refused", bad "uint08"),
    ("type bytes0 refused", bad "bytes0"),
    ("type bytes33 refused", bad "bytes33"),
    ("type T[0] refused", bad "uint256[0]"),
    ("type empty tuple refused", bad "()"),
    ("type nested empty tuple refused", bad "(uint256,())"),
    ("type fixed refused", bad "fixed128x18"),
    ("type function refused", bad "function"),
    ("type leading space refused", bad " uint256"),
    ("type trailing text refused", bad "uint256 "),
    ("type length with leading zero refused", bad "uint256[01]"),
    ("type length of 11 digits refused", bad "uint256[99999999999]"),
    ("type unbalanced refused", bad "(uint256"),
    ("signature with no arguments", isOk (parseSignature "deposit()")),
    ("signature with array suffix refused", !isOk (parseSignature "f(uint256)[]")),
    ("signature with no name refused", !isOk (parseSignature "(uint256)")) ]

def big : Nat := 2 ^ 255

def roundTripVectors : List (String × Bool) := [
  ("round trip no arguments", roundTrips [] []),
  ("round trip uint256 max", roundTrips ["uint256"] [.uint (2 ^ 256 - 1)]),
  ("round trip int256 min", roundTrips ["int256"] [.int (-(big : Int))]),
  ("round trip int8 -128", roundTrips ["int8"] [.int (-128)]),
  ("round trip int8 127", roundTrips ["int8"] [.int 127]),
  ("int8 128 is not well typed", !(ty "int8").check (.int 128)),
  ("uint8 256 is not well typed", !(ty "uint8").check (.uint 256)),
  ("round trip empty bytes", roundTrips ["bytes"] [.bytes []]),
  ("round trip 32 bytes", roundTrips ["bytes"] [.bytes (zeros 31 ++ [7])]),
  ("round trip 33 bytes", roundTrips ["bytes"] [.bytes (zeros 32 ++ [7])]),
  ("round trip empty array", roundTrips ["uint256[]"] [.seq []]),
  ("round trip static tuple array", roundTrips ["(uint8,address)[2]"]
    [.seq [.seq [.uint 1, .address 2], .seq [.uint 3, .address 4]]]),
  ("round trip dynamic fixed array", roundTrips ["string[2]", "uint256"]
    [.seq [.bytes (utf8 "a"), .bytes (utf8 "bb")], .uint 9]),
  ("round trip nested dynamic", roundTrips ["(uint256,(bytes,int8)[2])[]", "int256"]
    [.seq [.seq [.uint 7, .seq [.seq [.bytes [1, 2, 3], .int (-1)], .seq [.bytes [], .int 127]]]],
      .int (-5)]),
  ("round trip array of empty arrays", roundTrips ["uint256[][]"] [.seq [.seq [], .seq [], .seq []]]),
  ("int256 -5 encodes as two's complement",
    hexOf (encodeArgs [.int 256] [.int (-5)])
      == "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb")
]

/-- The single dynamic value `bytes "a"` with a correct layout, for mutation. -/
def oneByte : List UInt8 := word 0x20 ++ word 1 ++ (0x61 :: zeros 31)

def negativeControls : List (String × Bool) := [
  ("control: the unmutated input is accepted", isOk (decodeArgs [.bytes] (toBytes oneByte))),
  ("truncated word refused", refuses ["uint256"] (zeros 31) .outOfBounds),
  ("empty data for one argument refused", refuses ["uint256"] [] .outOfBounds),
  ("trailing byte refused", refuses ["uint256"] (word 1 ++ [0]) .trailingBytes),
  ("trailing word after a dynamic value refused",
    refuses ["bytes"] (oneByte ++ zeros 32) .trailingBytes),
  ("offset past the canonical place refused",
    refuses ["bytes"] (word 0x40 ++ word 0 ++ word 0) .badOffset),
  ("offset before the canonical place refused",
    refuses ["bytes"] (word 0 ++ word 0) .badOffset),
  ("offset of 2^255 refused", refuses ["bytes"] (word big ++ word 0) .badOffset),
  ("two offsets sharing one tail refused",
    refuses ["bytes", "bytes"] (word 0x40 ++ word 0x40 ++ word 1 ++ (0x61 :: zeros 31)) .badOffset),
  ("tails in the wrong order refused",
    refuses ["bytes", "bytes"]
      (word 0x80 ++ word 0x40 ++ word 1 ++ (0x61 :: zeros 31) ++ word 1 ++ (0x62 :: zeros 31))
      .badOffset),
  ("array count of 2^255 refused", refuses ["uint256[]"] (word 0x20 ++ word big) .lengthOutOfBounds),
  ("array count of 2^32 with no elements refused",
    refuses ["uint256[]"] (word 0x20 ++ word (2 ^ 32)) .lengthOutOfBounds),
  ("array count one more than the data holds refused",
    refuses ["uint256[]"] (word 0x20 ++ word 3 ++ word 1 ++ word 2) .lengthOutOfBounds),
  ("fixed array longer than the data refused, with no allocation for it",
    isErr (decodeArgsAt [.fixedArray (.uint 256) 4000000000] (toBytes (word 1)) 0)
      .lengthOutOfBounds),
  ("bytes length past the end refused",
    refuses ["bytes"] (word 0x20 ++ word 1000 ++ word 0) .lengthOutOfBounds),
  ("bytes length of 2^255 refused", refuses ["bytes"] (word 0x20 ++ word big) .lengthOutOfBounds),
  ("bytes content without its padding refused",
    refuses ["bytes"] (word 0x20 ++ word 1 ++ [0x61]) .outOfBounds),
  ("nonzero bytes padding refused",
    refuses ["bytes"] (word 0x20 ++ word 1 ++ (0x61 :: 0x01 :: zeros 30)) .dirtyPadding),
  ("uint8 with high bits refused", refuses ["uint8"] (word 256) .dirtyPadding),
  ("bool 2 refused", refuses ["bool"] (word 2) .dirtyPadding),
  ("address with high bits refused", refuses ["address"] (word (2 ^ 160)) .dirtyPadding),
  ("int8 128 without sign extension refused", refuses ["int8"] (word 128) .dirtyPadding),
  ("int8 below -128 refused", refuses ["int8"] (word (2 ^ 256 - 129)) .dirtyPadding),
  ("int8 -128 accepted", isOk (decodeArgs [.int 8] (toBytes (word (2 ^ 256 - 128))))),
  ("bytes4 with low bytes set refused", refuses ["bytes4"] (word 1) .dirtyPadding),
  ("nested arrays sharing one inner array refused (expansion attack)",
    refuses ["uint256[][]"]
      (word 0x20 ++ word 3 ++ word 0x60 ++ word 0x60 ++ word 0x60 ++ word 1 ++ word 7) .badOffset),
  ("inner offset pointing at the outer array refused (cycle)",
    refuses ["uint256[][]"] (word 0x20 ++ word 1 ++ word 0) .badOffset),
  ("width over 256 bits refused by the single pass, with no power computed",
    isErr ((AbiType.uint 1000000000000).decodeAt (toBytes (word 1)) 0) .badType),
  ("int width over 256 bits refused by the single pass",
    isErr ((AbiType.int 1000000000000).decodeAt (toBytes (word 1)) 0) .badType),
  ("bytes<M> over 32 refused by the single pass, with no allocation",
    isErr ((AbiType.fixedBytes 1000000000000).decodeAt (toBytes (word 1)) 0) .badType),
  ("a value of an over-wide type is not well typed",
    !(AbiType.uint 1000000000000).check (.uint 1)),
  ("types nested beyond the bound refused before reading",
    isErr (decodeArgsAt [(List.range 40).foldl (fun t _ => .array t) (.uint 256)] (toBytes []) 0)
      .badType),
  ("zero-size element type refused before reading",
    isErr (decodeArgsAt [.array (.tuple [])] (toBytes (word 0x20 ++ word (2 ^ 64))) 0) .badType),
  ("unknown selector refused",
    isErr (decodeCall sigTransfer (toBytes (hx "deadbeef" ++ word 1 ++ word 2))) .unknownSelector),
  ("calldata shorter than a selector refused",
    isErr (decodeCall sigTransfer (toBytes [0xa9, 0x05])) .unknownSelector),
  ("transfer with a trailing byte refused",
    isErr (decodeCall sigTransfer (toBytes (erc20Transfer 1 2 ++ [0]))) .trailingBytes),
  ("transfer with a dirty address refused",
    isErr (decodeCall sigTransfer
      (toBytes (sigTransfer.selector ++ word (2 ^ 200) ++ word 2))) .dirtyPadding)
]

def addr1 : Nat := 0x1111111111111111111111111111111111111111
def addr2 : Nat := 0x2222222222222222222222222222222222222222

def eventVectors : List (String × Bool) :=
  let t (a : Nat) : List UInt8 := word a
  let named (r : Except Err (List (String × EventArg))) (name : String) : Option AbiValue :=
    match r with
    | .ok args =>
      match args.lookup name with
      | some (.value v) => some v
      | _ => none
    | .error _ => none
  let erc20 := decodeEvent evTransfer [evTransfer.topic0, t addr1, t addr2] (toBytes (word 500))
  let erc721 := decodeEvent evTransfer721 [evTransfer.topic0, t addr1, t addr2, t 42] (toBytes [])
  let asNat (v : Option AbiValue) : Option Nat :=
    match v with
    | some (.uint n) => some n
    | some (.address n) => some n
    | _ => none
  [ ("event ERC-20 Transfer value", asNat (named erc20 "value") == some 500),
    ("event ERC-20 Transfer from", asNat (named erc20 "from") == some addr1),
    ("event ERC-20 Transfer to", asNat (named erc20 "to") == some addr2),
    ("event ERC-721 Transfer tokenId", asNat (named erc721 "tokenId") == some 42),
    ("event ERC-721 log refused as ERC-20 (topic count)",
      isErr (decodeEvent evTransfer [evTransfer.topic0, t addr1, t addr2, t 42] (toBytes []))
        .outOfBounds),
    ("event ERC-20 log refused as ERC-721 (topic count)",
      !isOk (decodeEvent evTransfer721 [evTransfer.topic0, t addr1, t addr2] (toBytes (word 500)))),
    ("event wrong topic0 refused",
      isErr (decodeEvent evApproval [evTransfer.topic0, t addr1, t addr2] (toBytes (word 5)))
        .unknownSelector),
    ("event dirty address topic refused",
      isErr (decodeEvent evTransfer [evTransfer.topic0, t (2 ^ 160), t addr2] (toBytes (word 5)))
        .dirtyPadding),
    ("event five topics refused",
      isErr (decodeEvent evTransfer721 [evTransfer.topic0, t 1, t 2, t 3, t 4] (toBytes []))
        .badTopics),
    ("event short topic refused",
      isErr (decodeEvent evTransfer [evTransfer.topic0, [1, 2, 3], t addr2] (toBytes (word 5)))
        .badTopics),
    ("event indexed string is a hash, not a value",
      (match decodeEvent { name := "Named", params := [⟨"label", .string, true⟩] }
          [(EventSig.topic0 { name := "Named", params := [⟨"label", .string, true⟩] }),
            keccak256 (utf8 "x")] (toBytes []) with
        | .ok [(_, .hashed h)] => h == keccak256 (utf8 "x")
        | _ => false)),
    ("ERC-20 return true", decodeErc20Return (toBytes (word 1)) == .succeeded),
    ("ERC-20 return false", decodeErc20Return (toBytes (word 0)) == .failed),
    ("ERC-20 return nothing", decodeErc20Return (toBytes []) == .noData),
    ("ERC-20 return 2 is malformed", decodeErc20Return (toBytes (word 2)) == .malformed),
    ("balanceOf return", (decodeUintReturn (toBytes (word 12345))).toOption == some 12345) ]

def mailJson : String :=
  "{\"types\":{\"EIP712Domain\":[{\"name\":\"name\",\"type\":\"string\"},{\"name\":\"version\",\"type\":\"string\"},{\"name\":\"chainId\",\"type\":\"uint256\"},{\"name\":\"verifyingContract\",\"type\":\"address\"}],\"Person\":[{\"name\":\"name\",\"type\":\"string\"},{\"name\":\"wallet\",\"type\":\"address\"}],\"Mail\":[{\"name\":\"from\",\"type\":\"Person\"},{\"name\":\"to\",\"type\":\"Person\"},{\"name\":\"contents\",\"type\":\"string\"}]},\"primaryType\":\"Mail\",\"domain\":{\"name\":\"Ether Mail\",\"version\":\"1\",\"chainId\":1,\"verifyingContract\":\"0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC\"},\"message\":{\"from\":{\"name\":\"Cow\",\"wallet\":\"0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826\"},\"to\":{\"name\":\"Bob\",\"wallet\":\"0xbBbBBBBbbBBBbbbBbbBbbbbBBbBbbbbBbBbbBBbB\"},\"contents\":\"Hello, Bob!\"}}"

/-- Typed data with one type `T` holding the given fields, a domain of only a chain id, and the
    given message text. -/
def smallTyped (fields message : String) : String :=
  "{\"types\":{\"EIP712Domain\":[{\"name\":\"chainId\",\"type\":\"uint256\"}],\"T\":[" ++ fields
    ++ "]},\"primaryType\":\"T\",\"domain\":{\"chainId\":1},\"message\":" ++ message ++ "}"

def fld (name type : String) : String :=
  "{\"name\":\"" ++ name ++ "\",\"type\":\"" ++ type ++ "\"}"

def mailTypes : List TypeDef := [
  ⟨"EIP712Domain", [("name", "string"), ("version", "string"), ("chainId", "uint256"),
    ("verifyingContract", "address")]⟩,
  ⟨"Person", [("name", "string"), ("wallet", "address")]⟩,
  ⟨"Mail", [("from", "Person"), ("to", "Person"), ("contents", "string")]⟩ ]

def typedDataVectors (risk : MessageHashing) : List (String × Bool) :=
  let mail := signRequestOfJson risk mailJson
  let field (r : Except Err712 SignRequest) (f : SignRequest → List UInt8) : String :=
    match r with
    | .ok x => hexOf (f x)
    | .error _ => "error"
  let refused (s : String) (e : Err712) : Bool := isErr712 (signRequestOfJson risk s) e
  let nest (n : Nat) : String := rep n "{\"next\":[" ++ "{\"next\":[]}" ++ rep n "]}"
  [ ("EIP-712 Mail encodeType",
      encodeType mailTypes ⟨"Mail", [("from", "Person"), ("to", "Person"), ("contents", "string")]⟩
        == some "Mail(Person from,Person to,string contents)Person(string name,address wallet)"),
    ("EIP-712 Mail typeHash",
      hexOf (keccak256 (utf8
        "Mail(Person from,Person to,string contents)Person(string name,address wallet)"))
        == "a0cedeb2dc280ba39b857546d74f5549c3a1d7bdc2dd96bf881f76108e23dac2"),
    ("EIP-712 Mail domain separator", field mail (·.domainSeparator)
      == "f2cee375fa42b42143804025fc449deafd50cc031ca257e0b194a650a912090f"),
    ("EIP-712 Mail hashStruct(message)", field mail (·.messageHash)
      == "c52c0ee5d84264471806290a3f2c4cecfc5490626bf912d01f240d7a274b371e"),
    ("EIP-712 Mail digest", field mail (·.digest)
      == "be609aee343fb3c4b28e1df9e632fca64fcfaede20f02e86244efddf30957bd2"),
    ("EIP-712 Mail chain id shown", (mail.toOption.bind (·.chainId?)) == some 1),
    ("EIP-712 Mail verifying contract shown",
      (mail.toOption.bind (·.verifyingContract?))
        == some 0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC),
    ("EIP-712 control: small document accepted",
      isOk (signRequestOfJson risk (smallTyped (fld "a" "uint8") "{\"a\":255}"))),
    ("EIP-712 number as decimal string and as hex string agree",
      field (signRequestOfJson risk (smallTyped (fld "a" "uint256") "{\"a\":\"255\"}")) (·.digest)
        == field (signRequestOfJson risk (smallTyped (fld "a" "uint256") "{\"a\":\"0xff\"}"))
            (·.digest)),
    ("EIP-712 uint8 256 refused",
      refused (smallTyped (fld "a" "uint8") "{\"a\":256}") (.badValue "a")),
    ("EIP-712 negative uint refused",
      refused (smallTyped (fld "a" "uint8") "{\"a\":-1}") (.badValue "a")),
    ("EIP-712 int8 -128 accepted",
      isOk (signRequestOfJson risk (smallTyped (fld "a" "int8") "{\"a\":-128}"))),
    ("EIP-712 fraction refused",
      refused (smallTyped (fld "a" "uint256") "{\"a\":1.5}") (.badValue "a")),
    ("EIP-712 exponent refused",
      refused (smallTyped (fld "a" "uint256") "{\"a\":1e18}") (.badValue "a")),
    ("EIP-712 JSON number above 2^53 - 1 refused",
      refused (smallTyped (fld "a" "uint256") "{\"a\":9007199254740992}") (.badValue "a")),
    ("EIP-712 same number as a string accepted",
      isOk (signRequestOfJson risk
        (smallTyped (fld "a" "uint256") "{\"a\":\"9007199254740992\"}"))),
    ("EIP-712 extra member refused",
      refused (smallTyped (fld "a" "uint8") "{\"a\":1,\"b\":2}") .extraField),
    ("EIP-712 missing member refused",
      refused (smallTyped (fld "a" "uint8" ++ "," ++ fld "b" "uint8") "{\"a\":1}")
        (.missingField "b")),
    ("EIP-712 duplicate key refused",
      refused (smallTyped (fld "a" "uint8") "{\"a\":1,\"a\":2}") .duplicateKey),
    ("EIP-712 uint without a width refused",
      refused (smallTyped (fld "a" "uint") "{\"a\":1}") (.badType "uint")),
    ("EIP-712 undeclared type refused",
      refused (smallTyped (fld "a" "Missing") "{\"a\":1}") (.badType "Missing")),
    ("EIP-712 short address refused",
      refused (smallTyped (fld "a" "address") "{\"a\":\"0x1234\"}") (.badValue "a")),
    ("EIP-712 bytes4 of 5 bytes refused",
      refused (smallTyped (fld "a" "bytes4") "{\"a\":\"0x0102030405\"}") (.badValue "a")),
    ("EIP-712 odd hex refused",
      refused (smallTyped (fld "a" "bytes") "{\"a\":\"0x123\"}") (.badValue "a")),
    ("EIP-712 fixed array of the wrong length refused",
      refused (smallTyped (fld "a" "uint8[2]") "{\"a\":[1,2,3]}") (.badValue "a")),
    ("EIP-712 domain with an unknown field refused",
      isErr712 (signRequestOfJson risk
        "{\"types\":{\"EIP712Domain\":[{\"name\":\"owner\",\"type\":\"address\"}],\"T\":[]},\"primaryType\":\"T\",\"domain\":{},\"message\":{}}")
        (.badType "EIP712Domain")),
    ("EIP-712 domain fields out of the standard order refused",
      isErr712 (signRequestOfJson risk
        "{\"types\":{\"EIP712Domain\":[{\"name\":\"chainId\",\"type\":\"uint256\"},{\"name\":\"name\",\"type\":\"string\"}],\"T\":[]},\"primaryType\":\"T\",\"domain\":{\"chainId\":1,\"name\":\"x\"},\"message\":{}}")
        (.badType "EIP712Domain")),
    ("EIP-712 primary type EIP712Domain refused",
      isErr712 (signRequestOfJson risk
        "{\"types\":{\"EIP712Domain\":[]},\"primaryType\":\"EIP712Domain\",\"domain\":{},\"message\":{}}")
        (.badType "EIP712Domain")),
    ("EIP-712 struct type named as an elementary type refused",
      isErr712 (signRequestOfJson risk
        "{\"types\":{\"EIP712Domain\":[],\"uint256\":[]},\"primaryType\":\"uint256\",\"domain\":{},\"message\":{}}")
        (.badType "types")),
    ("EIP-712 recursive type, data 10 deep accepted",
      isOk (signRequestOfJson risk (smallTyped (fld "next" "T[]") (nest 10)))),
    ("EIP-712 recursive type, data 20 deep refused",
      refused (smallTyped (fld "next" "T[]") (nest 20)) .dataTooDeep),
    ("JSON nested 70 deep refused",
      isErr712 (parseJson (rep 70 "[" ++ rep 70 "]")) .jsonTooDeep),
    ("JSON nested 60 deep accepted", isOk (parseJson (rep 60 "[" ++ rep 60 "]"))),
    ("JSON over the size limit refused",
      isErr712 (parseJson ("\"" ++ rep 110000 "0123456789" ++ "\"")) .jsonTooLong),
    ("JSON trailing text refused", isErr712 (parseJson "{} x") .jsonSyntax),
    ("JSON unterminated string refused", isErr712 (parseJson "\"abc") .jsonSyntax),
    ("JSON lone surrogate refused", isErr712 (parseJson "\"\\ud800\"") .jsonSyntax),
    ("JSON surrogate pair read",
      (match parseJson "\"\\ud83d\\ude00\"" with
        | .ok (.str s) => s.toList.map Char.toNat == [0x1F600]
        | _ => false)),
    ("JSON control character in a string refused",
      isErr712 (parseJson ("\"a" ++ String.ofList [Char.ofNat 1] ++ "\"")) .jsonSyntax),
    ("JSON leading zero refused", isErr712 (parseJson "01") .jsonSyntax),
    ("JSON object with 300 members refused",
      isErr712 (parseJson ("{" ++ ",".intercalate ((List.range 300).map fun i =>
        "\"k" ++ toString i ++ "\":1") ++ "}")) .tooManyMembers),
    ("personal_sign hello world",
      hexOf (personalSignDigest risk (utf8 "hello world"))
        == "d9eba16ed0ecae432b71fe008c98cc872bb4cc214d3220a36f365326cf807d68"),
    ("personal_sign Hello World",
      hexOf (personalSignDigest risk (utf8 "Hello World"))
        == "a1de988600a42c4b4ab089b619297c17d53cffae5d5120d82d8a92d0bb3b78f2") ]

def usdc : Nat := 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48
def weth : Nat := 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2
def router : Nat := 0x68b3465833fb72A70ecDF485E0e4C7bD8665Fc45
def me : Nat := 0x00000000219ab540356cBB839Cbe05303d7705Fa

def sampleSwap : ExactInputSingle :=
  { tokenIn := weth, tokenOut := usdc, fee := 500, recipient := me,
    amountIn := 1000000000000000000, amountOutMinimum := 2990000000 }

def sampleSwapCall : List UInt8 := swapWithDeadline 1800000000 [exactInputSingle sampleSwap]

def permitJson (value deadline : String) : String :=
  "{\"types\":{\"EIP712Domain\":[{\"name\":\"name\",\"type\":\"string\"},{\"name\":\"version\",\"type\":\"string\"},{\"name\":\"chainId\",\"type\":\"uint256\"},{\"name\":\"verifyingContract\",\"type\":\"address\"}],\"Permit\":[{\"name\":\"owner\",\"type\":\"address\"},{\"name\":\"spender\",\"type\":\"address\"},{\"name\":\"value\",\"type\":\"uint256\"},{\"name\":\"nonce\",\"type\":\"uint256\"},{\"name\":\"deadline\",\"type\":\"uint256\"}]},\"primaryType\":\"Permit\",\"domain\":{\"name\":\"USD Coin\",\"version\":\"2\",\"chainId\":1,\"verifyingContract\":\"0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48\"},\"message\":{\"owner\":\"0x1111111111111111111111111111111111111111\",\"spender\":\"0x2222222222222222222222222222222222222222\",\"value\":\""
    ++ value ++ "\",\"nonce\":0,\"deadline\":\"" ++ deadline ++ "\"}}"

def maxStr : String := toString maxUint256

def callVectors (risk : MessageHashing) : List (String × Bool) :=
  let d (to value : Nat) (kind : TokenKind) (data : List UInt8) : CallSummary :=
    describeCall me to value kind (toBytes data)
  let has (s : CallSummary) (w : Warning) : Bool := s.warnings.contains w
  let swap := d router 0 .unknown sampleSwapCall
  let permit2 (p : PermitSingle) (chain : Nat) : Option SignSummary :=
    (permit2Request risk 1 p).toOption.map (describeTypedData chain)
  let p2 : PermitSingle :=
    { token := usdc, amount := 1000, expiration := 1800000000, nonce := 0, spender := router,
      sigDeadline := 1800000000 }
  let hasS (s : Option SignSummary) (w : SignWarning) : Bool :=
    match s with
    | some x => x.warnings.contains w
    | none => false
  let permit (value deadline : String) : Option SignSummary :=
    (signRequestOfJson risk (permitJson value deadline)).toOption.map (describeTypedData 1)
  let p2Table := (buildTable permit2Types).toOption.getD []
  let typeHashOf (n : String) : String :=
    match p2Table.find? (·.name == n) with
    | some e => hexOf e.typeHash
    | none => ""
  [ ("pinned addresses carry valid EIP-55 checksums", pinned.all fun p => validChecksum p.address),
    ("Permit2 constant matches its pinned entry",
      pinnedAddress? "Permit2" mainnet == some permit2Address),
    ("EIP-55 specification addresses",
      ["0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed", "0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359",
        "0xdbF03B407c01E7cD3CBea99509d93f8DDDC8C6FB", "0xD1220A0cf47c7B9Be7A2E6BA89F429762e7b9aDb",
        "0x52908400098527886E0F7030069857D2E4169EE7", "0x8617E340B3D01FA5F11F306F4090FD50E238070D",
        "0xde709f2102306220921060314715629080e2fb77",
        "0x27b1fdb04752bbc536007a920d24acb045561c26"].all validChecksum),
    ("EIP-55 wrong case refused", !validChecksum "0x5AAeb6053F3E94C9b9A09f33669435E7Ef1BeAed"),
    ("describe: empty calldata is a native transfer",
      (match (d addr1 5 .unknown []).action with
        | .nativeTransfer to v => to == addr1 && v == 5
        | _ => false)),
    ("describe: ERC-20 transfer",
      (match (d usdc 0 .erc20 (erc20Transfer addr1 77)).action with
        | .erc20Transfer token to amount => token == usdc && to == addr1 && amount == 77
        | _ => false)),
    ("describe: transfer to the token contract is flagged",
      has (d usdc 0 .erc20 (erc20Transfer usdc 77)) .suspectRecipient),
    ("describe: unlimited approval is flagged",
      has (d usdc 0 .erc20 (erc20Approve router maxUint256)) .unlimitedApproval),
    ("describe: bounded approval is not flagged as unlimited",
      !has (d usdc 0 .erc20 (erc20Approve router 1000)) .unlimitedApproval),
    ("describe: approve on an unknown token says amount or token id",
      has (d addr2 0 .unknown (erc20Approve router 1000)) .amountOrTokenId),
    ("describe: setApprovalForAll(true) is flagged",
      has (d addr2 0 .erc721 (erc721SetApprovalForAll router true)) .approvalForAll),
    ("describe: setApprovalForAll(false) is not flagged",
      !has (d addr2 0 .erc721 (erc721SetApprovalForAll router false)) .approvalForAll),
    ("describe: WETH deposit shows the value",
      (match (d weth 123 .erc20 wethDeposit).action with
        | .wethDeposit _ amount => amount == 123
        | _ => false)),
    ("describe: WETH withdraw",
      (match (d weth 0 .erc20 (wethWithdraw 9)).action with
        | .wethWithdraw _ amount => amount == 9
        | _ => false)),
    ("describe: swap inside a deadline multicall",
      (match swap.action with
        | .multicall deadline [.swapExactInput r p] =>
          deadline == 1800000000 && r == router && p.tokenIn == weth && p.tokenOut == usdc
            && p.fee == 500 && p.recipient == me && p.amountIn == 1000000000000000000
            && p.amountOutMinimum == 2990000000
        | _ => false)),
    ("describe: that swap raises no warning", swap.warnings.isEmpty),
    ("describe: bare swap has no deadline",
      has (d router 0 .unknown (exactInputSingle sampleSwap)) .noDeadline),
    ("describe: swap with zero minimum output is flagged",
      has (d router 0 .unknown
        (swapWithDeadline 1 [exactInputSingle { sampleSwap with amountOutMinimum := 0 }]))
        .noSlippageProtection),
    ("describe: swap to another recipient is flagged",
      has (d router 0 .unknown
        (swapWithDeadline 1 [exactInputSingle { sampleSwap with recipient := addr2 }]))
        .recipientNotSender),
    ("describe: exact-output swap with unlimited input is flagged",
      has (d router 0 .unknown
        (swapWithDeadline 1 [exactOutputSingle
          { tokenIn := weth, tokenOut := usdc, fee := 500, recipient := me, amountOut := 5,
            amountInMaximum := maxUint256 }])) .noSlippageProtection),
    ("describe: unknown selector",
      (match (d addr1 1 .unknown (hx "deadbeef")) with
        | ⟨.unknown s, ws⟩ => s == hx "deadbeef" && ws.contains .unknownFunction
            && ws.contains .valueWithUnknownCall
        | _ => false)),
    ("describe: known selector with a trailing byte is malformed, not decoded",
      (match (d usdc 0 .erc20 (erc20Approve router 5 ++ [0])) with
        | ⟨.malformed _, ws⟩ => ws.contains .malformedCalldata
        | _ => false)),
    ("describe: nested multicall is not decoded and is flagged",
      has (d router 0 .unknown (swapWithDeadline 1 [swapWithDeadline 2 []])) .innerCallNotDecoded),
    ("describe: approval of 2^200 is flagged as very large",
      has (d usdc 0 .erc20 (erc20Approve router (2 ^ 200))) .veryLargeApproval),
    ("chain: approval to the pinned router raises no unknown-spender warning",
      !(describeTx mainnet me usdc 0 .erc20 (toBytes (erc20Approve router 5))).warnings.contains
        .unknownSpender),
    ("chain: approval to an unpinned spender is flagged",
      (describeTx mainnet me usdc 0 .erc20 (toBytes (erc20Approve addr2 5))).warnings.contains
        .unknownSpender),
    ("chain: the mainnet router address is unknown on Sepolia",
      (describeTx sepolia me usdc 0 .erc20 (toBytes (erc20Approve router 5))).warnings.contains
        .unknownSpender),
    ("chain: setApprovalForAll to an unpinned operator is flagged",
      (describeTx mainnet me addr1 0 .erc721
        (toBytes (erc721SetApprovalForAll addr2 true))).warnings.contains .unknownSpender),
    ("chain: swap on the pinned router is not flagged",
      (describeTx mainnet me router 0 .unknown (toBytes sampleSwapCall)).warnings.isEmpty),
    ("chain: the same swap on another address is flagged",
      (describeTx mainnet me addr2 0 .unknown (toBytes sampleSwapCall)).warnings
        == [.unverifiedTarget]),
    ("chain: deposit() on an address that is not WETH9 is flagged",
      (describeTx mainnet me addr2 7 .unknown (toBytes wethDeposit)).warnings
        == [.unverifiedTarget]),
    ("chain: deposit() on WETH9 is not flagged",
      (describeTx mainnet me weth 7 .erc20 (toBytes wethDeposit)).warnings.isEmpty),
    ("chain: Permit2 to the pinned router has a known spender",
      !hasS (permit2 p2 1) .unknownSpender),
    ("chain: Permit2 to an unpinned spender is flagged",
      hasS (permit2 { p2 with spender := addr2 } 1) .unknownSpender),
    ("chain: EIP-2612 permit to an unpinned spender is flagged",
      hasS (permit "1000" "1800000000") .unknownSpender),
    ("slippage: 50 bp below 2000", minOutForSlippage 2000 50 == 1990),
    ("slippage: 50 bp above 2000", maxInForSlippage 2000 50 == 2010),
    ("slippage: rounding goes against the trader's counterparty, never past the quote",
      minOutForSlippage 3 50 == 2 && maxInForSlippage 3 50 == 4),
    ("Permit2 PermitDetails type hash", typeHashOf "PermitDetails"
      == "65626cad6cb96493bf6f5ebea28756c966f023ab9e8a83a7101849d5573b3678"),
    ("Permit2 PermitSingle type hash", typeHashOf "PermitSingle"
      == "f3841cd1ff0085026a6327b620b67997ce40f282c88a8e905a7a5626e310f3d0"),
    ("Permit2 mainnet domain separator",
      ((permit2Request risk 1 p2).toOption.map fun r => hexOf r.domainSeparator)
        == some "866a5aba21966af95d6c7ab78eb2b2fc913915c28be3b9aa07cc04ff903e3f28"),
    ("Permit2 PermitSingle is read back as an approval by signature",
      (match permit2 p2 1 with
        | some ⟨.permit2Single token amount _ _ spender _, ws, _, _⟩ =>
          token == usdc && amount == 1000 && spender == router
            && ws.contains .approvalBySignature && !ws.contains .unlimitedAmount
            && !ws.contains .notCanonicalPermit2
        | _ => false)),
    ("Permit2 unlimited amount is flagged",
      hasS (permit2 { p2 with amount := maxUint160 } 1) .unlimitedAmount),
    ("Permit2 no expiry is flagged",
      hasS (permit2 { p2 with expiration := maxUint48 } 1) .noExpiry),
    ("Permit2 on another chain is flagged", hasS (permit2 p2 5) .chainMismatch),
    ("EIP-2612 permit is read back",
      (match permit "1000" "1800000000" with
        | some ⟨.permit token owner spender value _ deadline, ws, _, _⟩ =>
          token == usdc && owner == addr1 && spender == addr2 && value == 1000
            && deadline == 1800000000 && ws.contains .approvalBySignature
        | _ => false)),
    ("EIP-2612 unlimited permit with no expiry is flagged",
      hasS (permit maxStr maxStr) .unlimitedAmount && hasS (permit maxStr maxStr) .noExpiry),
    ("unrecognised typed data is flagged",
      hasS ((signRequestOfJson risk mailJson).toOption.map (describeTypedData 1))
        .unrecognisedTypedData),
    ("typed data with no verifying contract is flagged",
      hasS ((signRequestOfJson risk (smallTyped (fld "a" "uint8") "{\"a\":1}")).toOption.map
        (describeTypedData 1)) .noVerifyingContract),
    ("personal_sign text shown", (describePersonalSign risk (utf8 "hello")).text == some "hello"
      && (describePersonalSign risk (utf8 "hello")).warnings.isEmpty),
    ("personal_sign 32 opaque bytes flagged",
      (describePersonalSign risk (keccak256 [])).warnings.contains .opaqueHash),
    ("personal_sign direction override flagged",
      (describePersonalSign risk (utf8 ("pay " ++ String.ofList [Char.ofNat 0x202e] ++ "x"))).warnings
        == [.hiddenCharacters]),
    ("EIP-7702 delegation always warns of full control",
      (describeAuthorization 1 [] ⟨1, addr1, 0⟩).warnings
        == [.fullAccountControl, .unknownDelegate]),
    ("EIP-7702 chain id 0 is flagged as valid on all chains",
      (describeAuthorization 1 [addr1] ⟨0, addr1, 0⟩).warnings
        == [.fullAccountControl, .validOnAllChains]),
    ("EIP-7702 zero address clears the delegation",
      (describeAuthorization 1 [] ⟨1, 0, 0⟩).action == .clearDelegation),
    ("EIP-7702 designator read",
      delegationDesignator? (hx "ef0100" ++ beBytes 20 addr1) == some addr1),
    ("EIP-7702 ordinary code is not a designator", delegationDesignator? (hx "6080604052") == none) ]

def deployVectors : List (String × Bool) :=
  let sender : Nat := 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0
  let c2 (s : Nat) (salt : Nat) (code : String) : String :=
    "0x" ++ hexOf (beBytes 20 (create2Address s salt (hx code)))
  let c1 (nonce : Nat) : String := hexOf (beBytes 20 (createAddress sender nonce))
  let initcode := hx "6080604052348015600e575f80fd5b50"
  let data := creationData initcode [.address, .string] [.address addr1, .bytes (utf8 "Token")]
  [ ("CREATE nonce 0", c1 0 == "cd234a471b72ba2f1ccf0a70fcaba648a5eecd8d"),
    ("CREATE nonce 1", c1 1 == "343c43a37d37dff08ae8c4a11544c718abb4fcf8"),
    ("CREATE nonce 2", c1 2 == "f778b86fa74e846c4f0a1fbd1335fe81c00a0c91"),
    ("CREATE nonce 3", c1 3 == "fffd933a0bc612844eaf0c6fe3e5b8e9b6c1d19c"),
    ("CREATE preimage nonce 0", hexOf (createPreimage sender 0)
      == "d6946ac7ea33f8831ea9dcc53393aaa88b25a785dbf080"),
    ("CREATE preimage nonce 128", hexOf (createPreimage sender 128)
      == "d7946ac7ea33f8831ea9dcc53393aaa88b25a785dbf08180"),
    ("CREATE preimage nonce 2^64 - 1", hexOf (createPreimage sender maxNonce)
      == "de946ac7ea33f8831ea9dcc53393aaa88b25a785dbf088ffffffffffffffff"),
    ("RLP of 60 bytes uses a long header",
      hexOf ((Rlp.bytes (zeros 60)).encode) == "b83c" ++ rep 60 "00"),
    ("RLP empty list", hexOf ((Rlp.list []).encode) == "c0"),
    ("CREATE2 EIP-1014 example 1", c2 0 0 "00" == "0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38"),
    ("CREATE2 EIP-1014 example 2",
      c2 0xdeadbeef00000000000000000000000000000000 0 "00"
        == "0xb928f69bb1d91cd65274e3c79d8986362984fda3"),
    ("CREATE2 EIP-1014 example 3",
      c2 0xdeadbeef00000000000000000000000000000000
        0x000000000000000000000000feed000000000000000000000000000000000000 "00"
        == "0xd04116cdd17bebe565eb2422f2497e06cc1c9833"),
    ("CREATE2 EIP-1014 example 4", c2 0 0 "deadbeef"
      == "0x70f2b2914a2a4b783faefb75f459a580616fcb5e"),
    ("CREATE2 EIP-1014 example 5",
      c2 0x00000000000000000000000000000000deadbeef 0xcafebabe "deadbeef"
        == "0x60f3f640a8508fc6a86d45df051962668e1e8ac7"),
    ("CREATE2 EIP-1014 example 6",
      c2 0x00000000000000000000000000000000deadbeef 0xcafebabe
        "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
        == "0x1d8bfdc5d46dc4f61d6b6115972536ebe6a8854c"),
    ("CREATE2 EIP-1014 example 7", c2 0 0 "" == "0xe33c0c7f7df4809055c3eba6c09cfe4baf1bd9e0"),
    ("creation data is initcode then arguments", data.take initcode.length == initcode),
    ("constructor arguments read back",
      (match decodeArgsAt [.address, .string] (toBytes data) initcode.length with
        | .ok [.address a, .bytes s] => a == addr1 && s == utf8 "Token"
        | _ => false)) ]

/-- All groups. The typed-data and signing groups hash message content, so the caller passes
    the risk token; the executable makes one only under its `--dangerously-…` flag. -/
def all (risk : MessageHashing) : List (String × List (String × Bool)) := [
  ("solidity-abi-spec", specVectors),
  ("selectors-and-topics", selectorVectors),
  ("type-grammar", typeVectors),
  ("round-trips", roundTripVectors),
  ("decoder-negative-controls", negativeControls),
  ("events-and-returns", eventVectors),
  ("eip712-eip191-json", typedDataVectors risk),
  ("calls-and-summaries", callVectors risk),
  ("deployment", deployVectors)
]

end EthereumWallet.AbiVectors
