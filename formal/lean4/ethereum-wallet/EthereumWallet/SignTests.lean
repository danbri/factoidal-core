import EthereumWallet.TxSign

/-!
# Build-time checks for signing and transaction encoding

A small set of `#guard` tests (each one is a test, not a proof) that run
whenever the library is built: the EIP-155 specification example byte for
byte, a published RFC 6979 secp256k1 signature, the comb multiplication
against the shared double-and-add, every refusal, and negative controls.
The large suites (execution-specs fixtures, Wycheproof, the bitcoinjs
RFC 6979 fixture, the differential run) are run by `eth-wallet-sign` in CI.

Keys here are published test values (the EIP-155 example key, the scalar 1).
-/

namespace EthereumWallet.SignTests

open EVMCleanroom.Precompiles
open EthereumWallet EthereumWallet.Secp EthereumWallet.Sign EthereumWallet.Tx
open EthereumWallet.TxSign EthereumWallet.TxDecode

private def table : BaseTable := BaseTable.build ()
-- Test code only: published keys, so the timing risk is accepted here by name.
private def risk : Risk.Accepted .variableTimeSigning := Risk.dangerouslyAccept .variableTimeSigning
private def n : Nat := Secp256k1.n

/-- The private key of the EIP-155 specification example (published). -/
private def eip155Key : Nat := 0x4646464646464646464646464646464646464646464646464646464646464646

/-- The transaction of the EIP-155 specification example. -/
private def eip155Tx : Unsigned :=
  { kind := 0, chainId := some 1, nonce := 9, maxPriorityFeePerGas := 0,
    maxFeePerGas := 20000000000, gasLimit := 21000,
    to := some 0x3535353535353535353535353535353535353535, value := 1000000000000000000,
    data := #[], accessList := [], maxFeePerBlobGas := 0, blobVersionedHashes := [],
    authorizationList := [] }

/-- A signing result as a comparable pair (signature, error). -/
private def outcome (result : Except Sign.Error Signature) : Option Signature × Option Sign.Error :=
  match result with
  | .ok sig => (some sig, none)
  | .error e => (none, some e)

private def signedHex (key : Nat) (tx : Unsigned) : String :=
  match KeyPair.ofSecret table key with
  | none => "no key"
  | some kp =>
    match signTransaction risk table kp tx with
    | .ok out => toHex out.raw
    | .error e => reprStr e

-- The comb table has 64 rows of 16 entries, and agrees with the shared double-and-add.
#guard table.entries.size == 1024
#guard [1, 2, 15, 16, 17, 0xdeadbeef, n - 1, n - 2, 2 ^ 255 + 12345, combOffset, combOffset + 1].all
  fun k => mulBaseSecret table k == Secp256k1.mulBase k
#guard mulBaseSecret table 0 == none && mulBaseSecret table n == none
#guard invFixed n 7 * 7 % n == 1 && invFixed n 0 == 0

-- EIP-155 specification example: signing payload, signing hash, signed transaction.
#guard toHex (signingPayload eip155Tx) ==
  "ec098504a817c800825208943535353535353535353535353535353535353535880de0b6b3a764000080018080"
#guard toHex (signingHash eip155Tx) ==
  "daf5a779ae972f972197303d7b574746c7ef83eadac0f2791ad23db92e4c8e53"
#guard signedHex eip155Key eip155Tx ==
  "f86c098504a817c800825208943535353535353535353535353535353535353535880de0b6b3a7640000" ++
  "8025a028ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276" ++
  "a067cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83"
#guard (KeyPair.ofSecret table eip155Key).map (·.address) ==
  some 0x9d8a62f656a8d1615c1294fd71e9cfb3e4855a4f

-- A published RFC 6979 secp256k1 signature: key 1, SHA-256 of "Satoshi Nakamoto".
#guard ((KeyPair.ofSecret table 1).map fun kp =>
    outcome (signHash risk table kp (L4Factoidal.Crypto.sha256 "Satoshi Nakamoto".toUTF8))) ==
  some (some ⟨0x934b1ea10a4b3c1757e2b0c017d0b6143ce3c9a7e6a4a49860d7a6ab210ee3d8,
    0x2442ce9d2b916064108014783e923ec36b49743e2ffa1c4496f01a512aafd9e5, 1⟩, none)

-- Every kind signs and is read back (the check is inside `signTransaction`).
#guard (signedHex eip155Key { eip155Tx with chainId := none }).startsWith "f86c"
#guard (signedHex eip155Key { eip155Tx with kind := 1, accessList := [⟨7, [1, 2]⟩] }).startsWith "01f8"
#guard (signedHex eip155Key { eip155Tx with kind := 2, to := none, data := #[0x60, 0x00] }).startsWith "02f8"
private def blobTx : Unsigned :=
  { eip155Tx with kind := 3, maxFeePerBlobGas := 5, blobVersionedHashes := [2 ^ 248 + 77] }
private def setCodeTx : Unsigned :=
  { eip155Tx with kind := 4, authorizationList := [⟨1, 0x1111111111111111111111111111111111111111, 5, 0, 3, 4⟩] }
#guard (signedHex eip155Key blobTx).startsWith "03f8"
#guard (signedHex eip155Key setCodeTx).startsWith "04f8"

-- Refusals.
#guard KeyPair.ofSecret table 0 |>.isNone
#guard KeyPair.ofSecret table n |>.isNone
#guard ((KeyPair.ofSecret table 1).map fun kp => outcome (signHash risk table kp (natToBE 32 0))) ==
  some (none, some .zeroHash)
#guard ((KeyPair.ofSecret table 1).map fun kp => outcome (signHash risk table kp (natToBE 31 5))) ==
  some (none, some .hashLength)
#guard outcome (signHash risk table ⟨0, 1, 1⟩ (natToBE 32 5)) == (none, some .invalidKey)
-- A key pair whose public key is not that of its scalar never signs.
#guard outcome (signHash risk table ⟨1, Secp256k1.gx, Secp256k1.p - Secp256k1.gy⟩ (natToBE 32 5)) ==
  (none, some .selfCheckFailed)
#guard signedHex eip155Key { eip155Tx with kind := 5 } == reprStr Tx.Error.unknownKind
#guard signedHex eip155Key { eip155Tx with kind := 2, chainId := none } == reprStr Tx.Error.missingChainId
#guard signedHex eip155Key { eip155Tx with kind := 3 } == reprStr Tx.Error.noBlobHashes
#guard signedHex eip155Key { eip155Tx with kind := 3, to := none, blobVersionedHashes := [2 ^ 248] } ==
  reprStr Tx.Error.creationNotAllowed
#guard signedHex eip155Key { eip155Tx with kind := 3, blobVersionedHashes := [2 ^ 249] } ==
  reprStr Tx.Error.blobHashVersion
#guard signedHex eip155Key { eip155Tx with kind := 4 } == reprStr Tx.Error.noAuthorizations
#guard signedHex eip155Key { eip155Tx with nonce := 2 ^ 64 - 1 } == reprStr (Tx.Error.fieldRange "nonce")
#guard signedHex eip155Key { eip155Tx with maxPriorityFeePerGas := 1 } ==
  reprStr (Tx.Error.notEmpty "maxPriorityFeePerGas")
#guard signedHex eip155Key { eip155Tx with to := some (2 ^ 160) } == reprStr (Tx.Error.fieldRange "to")

-- Negative controls on the EIP-155 signature.
private def r155 : Nat := 0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276
private def s155 : Nat := 0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83
private def z155 : Nat := bytesToNat (signingHash eip155Tx)
private def q155 : Nat × Nat := (Secp256k1.mulBase eip155Key).getD (0, 0)

#guard verify z155 r155 s155 q155
#guard !verify (z155 + 1) r155 s155 q155
#guard !verify z155 r155 (s155 + 1) q155
#guard !verify z155 r155 s155 (Secp256k1.gx, Secp256k1.gy)
#guard !verify z155 r155 s155 (5, 5)
-- The high-s twin is a valid ECDSA signature, and `checkedRaw` does not produce it:
-- the wallet only ever encodes the signature `signHash` returned.
#guard verify z155 r155 (n - s155) q155 && n / 2 < n - s155
-- A raw transaction with one bit changed does not read back as the same transaction.
#guard (checkedRaw eip155Tx ⟨r155, s155, 0⟩).toOption.map toHex == some (signedHex eip155Key eip155Tx)
#guard (decodeBack 0 (hex (signedHex eip155Key eip155Tx)).data).toOption ==
  some (eip155Tx, ⟨r155, s155, 0⟩, (signingPayload eip155Tx).data)
#guard (decodeBack 0 ((hex (signedHex eip155Key eip155Tx)).data.modify 5 (· ^^^ 1))).toOption !=
  some (eip155Tx, ⟨r155, s155, 0⟩, (signingPayload eip155Tx).data)
-- Kind 4 is read by the wallet's set-code decoder, kinds 0 to 3 by the admission decoder.
#guard (decodeBack 4 (hex (signedHex eip155Key eip155Tx)).data).toOption.isNone
-- The authorization hash of EIP-7702 covers the magic byte 0x05 and the three fields.
#guard toHex (authorizationPayload 1 0x1111111111111111111111111111111111111111 5) ==
  "05d7019411111111111111111111111111111111111111" ++ "1105"

end EthereumWallet.SignTests
