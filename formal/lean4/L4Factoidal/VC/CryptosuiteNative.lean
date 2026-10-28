/-
L4Factoidal.VC.CryptosuiteNative — the HACL* primitives and the signer
component that `VC/Cryptosuite.lean` takes as parameters, for every target
that links `libl4hacl` (native executables and the wasm module).

  * `diPrimitives`: Ed25519 verification (`Crypto/Ed25519.lean`) and ECDSA
    P-256 with SHA-256 (`Crypto/P256Native.lean`, HACL*
    `Hacl_P256_ecdsa_verif_p256_sha2`). P-384 is not available: HACL* has no
    P-384 (https://github.com/danbri/factoidal/issues/1166).
  * `diSigner`: the one place a secret key becomes a `Signer`, the custodian
    of that key (`docs/web/hub/webdav-lws-design.md`, "One custodian per
    privileged resource"). The key stays in the signer's closure; callers get
    signatures and the verification method only. The ECDSA nonce is drawn by
    the host's random source and passed in; this tree derives no nonce.

Trust: as in the two binding modules. Nothing here computes a signature;
`compressP256` is SEC 1 point compression (a byte choice, no arithmetic).
The run-time checks are `lake exe l4vc-probe`, section `vc-di-ecdsa`.
-/
import L4Factoidal.Crypto.Ed25519
import L4Factoidal.Crypto.P256Native
import L4Factoidal.VC.Cryptosuite

namespace L4Factoidal.VC.Cryptosuite

open L4Factoidal.Crypto

/-- SEC 1 v2 §2.3.3 point compression of a raw 64-byte `x || y` P-256 key:
0x02 when `y` is even, 0x03 when it is odd, then `x`. -/
def compressP256 (xy : ByteArray) : ByteArray :=
  let parity := (xy.get! 63) % 2
  ByteArray.mk #[if parity == 0 then 2 else 3] ++ xy.extract 0 32

/-- The verifying primitives of this target: HACL* Ed25519 and P-256. A
P-256 key comes compressed (33 bytes, Multikey) or raw (64 bytes, JWK);
HACL* decompresses and checks the point. No P-384 (issue 1166). -/
def diPrimitives : Primitives :=
  { verify := fun c pk msg sig =>
      match c with
      | .ed25519 => Ed25519.verify pk msg sig
      | .p256 =>
          let raw? := if pk.size == 64 then some pk
            else if pk.size == 33 then P256.p256CompressedToRaw pk else none
          match raw? with
          | some raw => P256.p256VerifySha256 raw msg sig
          | none => false
      | .p384 => false
    available := fun c => c != .p384 }

/-- The signer component of this target: the one place a secret key is
turned into a `Signer` (the custodian of that key; the key does not leave
its closure). `none` for a key HACL* refuses and for P-384. -/
def diSigner (c : Curve) (sk nonce : ByteArray) : Option Signer :=
  match c with
  | .ed25519 =>
      let pk := Ed25519.secretToPublic sk
      if pk.size != 32 then none
      else some { curve := .ed25519
                  verificationMethod := didKeyVerificationMethod ⟨.ed25519, pk⟩
                  sign := fun m => let sg := Ed25519.sign sk m; if sg.size == 64 then some sg else none }
  | .p256 =>
      match P256.p256SecretToPublic sk with
      | none => none
      | some xy => some { curve := .p256
                          verificationMethod := didKeyVerificationMethod ⟨.p256, compressP256 xy⟩
                          sign := fun m => P256.p256SignSha256 sk m nonce }
  | .p384 => none

end L4Factoidal.VC.Cryptosuite
