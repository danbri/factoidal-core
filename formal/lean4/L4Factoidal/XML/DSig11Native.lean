/-
L4Factoidal.XML.DSig11Native — the backend of `L4Factoidal.XML.DSig11`
over HACL*: the RSA public operation (`Crypto.Rsa.rsaPublicOp`, moduli of
2048, 3072 and 4096 bits) and ECDSA P-256 with each of the five digests of
§6.2 (`Crypto.P256.p256VerifyHash`: the digest is computed in Lean by
`DigestAlg.digest`, and HACL* checks the signature over its FIPS 186-4 §6.4
representative). P-384 and P-521 give `none`, which
`DSig11.signatureValueOk` reports as not available
(https://github.com/danbri/factoidal/issues/1223): HACL* has no P-384 or
P-521 (https://github.com/danbri/factoidal/issues/1166).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.DSig11
import L4Factoidal.Crypto.RsaNative
import L4Factoidal.Crypto.P256Native
import L4Factoidal.Crypto.RsaOaep
import L4Factoidal.XML.DSig11Sign

namespace L4Factoidal.XML.DSig11

def nativeBackend : Backend where
  rsaPublicOp := Crypto.Rsa.rsaPublicOp
  ecdsaVerify := fun c h xy msg sig =>
    if c == .p256 then some (Crypto.P256.p256VerifyHash xy (h.digest msg) sig) else none

/-- XML Signature 1.1 §6.4.3 over HACL*: every `ecdsa-sha*` method at P-256
is the HACL* check over the FIPS 186-4 §6.4 representative of the Lean
digest of the canonical `ds:SignedInfo`. -/
theorem dsig11_native_ecdsa_p256 (h : DigestAlg) (xy msg sig : ByteArray) :
    nativeBackend.ecdsaVerify .p256 h xy msg sig =
      some (Crypto.P256.p256VerifyPrehashed xy (Crypto.P256.p256MsgRep (h.digest msg)) sig) := rfl

/-- P-384 and P-521 stay unavailable (https://github.com/danbri/factoidal/issues/1223). -/
theorem dsig11_native_ecdsa_other_curves (c : Curve) (hc : c ≠ .p256) (h : DigestAlg)
    (xy msg sig : ByteArray) : nativeBackend.ecdsaVerify c h xy msg sig = none := by
  simp [nativeBackend, hc]

/-! ## Signers (the custodians of `XML/DSig11Sign.lean`)

The one place in the XML Signature code where a private key becomes a
`Signer`. The key stays in the closure; a caller gets signature values, the
algorithm and the public key only. -/

/-- RSASSA-PKCS1-v1_5 (RFC 8017 §8.2.1) with the digest `h`: the
EMSA-PKCS1-v1_5 block is generated in Lean (`JOSE.Pkcs1.emsaEncodeGen`, the
function the verifier compares with) and the RSA private operation is HACL*
`Hacl_Bignum64_mod_exp_consttime` (`Crypto.RsaOaep.rsaPrivateOp`; moduli of
2048, 3072 and 4096 bits). Before a value is given out it is checked with
the public operation, so a fault in the private operation does not give out
a wrong value (Boneh, DeMillo and Lipton 1997). -/
def rsaSigner (h : DigestAlg) (n e d : ByteArray) : Option Signer :=
  if n.size * 8 < 2048 then none else
  some { alg := .rsa h
         publicKey := some (.rsa n e)
         sign := fun m _ => do
           let em ← JOSE.Pkcs1.emsaEncodeGen h.digestInfo h.size (h.digest m).data.toList n.size
           let s ← Crypto.RsaOaep.rsaPrivateOp n d ⟨em.toArray⟩
           if JOSE.Pkcs1.rsaPkcs1Verify Crypto.Rsa.rsaPublicOp h.digestInfo h.size n e s (h.digest m)
           then some s else none }

/-- ECDSA P-256 with the digest `h` (§6.4.3; FIPS 186-4 §6.4) by HACL*
`Hacl_P256_ecdsa_sign_p256_without_hash` over the representative of
`h.digest m` (`Crypto.P256.p256SignHash`), with the value `r || s`. The
nonce is the `rand` of each call: 32 fresh random octets from the host.
`none` for a secret HACL* refuses. Before a value is given out it is checked
with the verifier of `nativeBackend`. -/
def p256Signer (sk : ByteArray) (h : DigestAlg := .sha256) : Option Signer :=
  match Crypto.P256.p256SecretToPublic sk with
  | none => none
  | some xy => some { alg := .ecdsa h
                      publicKey := some (.ec .p256 xy)
                      sign := fun m rand =>
                        if rand.size != 32 then none else do
                          let s ← Crypto.P256.p256SignHash sk (h.digest m) rand
                          if Crypto.P256.p256VerifyHash xy (h.digest m) s then some s else none }

end L4Factoidal.XML.DSig11
