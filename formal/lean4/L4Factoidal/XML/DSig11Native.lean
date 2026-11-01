/-
L4Factoidal.XML.DSig11Native — the backend of `L4Factoidal.XML.DSig11`
over HACL*: the RSA public operation (`Crypto.Rsa.rsaPublicOp`, moduli of
2048, 3072 and 4096 bits) and ECDSA P-256 with SHA-256
(`Crypto.P256.p256VerifySha256`). Every other curve and digest gives
`none`, which `DSig11.signatureValueOk` reports as not available
(https://github.com/danbri/factoidal/issues/1223).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.DSig11
import L4Factoidal.Crypto.RsaNative
import L4Factoidal.Crypto.P256Native

namespace L4Factoidal.XML.DSig11

def nativeBackend : Backend where
  rsaPublicOp := Crypto.Rsa.rsaPublicOp
  ecdsaVerify := fun c h xy msg sig =>
    if c == .p256 && h == .sha256 then some (Crypto.P256.p256VerifySha256 xy msg sig) else none

end L4Factoidal.XML.DSig11
