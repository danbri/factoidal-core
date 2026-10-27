/-
L4Factoidal.JOSE.JweKey — the keys of JSON Web Encryption (RFC 7516): the
recipient's PRIVATE key for decryption, the recipient's PUBLIC key for
encryption, and the ephemeral public key (`epk`) of ECDH-ES
(https://github.com/danbri/factoidal/issues/1085).

`JOSE/Jwk.lean` holds the public keys of the JWS verifier (EC P-256, RSA,
Ed25519). JWE needs other key material, so it has its own types here:

  * `DecKey` — the private key the recipient decrypts with:
    `rsa n d` (RFC 7518 §6.3.2.1, the `(n, d)` form `RsaOaep.rsaPrivateOp`
    takes), `ec d` (P-256, RFC 7518 §6.2.2.1), `x25519 d` (RFC 8037 §2,
    `crv` `X25519`), `oct k` (RFC 7518 §6.4.1, for `A128KW`, `A256KW` and
    `dir`).
  * `EncKey` — the public key a sender encrypts to: `rsa n e`, `ec x y`,
    `x25519 x`, and `oct k` (a symmetric key has no public half).
  * `Epk` — the ephemeral public key that an ECDH-ES sender puts in the
    protected header: `ec x y` or `x25519 x`. It is the ONLY key this tree
    writes into a JWE.

## No private member leaves through a written key

A JWE header is public. The only key a sender writes there is `epk`, and
`Epk.toJson` is the only function that renders one. `Epk` has no field for
a private scalar, so a private member cannot be put in; the theorem
`epk_no_private_member` states it over `JOSE.hasPrivateMember`, the same
predicate the DPoP check (`parsePublicJwk_no_private`) and the
authorization server's JWKS (`Authz.jwks_no_private_member`) use. A
`DecKey` has no rendering function at all.

## Sizes are checked at parse time

Every constructor's field sizes are fixed by the parse, so a consumer does
not re-check them: RSA modulus 256, 384 or 512 octets (the sizes HACL*
`rsaPrivateOp` accepts) with a non-empty `d` no longer than the modulus;
P-256 coordinates and scalar 32 octets; X25519 values 32 octets; `oct` keys
16, 24, 32, 48 or 64 octets (the CEK and KEK lengths of RFC 7518 §4.4, §5.2,
§5.3; 24 and 48 are parsed and then refused by every algorithm this tree
allows).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.JOSE.Jwk

namespace L4Factoidal.JOSE.JweKey

open L4Factoidal.JSON
open L4Factoidal.JOSE

/-- A recipient's private key for JWE decryption. -/
inductive DecKey where
  | rsa (n d : ByteArray)
  | ec (d : ByteArray)
  | x25519 (d : ByteArray)
  | oct (k : ByteArray)

/-- A recipient's public key for JWE encryption. -/
inductive EncKey where
  | rsa (n e : ByteArray)
  | ec (x y : ByteArray)
  | x25519 (x : ByteArray)
  | oct (k : ByteArray)

/-- The ephemeral public key of ECDH-ES (RFC 7518 §4.6.1.1). -/
inductive Epk where
  | ec (x y : ByteArray)
  | x25519 (x : ByteArray)
  deriving BEq

/-- The symmetric key lengths a JWK `oct` key may have here. -/
def octSizes : List Nat := [16, 24, 32, 48, 64]

private def member? (j : Json) (name : String) : Option ByteArray :=
  (j.getString? name).bind Base64Url.decode

/-- Parse a private JWK for decryption. Members the key type does not need
(`kid`, `use`, `alg`, the RSA CRT members) are ignored. -/
def parseDecKey? (j : Json) : Option DecKey :=
  match j.getString? "kty" with
  | some "RSA" =>
      match member? j "n", member? j "d" with
      | some n, some d =>
          if acceptedModulusSize n.size && d.size != 0 && d.size ≤ n.size
          then some (.rsa n d) else none
      | _, _ => none
  | some "EC" =>
      match j.getString? "crv", member? j "d" with
      | some "P-256", some d => if d.size == 32 then some (.ec d) else none
      | _, _ => none
  | some "OKP" =>
      match j.getString? "crv", member? j "d" with
      | some "X25519", some d => if d.size == 32 then some (.x25519 d) else none
      | _, _ => none
  | some "oct" =>
      match member? j "k" with
      | some k => if octSizes.contains k.size then some (.oct k) else none
      | none => none
  | _ => none

/-- Parse the PUBLIC members of a JWK for encryption. A private member, when
present, is not read. -/
def parseEncKey? (j : Json) : Option EncKey :=
  match j.getString? "kty" with
  | some "RSA" =>
      match member? j "n", member? j "e" with
      | some n, some e =>
          if acceptedModulusSize n.size && e.size != 0 then some (.rsa n e) else none
      | _, _ => none
  | some "EC" =>
      match j.getString? "crv", member? j "x", member? j "y" with
      | some "P-256", some x, some y =>
          if x.size == 32 && y.size == 32 then some (.ec x y) else none
      | _, _, _ => none
  | some "OKP" =>
      match j.getString? "crv", member? j "x" with
      | some "X25519", some x => if x.size == 32 then some (.x25519 x) else none
      | _, _ => none
  | some "oct" =>
      match member? j "k" with
      | some k => if octSizes.contains k.size then some (.oct k) else none
      | none => none
  | _ => none

/-- Parse the `epk` header member (RFC 7518 §4.6.1.1): a PUBLIC key on
P-256 or X25519. An `epk` carrying a private member is refused: a sender
that writes its ephemeral private scalar into the header has published the
key that protects the content. -/
def parseEpk? (j : Json) : Option Epk :=
  if hasPrivateMember j then none
  else
    match j.getString? "kty" with
    | some "EC" =>
        match j.getString? "crv", member? j "x", member? j "y" with
        | some "P-256", some x, some y =>
            if x.size == 32 && y.size == 32 then some (.ec x y) else none
        | _, _, _ => none
    | some "OKP" =>
        match j.getString? "crv", member? j "x" with
        | some "X25519", some x => if x.size == 32 then some (.x25519 x) else none
        | _, _ => none
    | _ => none

/-- The `epk` header member a sender writes. The only key rendering in the
JWE code. -/
def Epk.toJson : Epk → Json
  | .ec x y => .object [("kty", .string "EC"), ("crv", .string "P-256"),
                        ("x", .string (Base64Url.encode x)),
                        ("y", .string (Base64Url.encode y))]
  | .x25519 x => .object [("kty", .string "OKP"), ("crv", .string "X25519"),
                          ("x", .string (Base64Url.encode x))]

/-- **No private member is written with an `epk`.** -/
theorem epk_no_private_member (e : Epk) : hasPrivateMember e.toJson = false := by
  cases e <;>
    simp [Epk.toJson, hasPrivateMember, privateMemberNames, Json.field?, List.find?]

/-- An `epk` this module accepts carries no private member. -/
theorem parseEpk_no_private {j : Json} {e : Epk} (h : parseEpk? j = some e) :
    hasPrivateMember j = false := by
  unfold parseEpk? at h
  split at h
  · simp at h
  · next hn => simpa using hn

/-! ## Fixtures -/

-- RFC 7518 Appendix C, Bob's key: the private parse reads `d`, the public
-- parse reads `x` and `y`.
private def bobKey : String :=
  "{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
  "\"x\":\"weNJy2HscCSM6AEDTDg04biOvhFhyyWvOHQfeF_PxMQ\"," ++
  "\"y\":\"e8lnCO-AlStT-NJVX-crhB7QRYhiix03illJOVAOyck\"," ++
  "\"d\":\"VEmDZpDXXK8p8N0Cndsxs924q6nS1RXFASRl6BfUqdw\"}"

#guard ((parseJson? bobKey).bind parseDecKey?).isSome
#guard (match (parseJson? bobKey).bind parseEncKey? with
  | some (.ec x y) => x.size == 32 && y.size == 32
  | _ => false)
-- The same key is refused as an `epk`: it carries `d`.
#guard ((parseJson? bobKey).bind parseEpk?).isNone
-- Without `d` it is a valid `epk`, and it renders back to the same members.
#guard (match (parseJson? ("{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
    "\"x\":\"weNJy2HscCSM6AEDTDg04biOvhFhyyWvOHQfeF_PxMQ\"," ++
    "\"y\":\"e8lnCO-AlStT-NJVX-crhB7QRYhiix03illJOVAOyck\"}")).bind parseEpk? with
  | some e => (parseEpk? e.toJson) == some e
  | none => false)
-- RFC 7516 Appendix A.3 key, `oct`, 16 octets.
#guard (match (parseJson? "{\"kty\":\"oct\",\"k\":\"GawgguFyGrWKav7AX4VKUg\"}").bind parseDecKey? with
  | some (.oct k) => k.size == 16
  | _ => false)
-- An `oct` key of a length no algorithm uses is refused.
#guard ((parseJson? "{\"kty\":\"oct\",\"k\":\"AAAA\"}").bind parseDecKey?).isNone
-- A P-384 key is refused (no P-384 ECDH in this tree).
#guard ((parseJson? "{\"kty\":\"EC\",\"crv\":\"P-384\",\"d\":\"AAAA\"}").bind parseDecKey?).isNone
-- Ed25519 is a signature curve, not a key agreement curve.
#guard ((parseJson? ("{\"kty\":\"OKP\",\"crv\":\"Ed25519\"," ++
    "\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\"}")).bind parseEncKey?).isNone

end L4Factoidal.JOSE.JweKey
