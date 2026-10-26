/-
L4Factoidal.Authz.Keys — the signing keys of the authorization server
component (https://github.com/danbri/factoidal/issues/916). Design record:
`docs/designissues/2026-10-22-authorization-server.md`.

The keys sign RFC 9068 access tokens (lws10-core, "Authorization",
"Token Exchange", "Response": "The resulting access token MUST conform to
the JSON Web Token Profile for OAuth 2.0 Access Tokens [RFC9068]") and are
published as an RFC 7517 JWK Set at the metadata's `jwks_uri`
(RFC 8414 §2). lws10-core "Token Validation by a Storage Server": "Storage
servers SHOULD cache these keys and MUST support key rotation": a rotated
key stays published until every token it signed has expired.

## Crypto

No signature code here (`skills/crypto-policy`). `Crypto` is a record of
the primitives; `hacl` is the vendored HACL\* code
(`Crypto/P256Native.lean`, `Crypto/Ed25519.lean`, `JOSE/Pkcs1.lean` over
`Crypto/RsaNative.lean`). The theorems of `Authz/Theorems.lean` hold for
every `Crypto`; the `#guard`s of `Authz/Tests.lean` use a stub (an extern
cannot run in the interpreter).

Private key material comes from the host's random source (32 bytes, checked
by HACL\*: a P-256 key outside `[1, n-1]` is refused and the next candidate
is tried). The `kid` is the RFC 7638 thumbprint of the public key.
-/
import L4Factoidal.JOSE.Jws
import L4Factoidal.JOSE.Jwk
import L4Factoidal.JOSE.Pkcs1
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.Crypto.P256Native
import L4Factoidal.Crypto.Ed25519
import L4Factoidal.Crypto.RsaNative
import L4Factoidal.Crypto.SHA2
import L4Factoidal.JSON.Serialize
import L4Factoidal.JSON.Parser

namespace L4Factoidal.Authz

open L4Factoidal.JSON
open L4Factoidal.JOSE

/-! ## The primitives -/

/-- The signature primitives, supplied by the caller. -/
structure Crypto where
  /-- The JWS verifiers (`JOSE.Verifiers`). -/
  verifiers : Verifiers
  /-- ES256: private key, message, 32-byte nonce → 64-byte `r || s`. -/
  es256Sign : ByteArray → ByteArray → ByteArray → Option ByteArray
  /-- P-256: private key → raw `x || y`. -/
  es256Public : ByteArray → Option ByteArray
  /-- Ed25519: private key, message → 64-byte signature. -/
  eddsaSign : ByteArray → ByteArray → ByteArray
  /-- Ed25519: private key → 32-byte public key. -/
  eddsaPublic : ByteArray → Option ByteArray
  /-- P-256: 33-byte SEC 1 compressed point → raw `x || y`. -/
  p256Decompress : ByteArray → Option ByteArray

/-- The vendored HACL\* code. -/
def hacl : Crypto :=
  { verifiers :=
      { es256 := fun pubXY msg sig => L4Factoidal.Crypto.P256.p256VerifySha256 pubXY msg sig
        rs256 := fun n e sig msg =>
          L4Factoidal.JOSE.Pkcs1.rs256Verify L4Factoidal.Crypto.Rsa.rsaPublicOp n e sig msg
        eddsa := fun pk msg sig => L4Factoidal.Crypto.Ed25519.verify pk msg sig }
    es256Sign := fun sk msg nonce => L4Factoidal.Crypto.P256.p256SignSha256 sk msg nonce
    es256Public := fun sk => L4Factoidal.Crypto.P256.p256SecretToPublic sk
    eddsaSign := fun sk msg => L4Factoidal.Crypto.Ed25519.sign sk msg
    eddsaPublic := fun sk =>
      if sk.size == 32 then
        let p := L4Factoidal.Crypto.Ed25519.secretToPublic sk
        if p.size == 32 then some p else none
      else none
    p256Decompress := fun pk => L4Factoidal.Crypto.P256.p256CompressedToRaw pk }

/-! ## Keys -/

/-- The signing algorithm of a key: RFC 7518 §3.4 ES256 (the default) or
RFC 8037 EdDSA with Ed25519. -/
inductive SigAlg where
  | es256
  | eddsa
  deriving Repr, BEq, DecidableEq, Inhabited

def SigAlg.name : SigAlg → String
  | .es256 => "ES256"
  | .eddsa => "EdDSA"

def SigAlg.ofString? : String → Option SigAlg
  | "ES256" => some .es256
  | "EdDSA" => some .eddsa
  | _ => none

/-- One signing key. `retired` is when it stopped signing; it stays
published until `retired + grace` (`published`). -/
structure KeyRec where
  kid : String
  alg : SigAlg
  secret : ByteArray
  pub : ByteArray
  created : Nat
  retired : Option Nat := none
  deriving Inhabited

/-- The public JWK of a key. -/
def publicJwkOf (alg : SigAlg) (pub : ByteArray) : Jwk :=
  match alg with
  | .es256 => .ec (pub.extract 0 32) (pub.extract 32 64)
  | .eddsa => .okp pub

def KeyRec.jwk (k : KeyRec) : Jwk := publicJwkOf k.alg k.pub

/-- A key from a private key: the public key by the primitive, the `kid`
by RFC 7638. `none` when the primitive refuses the private key. -/
def mkKey (C : Crypto) (alg : SigAlg) (secret : ByteArray) (now : Nat) : Option KeyRec :=
  let pub? := match alg with
    | .es256 => C.es256Public secret
    | .eddsa => C.eddsaPublic secret
  pub?.map fun pub =>
    { kid := thumbprint (publicJwkOf alg pub), alg, secret, pub, created := now }

/-- The first candidate the primitive accepts. -/
def mkKeyFirst (C : Crypto) (alg : SigAlg) (now : Nat) : List ByteArray → Option KeyRec
  | [] => none
  | c :: cs => match mkKey C alg c now with
    | some k => some k
    | none => mkKeyFirst C alg now cs

/-- The members of a public JWK (RFC 7517 §4, RFC 7518 §6.2.1, RFC 8037 §2),
with `kid`, `alg` and `use`. Never a private member (`jwks_no_private_member`). -/
def publicJson (k : KeyRec) : Json :=
  match k.alg with
  | .es256 =>
      .object [ ("kty", .string "EC"), ("crv", .string "P-256")
              , ("x", .string (Base64Url.encode (k.pub.extract 0 32)))
              , ("y", .string (Base64Url.encode (k.pub.extract 32 64)))
              , ("kid", .string k.kid), ("alg", .string "ES256"), ("use", .string "sig") ]
  | .eddsa =>
      .object [ ("kty", .string "OKP"), ("crv", .string "Ed25519")
              , ("x", .string (Base64Url.encode k.pub))
              , ("kid", .string k.kid), ("alg", .string "EdDSA"), ("use", .string "sig") ]

/-- The private JWK (with `d`, RFC 7518 §6.2.2.1, RFC 8037 §2). Only for the
test harness export (`authzKeys` with `private`), never served. -/
def privateJson (k : KeyRec) : Json :=
  match publicJson k with
  | .object fs => .object (fs ++ [("d", .string (Base64Url.encode k.secret))])
  | j => j

/-! ## The key store -/

/-- The keys, newest first. The current signing key is the first that is
not retired. -/
structure KeyStore where
  keys : List KeyRec := []

def KeyStore.current? (s : KeyStore) : Option KeyRec :=
  s.keys.find? (fun k => k.retired.isNone)

/-- Is a key still published at `now`? A retired key stays until
`retired + grace`, `grace` being the token lifetime plus the leeway, so a
token it signed can still be validated. -/
def stillPublished (now grace : Nat) (k : KeyRec) : Bool :=
  match k.retired with
  | none => true
  | some r => decide (now < r + grace)

def published (s : KeyStore) (now grace : Nat) : List KeyRec :=
  s.keys.filter (stillPublished now grace)

/-- The JWK Set document (RFC 7517 §5). -/
def jwksJson (s : KeyStore) (now grace : Nat) : Json :=
  .object [("keys", .array ((published s now grace).map publicJson))]

def jwksText (s : KeyStore) (now grace : Nat) : String :=
  toStringCompact (jwksJson s now grace)

/-- Rotate: `k` becomes the current key; the previous current key is retired
at `now`; keys past their grace are dropped. -/
def rotateWith (s : KeyStore) (k : KeyRec) (now grace : Nat) : KeyStore :=
  let old := s.keys.map (fun x => if x.retired.isNone then { x with retired := some now } else x)
  { keys := k :: old.filter (stillPublished now grace) }

/-- Does the store need a new key at `now`? With no current key, always;
with `rotateAfter = 0`, never otherwise. -/
def needsRotation (s : KeyStore) (now rotateAfter : Nat) : Bool :=
  match s.current? with
  | none => true
  | some k => rotateAfter != 0 && decide (k.created + rotateAfter ≤ now)

/-! ## The key file -/

def keysFormat : String := "factoidal-authz-keys-1"

/-- The key file document: format, then each key's `kid`, `alg`, private key
`d` (base64url), `created` and `retired`. The public key is not stored: it is
recomputed when the file is read, so the two cannot disagree. -/
def keysDoc (s : KeyStore) : Json :=
  .object [ ("format", .string keysFormat)
          , ("keys", .array (s.keys.map fun k => .object
              ([ ("kid", .string k.kid), ("alg", .string k.alg.name)
               , ("d", .string (Base64Url.encode k.secret))
               , ("created", .number (toString k.created)) ] ++
               (match k.retired with
                | none => []
                | some r => [("retired", .number (toString r))])))) ]

private def natField? (j : Json) (n : String) : Option Nat :=
  match j.field? n with
  | some (.number s) => s.toNat?
  | _ => none

/-- Read the key file. Each key is rebuilt with the primitive; a key whose
stored `kid` differs from its recomputed thumbprint is refused. -/
def keyStoreOfDoc (C : Crypto) (j : Json) : Except String KeyStore := do
  if j.getString? "format" != some keysFormat then
    throw s!"authz keys: the key file is not format {keysFormat}"
  let items := (j.getArray? "keys").getD []
  let keys ← items.mapM fun it => do
    let alg ← ((it.getString? "alg").bind SigAlg.ofString?).elim
      (.error "authz keys: a key has no supported alg") .ok
    let d ← ((it.getString? "d").bind Base64Url.decode).elim
      (.error "authz keys: a key has no private key d") .ok
    let created := (natField? it "created").getD 0
    let k ← (mkKey C alg d created).elim (.error "authz keys: a private key is refused by the primitive") .ok
    if it.getString? "kid" != some k.kid then
      throw "authz keys: a stored kid is not the thumbprint of its key"
    pure { k with retired := natField? it "retired" }
  pure { keys }

end L4Factoidal.Authz
