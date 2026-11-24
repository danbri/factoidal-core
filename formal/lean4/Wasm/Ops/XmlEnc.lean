/-
Wasm.Ops.XmlEnc — XML Encryption 1.1 on the dispatch surface
(https://github.com/danbri/factoidal/issues/1084), over
`L4Factoidal.XML.Enc`. Every decision is in Lean; the host only answers
AES requests (`Crypto/CipherCall.lean`, design record
`docs/designissues/2026-10-27-xml-encryption-and-jwe.md`).

  xmlDecrypt({"document": xml, "keys": [jwk…], "allowCbc": bool, "octets": bool,
              "dangerouslyAndRegrettablyAcceptDh1024": bool,
              "answers": [{"request": need, "answer": {"ok": b64} | {"refused": true}}…]})
  xmlEncrypt({"document": xml, "recipient": jwk, "algorithm": "aes128-gcm" | "aes256-gcm",
              "keyTransport": "rsa-oaep-mgf1p" | "rsa-oaep-sha256", "keyWrap": "kw-aes128" | "kw-aes256",
              "content": bool, "saml": bool, "derivedKey": bool,
              "keyDerivation": "ConcatKDF" | {"algorithm": "pbkdf2", "prf": "hmac-sha1" | "hmac-sha256"
                | "hmac-sha384" | "hmac-sha512", "iterations": n, "saltLength": n},
              "random": b64, "answers": […]})
    -> {"ok":true,"document":xml,"canonical":c14n}
     | {"ok":true,"need":{"op":…,"key":b64,"iv":b64,"aad":b64,"data":b64}}
     | {"ok":false,"error":…}
  with "octets": true, the document element must be an EncryptedData of any
  or no Type, and the result is {"ok":true,"octets":b64} (its plaintext
  octets, XML Encryption 1.1 §4.4 step 3) or the same need and error forms.

`need.op` is one of `aes-gcm-encrypt`, `aes-gcm-decrypt`, `aes-kw-wrap`,
`aes-kw-unwrap`, `aes-cbc-encrypt`, `aes-cbc-decrypt`. Byte members are
RFC 4648 §4 base64 with padding. The host runs exactly that WebCrypto call,
appends `{request: <the need as returned>, answer}` to `answers` and calls
the op again with the same other members (`npm/factoidal/lib/cipher-host.mjs`,
`runWithCipher`). The op is pure, so each run makes the same requests in the
same order and gets one further. More than `CipherCall.maxRequests` answers
is an error.

Keys (`keys`, and `recipient` of `xmlEncrypt`) are JWKs (RFC 7517, RFC 7518
§6, RFC 8037): `RSA` with `n` and `d` (`e` for a recipient), `EC` with `crv`
`P-256` and `d` (`x`, `y` for a recipient), `OKP` with `crv` `X25519` and `d`
(`x` for a recipient), `oct` with `k` of 1 to 1024 octets (a key encryption
key or content key must still have the size of its algorithm; a master key
of an `xenc11:DerivedKey` may have any of these sizes). An `oct` recipient
of `xmlEncrypt` has 16 or 32 octets. `kid` is the
`ds:KeyName` the document uses for the key. A finite-field Diffie-Hellman
key (XML Encryption 1.1 `xmlenc11#dh-es`, §5.6.3) has no JWK type; here it
is `{"kty": "DH", "p", "g", "q", "x"}` (base64 of big-endian numbers). A
prime of fewer than 2048 bits is refused unless
`dangerouslyAndRegrettablyAcceptDh1024` is true; then the result has a
`warnings` member. For `xmlEncrypt`, `random` is
octets from the host's random source: the content key, the 12-octet IV,
then 20 (RSA-OAEP SHA-1), 32 (RSA-OAEP SHA-256, or the ephemeral key of a
key agreement) or 0 (a named key encryption key or a derived key) octets,
then the PBKDF2 salt (`saltLength`, default 16) when `keyDerivation` is
PBKDF2.

`keyDerivation` (XML Encryption 1.1 §5.4) is the key derivation method of an
`EC` or `OKP` recipient (key agreement) or of a derived key: Concat KDF over
SHA-256 (§5.4.1, the default) or PBKDF2 (§5.4.2; `iterations` 1 to
1,000,000, `saltLength` 8 to 64). `derivedKey: true` with an `oct` recipient
(1 to 1024 octets) writes an `xenc11:DerivedKey` (§5.4.3): the content key is
wrapped (`keyWrap`, default the content key size) under a key derived from
the recipient's `k`, and the recipient's `kid` is the `xenc11:MasterKeyName`.

`canonical` is the canonical form of the result
(`XML.Canonical.canonDocument`), so a caller can compare two documents
without XML code of its own.

`saml`: the encrypted document element is put in a `saml:EncryptedAssertion`
(SAML Core §2.3.4).

The same functions with the native cipher run in `Harness/XmlEncProbe.lean`.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.XML.Enc
import L4Factoidal.JSON.Parser

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.XML
open L4Factoidal.XML.Enc
open L4Factoidal.Crypto.CipherCall

namespace XmlEnc

/-- The longest document read, in characters. -/
def maxDocumentChars : Nat := 4194304

/-- The deepest element nesting of a document read here. -/
def maxDocDepth : Nat := 64

def b64Field? (j : Json) (k : String) : Except String ByteArray :=
  match j.getString? k with
  | none => .error s!"missing string member \"{k}\""
  | some s => match base64Decode? s with
    | some b => .ok b
    | none => .error s!"member \"{k}\" is not base64"

def b64FieldOpt (j : Json) (k : String) : Except String ByteArray :=
  match j.getString? k with
  | none => .ok ByteArray.empty
  | some s => match base64Decode? s with
    | some b => .ok b
    | none => .error s!"member \"{k}\" is not base64"

def reqJson (r : Req) : Json :=
  .object [("op", .string r.op.name), ("key", .string (base64 r.key)), ("iv", .string (base64 r.iv)),
           ("aad", .string (base64 r.aad)), ("data", .string (base64 r.data))]

def reqOf (j : Json) : Except String Req := do
  let op ← match j.getString? "op" >>= Op.ofName? with
    | some o => pure o
    | none => throw "an answer's request has no known op"
  pure { op, key := ← b64Field? j "key", iv := ← b64FieldOpt j "iv", aad := ← b64FieldOpt j "aad",
         data := ← b64FieldOpt j "data" }

def ansOf (j : Json) : Except String Ans :=
  match j.field? "refused" with
  | some (.bool true) => .ok .refused
  | _ => match j.getString? "ok" with
    | some s => match base64Decode? s with
      | some b => .ok (.ok b)
      | none => .error "an answer's ok member is not base64"
    | none => .error "an answer must be {\"ok\": base64} or {\"refused\": true}"

/-- `answers`, in order; a tail call per answer. -/
def answersLoop : List Json → List (Req × Ans) → Except String (List (Req × Ans))
  | [], acc => .ok acc.reverse
  | a :: rest, acc =>
      match a.field? "request", a.field? "answer" with
      | some rq, some an =>
          match reqOf rq, ansOf an with
          | .ok r, .ok x => answersLoop rest ((r, x) :: acc)
          | .error e, _ => .error e
          | _, .error e => .error e
      | _, _ => .error "each answer must have the members request and answer"

def answersOf (j : Json) : Except String (List (Req × Ans)) :=
  match j.field? "answers" with
  | none => .ok []
  | some (.array xs) =>
      if xs.length > maxRequests then .error s!"more than {maxRequests} answers"
      else answersLoop xs []
  | some _ => .error "answers must be an array"

/-- One private JWK into `keys`. -/
def addKey (ks : Keys) (j : Json) : Except String Keys := do
  let kid := j.getString? "kid"
  match j.getString? "kty" with
  | some "RSA" =>
      pure { ks with rsa := ks.rsa ++ [{ kid, n := ← b64Field? j "n", e := ← b64FieldOpt j "e", d := ← b64Field? j "d" }] }
  | some "EC" =>
      if j.getString? "crv" != some "P-256" then throw "an EC key must be on P-256"
      let d ← b64Field? j "d"
      if d.size != 32 then throw "a P-256 private key d must be 32 octets"
      pure { ks with ec := ks.ec ++ [{ kid, curve := .p256, d }] }
  | some "OKP" =>
      if j.getString? "crv" != some "X25519" then throw "an OKP key must be X25519"
      let d ← b64Field? j "d"
      if d.size != 32 then throw "an X25519 private key d must be 32 octets"
      pure { ks with ec := ks.ec ++ [{ kid, curve := .x25519, d }] }
  | some "oct" =>
      let k ← b64Field? j "k"
      if k.size == 0 || k.size > 1024 then throw "an oct key must be 1 to 1024 octets"
      pure { ks with sym := ks.sym ++ [{ kid, k }] }
  | some "DH" =>
      -- Not a registered JWK type (RFC 7518 has none for finite-field
      -- Diffie-Hellman): this op's own form, the members of `DhKey`.
      let p ← b64Field? j "p"
      let x ← b64Field? j "x"
      if p.size > 513 || x.size == 0 || x.size > 513 then throw "a DH key must have p and x of at most 4096 bits"
      pure { ks with dh := ks.dh ++ [{ kid, p, g := ← b64Field? j "g", q := ← b64Field? j "q", x }] }
  | _ => throw "a key must be a JWK with kty RSA, EC, OKP or oct, or a DH key"

def keysOf (j : Json) : Except String Keys :=
  match j.field? "keys" with
  | some (.array xs) => xs.foldlM addKey {}
  | some _ => .error "keys must be an array of JWKs"
  | none => .ok {}

/-- The document member, parsed with the size and nesting bounds. -/
def documentOf (j : Json) : Except String Document :=
  match j.getString? "document" with
  | none => .error "missing string member \"document\""
  | some s =>
      if s.length > maxDocumentChars then .error "the document is too large"
      else if !nestingWithin maxDocDepth s.toList 0 then .error s!"the document nests more than {maxDocDepth} levels"
      else match parseXML s with
        | .ok d => .ok d
        | .error _ => .error "the document is not well-formed XML"

/-- The `warnings` member, when there are warnings. -/
def warningsField (ws : List String) : List (String × Json) :=
  if ws.isEmpty then [] else [("warnings", .array (ws.map Json.string))]

def octetsEnvelope (r : M ByteArray) (ws : List String := []) : String :=
  match r with
  | .ok b => okWith ([("octets", .string (base64 b))] ++ warningsField ws)
  | .error (.need q) => okWith [("need", reqJson q)]
  | .error f => errJson f.message

def envelope (r : M Document) (ws : List String := []) : String :=
  match r with
  | .ok d => okWith ([("document", .string (serializeDocument d)),
                     ("canonical", .string (L4Factoidal.XML.Canonical.canonDocument d))] ++ warningsField ws)
  | .error (.need q) => okWith [("need", reqJson q)]
  | .error f => errJson f.message

/-- The warning of the `dangerouslyAndRegrettablyAcceptDh1024` opt-in. -/
def dh1024Warning : String :=
  "dangerouslyAndRegrettablyAcceptDh1024: Diffie-Hellman primes of fewer than 2048 bits were accepted for this decryption (https://github.com/danbri/factoidal/issues/1227)"

/-- `xmlDecrypt` with a given cipher and primitives (the wasm op passes the
replay cipher of `answers`; the native probe passes `nativeCipher`). -/
def decryptWith (mkCipher : List (Req × Ans) → Cipher) (prims : Prims) (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do
        let d ← documentOf j
        let ks ← keysOf j
        let answers ← answersOf j
        let allowCbc := (j.field? "allowCbc").bind Json.asBool? |>.getD false
        let octets := (j.field? "octets").bind Json.asBool? |>.getD false
        let dh1024 := (j.field? "dangerouslyAndRegrettablyAcceptDh1024").bind Json.asBool? |>.getD false
        pure (d, ks, answers, allowCbc, octets, dh1024) : Except String _) with
      | .error e => errJson e
      | .ok (d, ks, answers, allowCbc, octets, dh1024) =>
          -- The token is made here only, from the caller's explicit member
          -- (skills/lean-risk-flags §5).
          let tok := if dh1024 then some (L4Factoidal.Risk.dangerouslyAccept .dh1024Agreement) else none
          let ws := if dh1024 then [dh1024Warning] else []
          let opts : Opts := { allowCbc, maxDepth := maxDocDepth, dh1024 := tok }
          if octets then octetsEnvelope (decryptOctets (mkCipher answers) prims ks opts d) ws
          else envelope (decrypt (mkCipher answers) prims ks opts d) ws

/-- The recipient of `xmlEncrypt`, from a public JWK. -/
def recipientOf (j : Json) (keyLen : Nat) : Except String Recipient := do
  let r ← match j.field? "recipient" with
    | some r@(.object _) => pure r
    | _ => throw "missing object member \"recipient\" (a public JWK)"
  let kid := r.getString? "kid"
  let kwLen ← match j.getString? "keyWrap" with
    | none => pure keyLen
    | some "kw-aes128" => pure 16
    | some "kw-aes256" => pure 32
    | some w => throw s!"keyWrap {w} is not supported (kw-aes128, kw-aes256)"
  match r.getString? "kty" with
  | some "RSA" =>
      let sha256 ← match j.getString? "keyTransport" with
        | none | some "rsa-oaep-mgf1p" => pure false
        | some "rsa-oaep-sha256" => pure true
        | some t => throw s!"keyTransport {t} is not supported (rsa-oaep-mgf1p, rsa-oaep-sha256)"
      pure (.rsa kid (← b64Field? r "n") (← b64Field? r "e") sha256)
  | some "EC" =>
      if r.getString? "crv" != some "P-256" then throw "an EC recipient must be on P-256"
      let x ← b64Field? r "x"
      let y ← b64Field? r "y"
      if x.size != 32 || y.size != 32 then throw "a P-256 recipient needs 32-octet x and y"
      pure (.agree kid .p256 (x ++ y) kwLen)
  | some "OKP" =>
      if r.getString? "crv" != some "X25519" then throw "an OKP recipient must be X25519"
      let x ← b64Field? r "x"
      if x.size != 32 then throw "an X25519 recipient needs a 32-octet x"
      pure (.agree kid .x25519 x kwLen)
  | some "oct" =>
      let k ← b64Field? r "k"
      if (j.field? "derivedKey").bind Json.asBool? |>.getD false then
        if k.size < 1 || k.size > 1024 then throw "a derived key's master key must be 1 to 1024 octets"
        pure (.derived kid k kwLen)
      else
        if k.size != 16 && k.size != 32 then throw "an oct recipient must be 16 or 32 octets"
        pure (.kek kid k)
  | _ => throw "the recipient must be a JWK with kty RSA, EC, OKP or oct"

/-- A non-negative integer member. -/
def natField? (j : Json) (name : String) : Except String (Option Nat) :=
  match j.field? name with
  | none => pure none
  | some (.number t) => match t.toNat? with
    | some n => pure (some n)
    | none => throw s!"{name} must be a non-negative integer"
  | some _ => throw s!"{name} must be a number"

/-- The `keyDerivation` member of `xmlEncrypt` (§5.4). -/
def writeKdfOf (j : Json) : Except String WriteKdf := do
  match j.field? "keyDerivation" with
  | none | some (.string "ConcatKDF") => pure .concat
  | some k@(.object _) =>
      if k.getString? "algorithm" != some "pbkdf2" then
        throw "keyDerivation.algorithm must be \"pbkdf2\" (or keyDerivation \"ConcatKDF\")"
      let prf ← match k.getString? "prf" with
        | none | some "hmac-sha256" => pure L4Factoidal.Crypto.WebHacl.HashAlg.sha256
        | some "hmac-sha1" => pure .sha1
        | some "hmac-sha384" => pure .sha384
        | some "hmac-sha512" => pure .sha512
        | some p => throw s!"keyDerivation.prf {p} is not supported (hmac-sha1, -sha256, -sha384, -sha512)"
      let some it ← natField? k "iterations" | throw "keyDerivation.iterations is required for pbkdf2"
      let salt := (← natField? k "saltLength").getD 16
      pure (.pbkdf2 prf it salt)
  | some _ => throw "keyDerivation must be \"ConcatKDF\" or an object"

def samlNs : String := "urn:oasis:names:tc:SAML:2.0:assertion"

/-- `xmlEncrypt` with a given cipher and primitives. -/
def encryptWith (mkCipher : List (Req × Ans) → Cipher) (prims : Prims) (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do
        let d ← documentOf j
        let keyLen ← match j.getString? "algorithm" with
          | none | some "aes128-gcm" => pure 16
          | some "aes256-gcm" => pure 32
          | some a => throw s!"algorithm {a} is not supported (aes128-gcm, aes256-gcm)"
        let recipient ← recipientOf j keyLen
        let rand ← b64Field? j "random"
        let answers ← answersOf j
        let content := (j.field? "content").bind Json.asBool? |>.getD false
        let saml := (j.field? "saml").bind Json.asBool? |>.getD false
        let kdf ← writeKdfOf j
        pure (d, ({ keyLen, recipient, content, kdf } : EncryptSpec), rand, answers, saml) : Except String _) with
      | .error e => errJson e
      | .ok (d, spec, rand, answers, saml) =>
          let out := encryptDocument (mkCipher answers) prims spec rand d
          envelope (if saml then
              out.map fun d' =>
                let wrapped : Node := .element "saml:EncryptedAssertion"
                  [({ name := "xmlns:saml", value := samlNs } : Attribute)] [d'.root]
                { d' with root := wrapped }
            else out)

end XmlEnc

def xmlEncOpNames : List String := ["xmlDecrypt", "xmlEncrypt"]

/-- `xmlDecrypt(argJson)`: HACL* public-key primitives in the wasm, AES by
the host through `answers`. -/
def xmlDecrypt (argJson : String) : String := XmlEnc.decryptWith replayCipher nativePrims argJson

/-- `xmlEncrypt(argJson)`. -/
def xmlEncrypt (argJson : String) : String := XmlEnc.encryptWith replayCipher nativePrims argJson

end L4Wasm.Ops
