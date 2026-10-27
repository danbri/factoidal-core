/-
Wasm.Ops.XmlEnc — XML Encryption 1.1 on the dispatch surface
(https://github.com/danbri/factoidal/issues/1084), over
`L4Factoidal.XML.Enc`. Every decision is in Lean; the host only answers
AES requests (`Crypto/CipherCall.lean`, design record
`docs/designissues/2026-10-27-xml-encryption-and-jwe.md`).

  xmlDecrypt({"document": xml, "keys": [jwk…], "allowCbc": bool,
              "answers": [{"request": need, "answer": {"ok": b64} | {"refused": true}}…]})
  xmlEncrypt({"document": xml, "recipient": jwk, "algorithm": "aes128-gcm" | "aes256-gcm",
              "keyTransport": "rsa-oaep-mgf1p" | "rsa-oaep-sha256", "keyWrap": "kw-aes128" | "kw-aes256",
              "content": bool, "saml": bool, "random": b64, "answers": […]})
    -> {"ok":true,"document":xml,"canonical":c14n}
     | {"ok":true,"need":{"op":…,"key":b64,"iv":b64,"aad":b64,"data":b64}}
     | {"ok":false,"error":…}

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
(`x` for a recipient), `oct` with `k` of 16 or 32 octets. `kid` is the
`ds:KeyName` the document uses for the key. For `xmlEncrypt`, `random` is
octets from the host's random source: the content key, the 12-octet IV,
then 20 (RSA-OAEP SHA-1), 32 (RSA-OAEP SHA-256, or the ephemeral key of a
key agreement) or 0 (a named key encryption key) octets.

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
      if k.size != 16 && k.size != 32 then throw "an oct key must be 16 or 32 octets"
      pure { ks with sym := ks.sym ++ [{ kid, k }] }
  | _ => throw "a key must be a JWK with kty RSA, EC, OKP or oct"

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

def envelope (r : M Document) : String :=
  match r with
  | .ok d => okWith [("document", .string (serializeDocument d)),
                     ("canonical", .string (L4Factoidal.XML.Canonical.canonDocument d))]
  | .error (.need q) => okWith [("need", reqJson q)]
  | .error f => errJson f.message

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
        pure (d, ks, answers, allowCbc) : Except String _) with
      | .error e => errJson e
      | .ok (d, ks, answers, allowCbc) =>
          envelope (decrypt (mkCipher answers) prims ks { allowCbc, maxDepth := maxDocDepth } d)

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
      if k.size != 16 && k.size != 32 then throw "an oct recipient must be 16 or 32 octets"
      pure (.kek kid k)
  | _ => throw "the recipient must be a JWK with kty RSA, EC, OKP or oct"

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
        pure (d, ({ keyLen, recipient, content } : EncryptSpec), rand, answers, saml) : Except String _) with
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
