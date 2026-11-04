/-
Wasm.Ops.XmlDsig — XML Signature 1.1 (W3C Recommendation 11 April 2013) on
the dispatch surface (https://github.com/danbri/factoidal/issues/1165, track
B, item 4), over `L4Factoidal.XML.DSig11` (core validation, §3.2) and
`L4Factoidal.XML.DSig11Sign` (generation, §3.1), with the HACL* backend and
signers of `L4Factoidal.XML.DSig11Native`. Every decision is in Lean; the
host gives only the arguments (and, for an ECDSA signature, 32 random
octets).

  xmlVerify({"document": xml,
             "key": jwk?, "hmacKey": b64?, "keyFromKeyInfo": bool?,
             "certificates": [b64 DER…]?, "documents": {uri: b64…}?})
    -> {"ok":true,"valid":true,"signedInfo":c14n,
        "references":[{"uri":u,"octets":b64}…],"key":jwk|null,"certificate":b64|null}
     | {"ok":true,"valid":false,"reason":text}
     | {"ok":false,"error":text}        (the arguments are wrong)

  xmlSign({"document": xml, "key": private jwk,
           "signatureMethod": uri?, "canonicalizationMethod": uri?,
           "inclusivePrefixes": [prefix…]?,
           "references": [{"uri": u, "transforms": [uri…]?, "digestMethod": uri?}…]?,
           "enveloping": {"id": id, "content": xml}?,
           "keyValue": bool?, "random": b64?})
    -> {"ok":true,"document":xml} | {"ok":false,"error":text}

Keys are JWKs (RFC 7517, RFC 7518 §6). `xmlVerify`: a public `RSA` key
(`n`, `e`) or an `EC` key (`crv` `P-256`, `P-384` or `P-521`, `x`, `y`);
with no `key`, the key of `ds:KeyInfo` is read unless `keyFromKeyInfo` is
false. A key read from `ds:KeyInfo` only says that the signature verifies
under that key: the op returns it (`key`) and the certificate that
`ds:X509Data` or `ds:RetrievalMethod` names (`certificate`), and the caller
decides whether it trusts them (path validation is the caller's).
`documents` are the octets of URIs that are not same-document references;
the engine fetches nothing.

`xmlSign`: a private `RSA` key (`n`, `e`, `d`; 2048, 3072 or 4096 bits), an
`EC` key on `P-256` (`d`), or an `oct` key (`k`) for HMAC. The key becomes a
`Signer` only in `DSig11Native` (`rsaSigner`, `p256Signer`) or
`DSig11Sign.hmacSigner`, the custodians: the op gives it to them and keeps
no copy. `signatureMethod` defaults to rsa-sha256, ecdsa-sha256 or
hmac-sha256 by the key; a method of another key kind is refused. The
default reference is `URI=""` with the enveloped-signature transform and the
canonicalization method; with `enveloping`, the signature is the document
and the default reference is `#id`. `random`: 32 octets from the host's
random source, the ECDSA nonce; it is required for an EC key. Every
returned document has passed core validation (`DSig11Sign.sign`'s
self-check; `dsig11_sign_validates`).

The same functions with the same backend run in `Harness/XmlDsigRun.lean`.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Wasm.Ops.Support
import L4Factoidal.XML.DSig11Native
import L4Factoidal.JSON.Parser

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.XML
open L4Factoidal.XML.C14n
open L4Factoidal.XML.DSig11

namespace XmlDsig

/-- The longest document read, in characters. -/
def maxDocumentChars : Nat := 4194304

/-- The deepest element nesting of a document read here. -/
def maxDocDepth : Nat := 64

/-- The most `certificates`, `documents` or `references` read. -/
def maxItems : Nat := 64

def b64 (b : ByteArray) : String := L4Factoidal.XML.Enc.base64 b

def b64Field? (j : Json) (k : String) : Except String ByteArray :=
  match j.getString? k with
  | none => .error s!"missing string member \"{k}\""
  | some s => match L4Factoidal.XML.Enc.base64Decode? s with
    | some b => .ok b
    | none => .error s!"member \"{k}\" is not base64"

/-- The `document` member, with the size and nesting bounds. -/
def documentText (j : Json) : Except String String :=
  match j.getString? "document" with
  | none => .error "missing string member \"document\""
  | some s =>
      if s.length > maxDocumentChars then .error "the document is too large"
      else if !L4Factoidal.XML.Enc.nestingWithin maxDocDepth s.toList 0 then
        .error s!"the document nests more than {maxDocDepth} levels"
      else .ok s

def curveOf (crv : Option String) : Except String Curve :=
  match crv with
  | some "P-256" => .ok .p256
  | some "P-384" => .ok .p384
  | some "P-521" => .ok .p521
  | _ => .error "an EC key must be on P-256, P-384 or P-521"

/-- A public JWK as a `PublicKey`. -/
def publicKeyOf (j : Json) : Except String PublicKey :=
  match j.getString? "kty" with
  | some "RSA" => do
      let n ← b64Field? j "n"
      let e ← b64Field? j "e"
      pure (.rsa (stripZeros n) (stripZeros e))
  | some "EC" => do
      let c ← curveOf (j.getString? "crv")
      let x ← b64Field? j "x"
      let y ← b64Field? j "y"
      if x.size != c.coordSize || y.size != c.coordSize then
        throw s!"the x and y of a {c.name} key must be {c.coordSize} octets"
      pure (.ec c (x ++ y))
  | _ => .error "a public key must be a JWK with kty RSA or EC"

/-- A `PublicKey` as a public JWK. -/
def keyJson : PublicKey → Json
  | .rsa n e => .object [("kty", .string "RSA"), ("n", .string (b64url n)), ("e", .string (b64url e))]
  | .ec c xy =>
      let k := c.coordSize
      .object [("kty", .string "EC"), ("crv", .string c.name),
               ("x", .string (b64url (xy.extract 0 k))), ("y", .string (b64url (xy.extract k (2 * k))))]
where
  /-- RFC 7515 §2 base64url without padding, as JWK members are written. -/
  b64url (b : ByteArray) : String :=
    String.ofList (((b64 b).toList.filter (· != '=')).map fun c =>
      if c == '+' then '-' else if c == '/' then '_' else c)

def certificatesOf (j : Json) : Except String (List ByteArray) :=
  match j.field? "certificates" with
  | none => .ok []
  | some (.array xs) =>
      if xs.length > maxItems then .error s!"more than {maxItems} certificates"
      else xs.foldlM (init := []) fun acc x => match x with
        | .string s => match L4Factoidal.XML.Enc.base64Decode? s with
          | some b => .ok (acc ++ [b])
          | none => .error "a certificate is not base64"
        | _ => .error "certificates must be an array of base64 strings"
  | some _ => .error "certificates must be an array of base64 strings"

def documentsOf (j : Json) : Except String (List (String × ByteArray)) :=
  match j.field? "documents" with
  | none => .ok []
  | some (.object kvs) =>
      if kvs.length > maxItems then .error s!"more than {maxItems} documents"
      else kvs.foldlM (init := []) fun acc (k, v) => match v with
        | .string s => match L4Factoidal.XML.Enc.base64Decode? s with
          | some b => .ok (acc ++ [(k, b)])
          | none => .error s!"documents member \"{k}\" is not base64"
        | _ => .error "documents must map URIs to base64 strings"
  | some _ => .error "documents must be an object"

/-- The `Config` of `xmlVerify`. -/
def configOf (j : Json) : Except String Config := do
  let key ← match j.field? "key" with
    | none => pure none
    | some k@(.object _) => some <$> publicKeyOf k
    | some _ => throw "key must be a JWK object"
  let hmacKey ← match j.getString? "hmacKey" with
    | none => pure none
    | some _ => some <$> b64Field? j "hmacKey"
  let keyFromKeyInfo := (j.field? "keyFromKeyInfo").bind Json.asBool? |>.getD true
  let certificates ← certificatesOf j
  let docs ← documentsOf j
  pure { key, hmacKey, keyFromKeyInfo, certificates,
         resolve := fun u => (docs.find? (·.1 == u)).map (·.2) }

/-- Core validation of the one `ds:Signature` of `src`, and the certificate
that its `ds:KeyInfo` names (`signingCertificate?`). -/
def verifyCore (be : Backend) (cfg : Config) (src : String) :
    Except String (Validated × Option L4Factoidal.X509.Cert) := do
  let cd ← C14nDoc.ofString? src
  match signatures cd with
  | [s] =>
      let sg ← parseSignature cd.doc s
      let v ← validateParsed be cfg cd sg
      match signingCertificate? cfg cd sg with
      | none => pure (v, none)
      | some (.ok c) => pure (v, some c)
      | some (.error e) => throw e
  | [] => throw "the document has no ds:Signature"
  | _ => throw "the document has more than one ds:Signature; validate one with `validate`"

def verifyWith (be : Backend) (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do pure (← documentText j, ← configOf j) : Except String _) with
      | .error e => errJson e
      | .ok (src, cfg) =>
          match verifyCore be cfg src with
          | .error r => okWith [("valid", .bool false), ("reason", .string r)]
          | .ok (v, c) =>
              okWith [("valid", .bool true), ("signedInfo", .string v.signedInfo),
                      ("references", .array (v.references.map fun (u, o) =>
                          .object [("uri", .string u), ("octets", .string (b64 o))])),
                      ("key", match v.key with | some k => keyJson k | none => .null),
                      ("certificate", match c with | some c => .string (b64 c.der) | none => .null)]

/-! ## Signing -/

inductive KeyKind where | rsa | ec | hmac
deriving DecidableEq

def algKind : SigAlg → Option KeyKind
  | .rsa _ => some .rsa | .ecdsa _ => some .ec | .hmac _ => some .hmac | .dsa _ => none

def algDigest : SigAlg → DigestAlg
  | .rsa h | .ecdsa h | .hmac h | .dsa h => h

/-- The private JWK: its kind and the custodian for the method `alg`. -/
def signerOf (k : Json) (alg? : Option String) : Except String Signer := do
  let kind ← match k.getString? "kty" with
    | some "RSA" => pure KeyKind.rsa
    | some "EC" => pure KeyKind.ec
    | some "oct" => pure KeyKind.hmac
    | _ => throw "a signing key must be a JWK with kty RSA, EC or oct"
  let alg ← match alg? with
    | none => pure (match kind with
        | .rsa => SigAlg.rsa .sha256 | .ec => .ecdsa .sha256 | .hmac => .hmac .sha256)
    | some u => match SigAlg.ofUri? u with
      | some (.dsa _) => throw "DSA is not supported (https://github.com/danbri/factoidal/issues/1224)"
      | some a => pure a
      | none => throw s!"signatureMethod {u} is not an algorithm of XML Signature 1.1 §6.3 or §6.4"
  if algKind alg != some kind then throw "the signatureMethod is not one for this kind of key"
  let h := algDigest alg
  match kind with
  | .rsa =>
      match rsaSigner h (stripZeros (← b64Field? k "n")) (stripZeros (← b64Field? k "e")) (← b64Field? k "d") with
      | some sg => pure sg
      | none => throw "the RSA key is refused (the modulus must be 2048, 3072 or 4096 bits)"
  | .ec =>
      if k.getString? "crv" != some "P-256" then
        throw "an EC signing key must be on P-256 (P-384 and P-521: https://github.com/danbri/factoidal/issues/1223)"
      let d ← b64Field? k "d"
      if d.size != 32 then throw "a P-256 private key d must be 32 octets"
      match p256Signer d h with
      | some sg => pure sg
      | none => throw "the P-256 private key is refused"
  | .hmac =>
      let key ← b64Field? k "k"
      if key.size == 0 then throw "an oct key must not be empty"
      pure (hmacSigner h key)

def methodOf (u : String) : Except String Method :=
  match Method.ofUri? u with
  | some m => .ok m
  | none => .error s!"{u} is not a canonicalization method of XML Signature 1.1 §6.5"

def transformOf (u : String) : Except String TransformSpec :=
  if u == envelopedAlg then .ok .enveloped
  else if u == base64Alg then .ok .base64
  else (methodOf u).map .c14n |>.mapError fun _ =>
    s!"transform {u} is not one xmlSign writes (enveloped-signature, base64, the canonicalization methods)"

def digestOf (u : Option String) : Except String DigestAlg :=
  match u with
  | none => .ok .sha256
  | some u => match DigestAlg.ofUri? u with
    | some h => .ok h
    | none => .error s!"digestMethod {u} is not an algorithm of XML Signature 1.1 §6.2"

def stringsOf (what : String) : Option Json → Except String (List String)
  | none => .ok []
  | some (.array xs) => xs.foldlM (init := []) fun acc x => match x with
      | .string s => .ok (acc ++ [s])
      | _ => .error s!"{what} must be an array of strings"
  | some _ => .error s!"{what} must be an array of strings"

def refOf (j : Json) : Except String RefSpec := do
  let some uri := j.getString? "uri" | throw "each reference needs a string member uri"
  let ts ← stringsOf "transforms" (j.field? "transforms")
  pure { uri, transforms := ← ts.mapM transformOf, digest := ← digestOf (j.getString? "digestMethod") }

/-- The `SignSpec` of `xmlSign`. -/
def specOf (j : Json) : Except String SignSpec := do
  let m0 ← methodOf ((j.getString? "canonicalizationMethod").getD excNs)
  let c14n := { m0 with inclusivePrefixes := ← stringsOf "inclusivePrefixes" (j.field? "inclusivePrefixes") }
  let placement ← match j.field? "enveloping" with
    | none => pure Placement.enveloped
    | some e@(.object _) =>
        match e.getString? "id", e.getString? "content" with
        | some i, some c => pure (.enveloping i c)
        | _, _ => throw "enveloping needs the string members id and content"
    | some _ => throw "enveloping must be an object"
  let refs ← match j.field? "references" with
    | none => pure (match placement with
        | .enveloped => [{ uri := "", transforms := [.enveloped, .c14n c14n] }]
        | .enveloping i _ => [{ uri := "#" ++ i, transforms := [.c14n c14n] }])
    | some (.array xs) =>
        if xs.length > maxItems then throw s!"more than {maxItems} references" else xs.mapM refOf
    | some _ => throw "references must be an array"
  let keyValue := (j.field? "keyValue").bind Json.asBool? |>.getD true
  pure { c14n, refs, placement, keyValue }

def signWith (be : Backend) (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do
        let spec ← specOf j
        let src ← match spec.placement with
          | .enveloped => documentText j
          | .enveloping .. => pure ((j.getString? "document").getD "")
        let k ← match j.field? "key" with
          | some k@(.object _) => pure k
          | _ => throw "missing object member \"key\" (a private JWK)"
        let sg ← signerOf k (j.getString? "signatureMethod")
        let rand ← match j.getString? "random" with
          | none => pure ByteArray.empty
          | some _ => b64Field? j "random"
        if algKind sg.alg == some KeyKind.ec && rand.size != 32 then
          throw "an ECDSA signature needs random: 32 octets from the host's random source"
        DSig11.sign be sg spec rand src : Except String String) with
      | .error e => errJson e
      | .ok out => okWith [("document", .string out)]

/-! ## Theorems -/

/-- XML Signature 1.1 (2013) §3.2: a signature that `xmlVerify` reports as
valid passes core validation (`DSig11.validateText`) with the same backend
and configuration, and the op reports the same `Validated` record. -/
theorem xmlVerify_2013_core {be : Backend} {cfg : Config} {src : String}
    {v : Validated} {c : Option L4Factoidal.X509.Cert} (h : verifyCore be cfg src = .ok (v, c)) :
    validateText be cfg src = .ok v := by
  unfold verifyCore at h
  unfold validateText DSig11.validate
  cases hcd : C14nDoc.ofString? src with
  | error e => simp [hcd, bind, Except.bind] at h
  | ok cd =>
      simp only [hcd, bind, Except.bind] at h ⊢
      split at h
      · rename_i s hs
        simp only [hs]
        cases hp : parseSignature cd.doc s with
        | error e => simp [hp] at h
        | ok sg =>
            simp only [hp] at h ⊢
            cases hv : validateParsed be cfg cd sg with
            | error e => simp [hv] at h
            | ok v' =>
                simp only [hv] at h ⊢
                split at h <;> simp_all [pure, Except.pure]
      · cases h
      · cases h

/-- XML Signature 1.1 (2013) §6.4: the default signature method of each key
kind is one of that kind (so a key never signs under another kind's method). -/
theorem xmlSign_2013_default_kind :
    algKind (.rsa .sha256) = some KeyKind.rsa ∧ algKind (.ecdsa .sha256) = some KeyKind.ec ∧
      algKind (.hmac .sha256) = some KeyKind.hmac := ⟨rfl, rfl, rfl⟩

/-- DSA has no key kind here: `xmlSign` never makes a DSA signature
(https://github.com/danbri/factoidal/issues/1224). -/
theorem xmlSign_2013_no_dsa (h : DigestAlg) : algKind (.dsa h) = none := rfl

end XmlDsig

def xmlDsigOpNames : List String := ["xmlVerify", "xmlSign"]

/-- `xmlVerify(argJson)`: core validation with HACL* RSA and P-256. -/
def xmlVerify (argJson : String) : String := XmlDsig.verifyWith nativeBackend argJson

/-- `xmlSign(argJson)`: signature generation by the custodians of
`DSig11Native`, checked by core validation before it is returned. -/
def xmlSign (argJson : String) : String := XmlDsig.signWith nativeBackend argJson

end L4Wasm.Ops
