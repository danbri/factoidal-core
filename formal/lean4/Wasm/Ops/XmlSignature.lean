/- Minimal XMLDSig coverage inspection. Existing strict XML.DSig semantics,
HACL* RSA public operation, and full PKCS#1-v1.5 template verification are reused.
No signing/key generation, key discovery, external resources, or extra transforms.
The caller supplies the trusted public key. `signatureDocument` optionally copies
one existing signature onto the actual candidate tree; it does not sign it.
Trust: HACL*/FFI and the host caller's key pinning, as for SAML. The returned
canonical strings describe coverage, not user consent or certificate trust. -/
import Wasm.Ops.Support
import L4Factoidal.XML.Enc
import L4Factoidal.JOSE.Jwk
import L4Factoidal.JOSE.Pkcs1
import L4Factoidal.Crypto.RsaNative

namespace L4Wasm.Ops.XmlSignature
open L4Factoidal
open XML JSON

def profile : String := "factoidal-enveloped-rsa-sha256-v1"

/-- Equality is of canonical coverage under this profile, not business intent. -/
def coverage (valid : Bool) (actual expected : String) : Bool :=
  valid && actual == expected

theorem coverage_iff (valid : Bool) (actual expected : String) :
    coverage valid actual expected = true ↔ valid = true ∧ actual = expected := by
  simp [coverage]

private def canonicalReport (document : Document) : Option (String × String × String) := do
  let (root,parts) ← (DSig.signedParts document "ID").toOption
  let (reference,info) ← DSig.canonForms root parts
  pure (parts.refUri,reference,info)

/-- Refuse declaration markup before parsing, so a DTD is never expanded.
This adapter is narrower than DSig: no comments or CDATA either. -/
def parseBounded (text : String) : Except String Document := do
  if text.length > 65536 then throw "XML signature demo document exceeds 65536 characters"
  if (text.splitOn "<!").length > 1 then throw "declaration markup (including DTD/comments/CDATA) is refused"
  if !Enc.nestingWithin 32 text.toList 0 then throw "XML signature demo document exceeds depth 32"
  match parseXML text with
  | .error _ => throw "XML parse failed: not well-formed XML"
  | .ok d =>
    if (d.decl.map (·.version)).getD "1.0" != "1.0" then
      throw "this coverage profile accepts XML 1.0 only"
    if !DSig.plainNodes Canonical.rootScope (d.prolog ++ [d.root] ++ d.epilog) then
      throw "processing instructions and unbound prefixes are refused"
    pure d

private def optionalText (j : Json) (field : String) : Except String (Option String) :=
  match j.field? field with
  | none => .ok none
  | some (.string s) => .ok (some s)
  | some _ => .error s!"{field} must be a string"

/-- Copy through the parsed XML tree, never by host-side string replacement. -/
def withSignature (candidate fixture : Document) : Except String Document := do
  let root ← (DSig.elOf? Canonical.rootScope fixture.root).elim (.error "no fixture root") .ok
  let sig ← match root.children.filter DSig.isSignature with
    | [sig] => pure sig
    | _ => throw "fixture must have exactly one direct signature child"
  match candidate.root with
  | .element name attrs kids =>
    pure { candidate with root := .element name attrs (kids ++ [sig.node]) }
  | _ => throw "no candidate document element"

private def readInput (j : Json) : Except String (Document × ByteArray × ByteArray × Option String) := do
  match j with
  | .object fields =>
    let names := fields.map Prod.fst
    if names.eraseDups.length != names.length then throw "duplicate request fields"
    if !names.all (fun k => ["document", "publicKey", "signatureDocument", "expectedDocument"].contains k) then
      throw "unknown request field"
  | _ => throw "request must be an object"
  let text ← (j.getString? "document").elim (.error "document must be a string") .ok
  let candidate ← parseBounded text
  let document ← match ← optionalText j "signatureDocument" with
    | none => pure candidate
    | some fixture => withSignature candidate (← parseBounded fixture)
  if (Enc.serializeDocument document).length > 65536 then
    throw "combined signed document exceeds 65536 characters"
  let key ← match (j.field? "publicKey").bind JOSE.parsePublicJwk? with
    | some (.rsa n e) =>
      if ![256,384,512].contains n.size then throw "RSA key must be 2048, 3072 or 4096 bits"
      if e.isEmpty || e.size > n.size then throw "RSA public exponent size refused"
      pure (n,e)
    | _ => throw "publicKey must be a public RSA JWK without private members"
  let expected ← match ← optionalText j "expectedDocument" with
    | none => pure none
    | some s =>
      let d ← parseBounded s
      match ExcC14n.canonSubtree [] Canonical.rootScope d.root with
      | none => throw "expected document cannot be exclusively canonicalized"
      | some canonical => pure (some canonical)
  pure (document, key.1, key.2, expected)

def verify (arg : String) : String :=
  if arg.length > 262144 then errJson "XML signature request too large" else
  match (do
    let j ← match parseJson arg with
      | .error _ => throw "request must be JSON"
      | .ok j => pure j
    readInput j : Except String (Document × ByteArray × ByteArray × Option String)) with
  | .error error => errJson error
  | .ok (document,n,e,expected) =>
    let outcome := DSig.verifyEnveloped (JOSE.Pkcs1.rs256Verify Crypto.Rsa.rsaPublicOp) n e document
    let canonical := canonicalReport document
    let fields : List (String × Json) :=
      [("profile", .string profile), ("document", .string (Enc.serializeDocument document)),
       ("valid", .bool outcome.isOk),
       ("keyTrust", .string "caller-pinned demo public key; no certificate validation")]
    let fields := match expected with
      | none => fields
      | some s => fields ++ [("expectedCanonical", .string s),
          ("coversExpected", .bool (match canonical with
            | none => false
            | some (_,reference,_) => coverage outcome.isOk reference s))]
    let fields := match canonical with
      | none => fields
      | some (uri,reference,info) => fields ++
          [("referenceUri", .string uri), ("canonicalReference", .string reference),
           ("canonicalSignedInfo", .string info)]
    match outcome with
    | .ok _ => okWith fields
    | .error error => okWith (fields ++ [("verificationError", .string error)])

#guard (parseBounded "<!DOCTYPE a [<!ENTITY e 'x'>]><a/>").isOk == false
#guard (parseBounded "<a/>").isOk == true
#guard (parseBounded "<?xml version=\"1.1\"?><a/>").isOk == false
#print axioms coverage_iff
end L4Wasm.Ops.XmlSignature

namespace L4Wasm.Ops
def xmlSignatureVerify := XmlSignature.verify
end L4Wasm.Ops
