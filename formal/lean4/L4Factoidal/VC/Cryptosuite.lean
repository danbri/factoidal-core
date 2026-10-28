/-
L4Factoidal.VC.Cryptosuite — the Data Integrity cryptosuites as one table
over shared steps: `eddsa-rdfc-2022`, `ecdsa-rdfc-2019` and `ecdsa-jcs-2019`.

Specifications, by version (a later version is a new table row or a new
theorem, never a silent change of these):

  * VC DI 1.0 — Verifiable Credential Data Integrity 1.0, W3C Recommendation
    2025-05-15: §2.1 Proofs, §4.3 Add Proof, §4.4 Verify Proof.
  * VC DI ECDSA 1.0 — Data Integrity ECDSA Cryptosuites v1.0, W3C
    Recommendation 2025-05-15, section "Algorithms" (as in the editor's draft
    of w3c/vc-di-ecdsa at commit 59df72ca, 2026-09-16): the suite table
    (`ecdsa-rdfc-2019` and `ecdsa-jcs-2019`, each with P-256 and SHA-256 or
    P-384 and SHA-384), signatures in the IEEE P1363 form `r || s` (RFC 4754
    §7), proof values base58-btc Multibase, and "For P-384 keys, SHA-2 with
    384-bits of output MUST be used" as the RDFC-1.0 hash too.
  * VC DI EdDSA 1.0 — Data Integrity EdDSA Cryptosuites v1.0, W3C
    Recommendation 2025-05-15, §3.3 `eddsa-rdfc-2022`.
  * RDFC-1.0 — RDF Dataset Canonicalization, W3C Recommendation 2024-05-21
    (`RDF/Canonical.lean`).
  * RFC 8785 — JSON Canonicalization Scheme (`JSONLD.jcsDocument`).
  * CID 1.0 — Controlled Identifiers v1.0, §2.2.2 Multikey (P-256 header
    0x8024, P-384 0x8124, Ed25519 0xed01) and §3.3 Retrieve Verification
    Method (`CID/Retrieve.lean`).

## One definition, three cryptosuites

Every suite runs the same four steps, and each step is one definition here
or in `VC/DataIntegrity.lean`:

    transform  : `transform` — RDFC-1.0 (with the hash of the key's curve)
                 or RFC 8785, chosen by the suite's `Transform`
    hash       : `DataIntegrity.hashData` — H(proof config) ++ H(document)
    sign       : the `Signer` (a custodian: it holds the key, this module
                 never sees a secret key)
    serialise  : `DataIntegrity.createFromCanonical` / `verifyFromCanonical`
                 — base58-btc Multibase of the signature

A suite is a row: its name, its family (which curves it takes) and its
transform. `Theorems` below states what the sharing gives: ecdsa-rdfc-2019
with P-256 and eddsa-rdfc-2022 compute the same hash data, and verification
reads the document only through its canonical form.

## What this module does not do

  * No signature arithmetic. The signature primitives are a `Primitives`
    value and a `Signer`, passed in by the executable edge
    (`Wasm/Ops/Vc.lean`), which binds HACL* (`Crypto/Ed25519.lean`,
    `Crypto/P256Native.lean`). HACL* has no P-384: `Primitives.available`
    answers `false` for it there, and P-384 is refused with a message that
    names https://github.com/danbri/factoidal/issues/1166.
  * No proof chains (`previousProof`): refused, as in `DataIntegrity`.
  * No I/O. A controlled identifier document the verifier needs is the
    refusal `needDocument url`, as in `DataIntegrity.resolveKey`.
-/
import L4Factoidal.VC.DataIntegrity
import L4Factoidal.CID.Multiformats

namespace L4Factoidal.VC.Cryptosuite

open L4Factoidal.RDF
open L4Factoidal.Crypto
open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.VC.Multibase
open L4Factoidal.VC.Context
open L4Factoidal.VC.DataIntegrity

/-! ## The suite table -/

/-- The canonicalization a suite uses. -/
inductive Transform where
  /-- RDFC-1.0 over the JSON-LD toRdf dataset. -/
  | rdfc10
  /-- RFC 8785 over the JSON value. -/
  | jcs
  deriving Repr, DecidableEq

/-- The signature algorithm family; it fixes the curves a suite accepts. -/
inductive Family where
  | eddsa
  | ecdsa
  deriving Repr, DecidableEq

/-- The curves of the full-disclosure suites. -/
inductive Curve where
  | ed25519
  | p256
  | p384
  deriving Repr, DecidableEq

def Curve.name : Curve → String
  | .ed25519 => "Ed25519"
  | .p256 => "P-256"
  | .p384 => "P-384"

/-- The hash of a curve (VC DI ECDSA 1.0 suite table; VC DI EdDSA 1.0 §3.3.4
for Ed25519). The same hash is the RDFC-1.0 hash of the transform. -/
def Curve.hashAlg : Curve → HashAlgorithm
  | .ed25519 => .sha256
  | .p256 => .sha256
  | .p384 => .sha384

structure Suite where
  name : String
  family : Family
  transform : Transform
  deriving Repr, DecidableEq

/-- VC DI EdDSA 1.0 §3.3. -/
def eddsaRdfc2022 : Suite := ⟨"eddsa-rdfc-2022", .eddsa, .rdfc10⟩
/-- VC DI ECDSA 1.0, `ecdsa-rdfc-2019`. -/
def ecdsaRdfc2019 : Suite := ⟨"ecdsa-rdfc-2019", .ecdsa, .rdfc10⟩
/-- VC DI ECDSA 1.0, `ecdsa-jcs-2019`. -/
def ecdsaJcs2019 : Suite := ⟨"ecdsa-jcs-2019", .ecdsa, .jcs⟩

def suites : List Suite := [eddsaRdfc2022, ecdsaRdfc2019, ecdsaJcs2019]

def Suite.ofName? (n : String) : Option Suite := suites.find? (·.name == n)

/-- Does the suite take keys on this curve? -/
def Suite.accepts (s : Suite) (c : Curve) : Bool :=
  match s.family, c with
  | .eddsa, .ed25519 => true
  | .ecdsa, .p256 => true
  | .ecdsa, .p384 => true
  | _, _ => false

/-! ## Keys -/

/-- A public key: its curve and its bytes, as a Multikey holds them (Ed25519
32 bytes, P-256 33 and P-384 49 bytes SEC 1 compressed) or as a JWK gives
them (P-256 64 and P-384 96 bytes `x || y`). The primitive accepts both
forms. -/
structure PublicKey where
  curve : Curve
  key : ByteArray

instance : BEq PublicKey where
  beq a b := a.curve == b.curve && a.key.data == b.key.data

def Curve.ofKeyType? : L4Factoidal.CID.KeyType → Option Curve
  | .ed25519 => some .ed25519
  | .p256 => some .p256
  | .p384 => some .p384
  | _ => none

def Curve.keyType : Curve → L4Factoidal.CID.KeyType
  | .ed25519 => .ed25519
  | .p256 => .p256
  | .p384 => .p384

/-- A public Multikey value (CID 1.0 §2.2.2) on one of the three curves. -/
def publicKeyOfMultikey? (mb : String) : Option PublicKey :=
  match L4Factoidal.CID.decodePublicMultikey mb with
  | .ok (kt, key) => (Curve.ofKeyType? kt).map (fun c => ⟨c, toByteArray key⟩)
  | .error _ => none

/-- The key of a did:key verification method: `did:key:MB` or
`did:key:MB#MB` (the did:key method: the fragment is the same Multikey). -/
def publicKeyOfDidKey? (vm : String) : Option PublicKey :=
  if !vm.startsWith "did:key:" then none
  else
    let rest := String.ofList (vm.toList.drop 8)
    match rest.splitOn "#" with
    | [mb] => publicKeyOfMultikey? mb
    | [mb, frag] => if mb == frag then publicKeyOfMultikey? mb else none
    | _ => none

/-- The key of a JWK (RFC 7517; curves of RFC 7518 §6.2.1.1 and RFC 8037
§2): OKP Ed25519 with a 32-byte `x`, EC P-256 or P-384 with `x` and `y` of
the curve's field size. -/
def publicKeyOfJwk? (j : Json) : Option PublicKey :=
  let b64 (n : String) := (j.getString? n).bind L4Factoidal.JOSE.Base64Url.decode
  match j.getString? "kty", j.getString? "crv" with
  | some "OKP", some "Ed25519" =>
      match b64 "x" with
      | some x => if x.size == 32 then some ⟨.ed25519, x⟩ else none
      | none => none
  | some "EC", some crv =>
      let c? : Option (Curve × Nat) :=
        if crv == "P-256" then some (.p256, 32) else if crv == "P-384" then some (.p384, 48) else none
      match c?, b64 "x", b64 "y" with
      | some (c, n), some x, some y =>
          if x.size == n && y.size == n then some ⟨c, x ++ y⟩ else none
      | _, _, _ => none
  | _, _ => none

/-- The public key of a CID verification method. -/
def publicKeyOfMethod? (m : L4Factoidal.CID.Method) : Option PublicKey :=
  match m.material with
  | .multikey kt key => (Curve.ofKeyType? kt).map (fun c => ⟨c, toByteArray key⟩)
  | .jwk j => publicKeyOfJwk? j
  | _ => none

/-- The Multikey value of a public key in multikey form. -/
def multikeyOf (pk : PublicKey) : String :=
  L4Factoidal.CID.encodePublicMultikey pk.curve.keyType (ofByteArray pk.key)

/-- The did:key verification method of a public key in multikey form. -/
def didKeyVerificationMethod (pk : PublicKey) : String :=
  let mb := multikeyOf pk
  s!"did:key:{mb}#{mb}"

/-! ## Primitives and the signer -/

/-- The verifying primitives, passed in by the executable edge. -/
structure Primitives where
  /-- curve, public key (either form), message, signature → accepted? -/
  verify : Curve → ByteArray → ByteArray → ByteArray → Bool
  /-- Does this target have the curve? -/
  available : Curve → Bool

/-- A signer: the custodian of one private key
(`docs/web/hub/webdav-lws-design.md`, "One custodian per privileged
resource"). It signs a message on request and never hands out the key;
this module sees only its curve, its verification method and its answers.
`sign` answers `none` when it refuses. -/
structure Signer where
  curve : Curve
  verificationMethod : String
  sign : ByteArray → Option ByteArray

/-! ## Transform -/

/-- The canonical form of a JSON value under a transform (VC DI ECDSA 1.0 and
VC DI EdDSA 1.0, "Transformation"). `alg` is the RDFC-1.0 hash. -/
def transform (loader : Loader) (t : Transform) (alg : HashAlgorithm) (j : Json) :
    Except String String :=
  match t with
  | .rdfc10 =>
      match parseJsonLd loader (toStringCompact j) none none none none with
      | .error e => .error s!"JSON-LD toRdf failed: {e.code}"
      | .ok ds => .ok (ds.canonicalNQuads alg)
  | .jcs => .ok (jcsDocument j)

/-! ## Dataset level

The RDFC suites over datasets, as `DataIntegrity.verifyProofValue` is for
eddsa-rdfc-2022: the suite must take the key's curve, and RDFC-1.0 and the
hash data use the curve's hash. `CryptosuiteTheorems` proves that
`DataIntegrity.verifyProofValue` is this function at eddsa-rdfc-2022 and
Ed25519, and at ecdsa-rdfc-2019 and P-256. -/

def verifyDataset (prims : Primitives) (s : Suite) (pk : PublicKey)
    (document proofConfig : Dataset) (proofValue : String) : Bool :=
  s.accepts pk.curve &&
    verifyFromCanonical (prims.verify pk.curve) pk.curve.hashAlg pk.key
      (document.canonicalNQuads pk.curve.hashAlg) (proofConfig.canonicalNQuads pk.curve.hashAlg)
      proofValue

/-! ## Errors -/

inductive SuiteError where
  /-- A refusal of the shared Data Integrity steps. -/
  | di (e : VerifyError)
  | unknownCryptosuite (got : String)
  /-- The key's curve is not one this suite takes. -/
  | keyNotForSuite (vm suite : String)
  /-- No primitive for this curve on this target. -/
  | curveUnavailable (curve : String)
  /-- VC DI: a proof `@context` that the document's `@context` does not
  start with. -/
  | contextNotPrefix
  deriving Repr, DecidableEq

def SuiteError.describe : SuiteError → String
  | .di e => e.describe
  | .unknownCryptosuite got => s!"proof.cryptosuite \"{got}\" is not one of: {", ".intercalate (suites.map (·.name))}"
  | .keyNotForSuite vm s => s!"verificationMethod \"{vm}\" is not a key for {s}"
  | .curveUnavailable c =>
      s!"{c} is not available on this target (HACL* has no {c}; https://github.com/danbri/factoidal/issues/1166)"
  | .contextNotPrefix => "the document's @context does not start with the proof's @context"

/-! ## Key resolution -/

/-- The public key of `verificationMethod` for a proof with this purpose: a
did:key on one of the three curves, or CID 1.0 §3.3 over the documents the
host fetched. Same refusals as `DataIntegrity.resolveKey`, for every curve. -/
def resolvePublicKey (cidDocs : List (String × String)) (now : Option Int) (vm purpose : String) :
    Except SuiteError PublicKey :=
  match publicKeyOfDidKey? vm with
  | some pk => .ok pk
  | none =>
      if vm.startsWith "did:" then .error (.di (.unresolvableVerificationMethod vm))
      else match L4Factoidal.CID.Relationship.ofName? purpose with
        | none => .error (.di (.unknownProofPurpose purpose))
        | some rel =>
            match L4Factoidal.CID.retrieveWith cidDocs vm rel with
            | .need u => .error (.di (.needDocument u))
            | .error e => .error (.di (.cid vm e))
            | .ok m =>
                if !inForceAt now m then .error (.di (.methodNotInForce vm))
                else match publicKeyOfMethod? m with
                  | some pk => .ok pk
                  | none => .error (.di (.unresolvableVerificationMethod vm))

/-! ## Contexts -/

/-- A `@context` value as a list of entries. -/
def contextEntries : Option Json → List Json
  | some (.array items) => items
  | some .null => []
  | some j => [j]
  | none => []

/-- VC DI, Verify Proof: "Check that the securedDocument.@context starts with
all values contained in the proofOptions.@context in the same order." -/
def contextStartsWith (docCtx : Option Json) (proofCtx : Json) : Bool :=
  let d := contextEntries docCtx
  let p := contextEntries (some proofCtx)
  p.length ≤ d.length && (d.take p.length) == p

/-- The proof configuration of a proof that carries no `@context` of its own:
for RDFC the context `proofContextFor` derives (as `DataIntegrity` does, so
that a VC 1.1 document keeps the proof vocabulary); for JCS the document's
own `@context` (VC DI ECDSA 1.0, Proof Configuration: "Set
proofConfig.@context to unsecuredDocument.@context"). -/
def configOf (t : Transform) (doc proof : Json) : Json :=
  let bare := withoutField "proofValue" proof
  match t with
  | .rdfc10 => setFieldFirst "@context" (proofContextFor (doc.field? "@context")) bare
  | .jcs =>
      match doc.field? "@context" with
      | some c => setFieldFirst "@context" c bare
      | none => bare

/-- The unsecured document and the proof configuration to hash, for a proof
of a secured document (VC DI, Verify Proof steps 1–4). -/
def verifyInputs (t : Transform) (doc proof : Json) : Except SuiteError (Json × Json) :=
  let unsecured := unsecuredOf doc
  match proof.field? "@context" with
  | some pctx =>
      if contextStartsWith (doc.field? "@context") pctx then
        .ok (setFieldFirst "@context" pctx unsecured, withoutField "proofValue" proof)
      else .error .contextNotPrefix
  | none => .ok (unsecured, configOf t doc proof)

/-! ## Verify -/

/-- Verify one proof object of a secured document (VC DI 1.0 §4.4, with the
suite named by its `cryptosuite`). -/
def verifyProof (loader : Loader) (prims : Primitives) (expectedPurpose : String) (doc proof : Json)
    (cidDocs : List (String × String) := []) (now : Option Int := none) :
    Except SuiteError Unit := do
  let _ ← match fieldsOf? proof with | some fs => pure fs | none => throw (.di .proofNotObject)
  if (proof.field? "previousProof").isSome then throw (.di .proofChainUnsupported)
  let need (n : String) : Except SuiteError String :=
    match proof.getString? n with
    | some s => if s.isEmpty then throw (.di (.missingField n)) else pure s
    | none => throw (.di (.missingField n))
  let ty ← need "type"
  if ty != proofTypeName then throw (.di (.wrongType ty))
  let cs ← need "cryptosuite"
  let suite ← match Suite.ofName? cs with
    | some s => pure s
    | none => throw (.unknownCryptosuite cs)
  let vm ← need "verificationMethod"
  let purpose ← need "proofPurpose"
  if purpose != expectedPurpose then throw (.di (.wrongPurpose purpose expectedPurpose))
  let pv ← need "proofValue"
  let pk ← resolvePublicKey cidDocs now vm purpose
  if !suite.accepts pk.curve then throw (.keyNotForSuite vm suite.name)
  if !prims.available pk.curve then throw (.curveUnavailable pk.curve.name)
  let alg := pk.curve.hashAlg
  let (unsecured, cfg) ← verifyInputs suite.transform doc proof
  let canonicalDoc ← match transform loader suite.transform alg unsecured with
    | .ok s => pure s
    | .error m => throw (.di (.canonicalization "document" m))
  let canonicalCfg ← match transform loader suite.transform alg cfg with
    | .ok s => pure s
    | .error m => throw (.di (.canonicalization "proof options" m))
  if verifyFromCanonical (prims.verify pk.curve) alg pk.key canonicalDoc canonicalCfg pv then pure ()
  else throw (.di .signatureRejected)

/-- Verify a secured document: one proof object, or a proof set whose every
member verifies. -/
def verifyDocument (loader : Loader) (prims : Primitives) (doc : Json)
    (expectedPurpose : String := "assertionMethod")
    (cidDocs : List (String × String) := []) (now : Option Int := none) :
    Except SuiteError Unit := do
  let proofs ← match doc.field? "proof" with
    | none => throw (.di .noProof)
    | some (.array ps) => if ps.isEmpty then throw (.di .noProof) else pure ps
    | some p => pure [p]
  for p in proofs do
    verifyProof loader prims expectedPurpose doc p cidDocs now

/-! ## Create -/

/-- Secure a document with one proof (VC DI 1.0 §4.3; the suite's Create
Proof). For RDFC the returned document's `@context` is extended the way
`proofContextFor` extends the configuration's, and the proof carries no
`@context` (as the VC DI ECDSA 1.0 and VC DI EdDSA 1.0 vectors show); for JCS
the document is unchanged and the proof carries the configuration's
`@context` (as the `ecdsa-jcs-2019` vectors show). -/
def secureDocument (loader : Loader) (signer : Signer) (suite : Suite)
    (proofPurpose created : String) (doc : Json) : Except String Json := do
  if !suite.accepts signer.curve then
    throw s!"{suite.name} does not take a {signer.curve.name} key"
  let alg := signer.curve.hashAlg
  let unsecured := unsecuredOf doc
  let options : DiProof :=
    { cryptosuite := suite.name, verificationMethod := signer.verificationMethod,
      proofPurpose, created, proofValue := "" }
  let cfg := configOf suite.transform doc options.toJson
  let canonicalDoc ← transform loader suite.transform alg unsecured
  let canonicalCfg ← transform loader suite.transform alg cfg
  let signF : SignFn := fun _ msg => (signer.sign msg).getD ByteArray.empty
  match createFromCanonical signF alg ByteArray.empty canonicalDoc canonicalCfg with
  | none => throw "the signer refused"
  | some pv =>
    match suite.transform with
    | .rdfc10 =>
        let proof := { options with proofValue := pv }.toJson
        pure (setField "proof" proof (setFieldFirst "@context" (proofContextFor (doc.field? "@context")) unsecured))
    | .jcs =>
        pure (setField "proof" (setField "proofValue" (.string pv) cfg) unsecured)

end L4Factoidal.VC.Cryptosuite
