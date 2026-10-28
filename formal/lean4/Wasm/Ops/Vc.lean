/-
Wasm.Ops.Vc — the Verifiable Credentials and DID operations.

Envelopes match `bin/npm-entry/entry_extras.ml` (`vc_*`, `did_key_resolve`)
op for op, so the same JavaScript argument drives either engine
(https://github.com/danbri/factoidal/issues/713 stage 2, and
https://github.com/danbri/factoidal/issues/578 gap 1):

  vcSha256Hex(message)                       -> {"ok":true,"sha256":"<64 hex>"}
  vcEd25519SecretToPublic(skHex)             -> {"ok":true,"publicKeyHex":"<64 hex>"}
  vcEd25519Sign(skHex, msgHex)               -> {"ok":true,"signatureHex":"<128 hex>"}
  vcEd25519Verify(pkHex, msgHex, sigHex)     -> {"ok":true,"valid":true|false}
  vcEddsaCreateFromCanonical(skHex, doc, cfg)
                                             -> {"ok":true,"proofValue":"z…"}
  vcEddsaVerifyFromCanonical(pkHex, doc, cfg, proofValue)
                                             -> {"ok":true,"verified":true|false}
  vcCheckCredential(v2ctxJson, credentialJson)
  vcCheckCredentialSubject(credentialJson)
  vcCheckNoDataLoss(credentialJson)
  vcCheckRelatedResourceDigests(registryJson, credentialJson)
                                             -> {"ok":true,"valid":true}
                                              | {"ok":true,"valid":false,"reason":"…"}
  didKeyResolve(did)                         -> {"ok":true,"did":"…","nquads":"…"}

The Data Integrity cryptosuites of `L4Factoidal/VC/Cryptosuite.lean`
(eddsa-rdfc-2022, ecdsa-rdfc-2019, ecdsa-jcs-2019), at the document level:

  vcDiKey(curve, skHex)                      -> {"ok":true,"publicKeyMultibase":"z…",
                                                 "verificationMethod":"did:key:z…#z…"}
  vcDiSecure(cryptosuite, curve, skHex, nonceHex, proofPurpose, created,
             contextsJson, documentJson)     -> {"ok":true,"document":{…}}
  vcDiVerify(expectedPurpose, contextsJson, documentJson)
                                             -> {"ok":true,"verified":true}
                                              | {"ok":true,"verified":false,"reason":"…"}

`curve` is `Ed25519`, `P-256` or `P-384`. `nonceHex` is the ECDSA nonce
(32 bytes for P-256) that the host drew from its random source; Ed25519
ignores it. `contextsJson` is a JSON object from context IRI to the text
of the context document (the host reads `third_party/contexts/`); RDFC
needs it, JCS does not. P-384 is refused on every target:
https://github.com/danbri/factoidal/issues/1166.

Key, message and signature arguments are lowercase hexadecimal, as in the
F* entry. A key or signature that is malformed, or of the wrong length, is
an error envelope for `SecretToPublic` and `Sign`, and `false` for the two
verifiers: a verifier never answers `true` on input it cannot check.

## Trust

The three Ed25519 operations go through `L4Factoidal.Crypto.Ed25519`, the
`@[extern]` binding of vendored HACL* (`formal/lean4/ffi/hacl_ed25519.c`,
trust statement in that module's header). Nothing in this file computes a
signature. SHA-256 is the pure Lean `Crypto.hashHex`, which
`skills/crypto-policy/SKILL.md` permits for hashes over public data; the
FIPS 180-4 vectors are build-time `#guard`s in `Crypto/SHA2Tests.lean`.
The signing and verifying primitives are PASSED to the
`VC/DataIntegrity.lean` functions as arguments, exactly as that module
requires.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Crypto.Ed25519
import L4Factoidal.VC.CryptosuiteNative
import L4Factoidal.Crypto.SHA2
import L4Factoidal.VC.DataIntegrity
import L4Factoidal.VC.DidKey
import L4Factoidal.VC.Credential
import L4Factoidal.Syntax.NTriples
import L4Factoidal.JSON.Parser

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Crypto
open L4Factoidal.VC.Multibase (ofByteArray toByteArray byteArrayOfHex? hexOfByteArray)

/-! ## Crypto -/

def vcSha256Hex (message : String) : String :=
  okWith [("sha256", .string (hashHex .sha256 message))]

def vcEd25519SecretToPublic (skHex : String) : String :=
  let bad := errJson "vcEd25519SecretToPublic: malformed secret key (need 32-byte hex)"
  match byteArrayOfHex? skHex with
  | none => bad
  | some sk =>
      let pk := Ed25519.secretToPublic sk
      if pk.size == 0 then bad
      else okWith [("publicKeyHex", .string (hexOfByteArray pk))]

def vcEd25519Sign (skHex msgHex : String) : String :=
  let bad := errJson "vcEd25519Sign: malformed input (need 32-byte hex key + hex message)"
  match byteArrayOfHex? skHex, byteArrayOfHex? msgHex with
  | some sk, some msg =>
      let sg := Ed25519.sign sk msg
      if sg.size == 0 then bad
      else okWith [("signatureHex", .string (hexOfByteArray sg))]
  | _, _ => bad

def vcEd25519Verify (pkHex msgHex sigHex : String) : String :=
  let valid : Bool :=
    match byteArrayOfHex? pkHex, byteArrayOfHex? msgHex, byteArrayOfHex? sigHex with
    | some pk, some msg, some sg => Ed25519.verify pk msg sg
    | _, _, _ => false
  okWith [("valid", .bool valid)]

def vcEddsaCreateFromCanonical (skHex canonicalDoc canonicalConfig : String) : String :=
  let bad := errJson
    "vcEddsaCreateFromCanonical: could not create proof (malformed key or encoding)"
  match byteArrayOfHex? skHex with
  | none => bad
  | some sk =>
      match L4Factoidal.VC.DataIntegrity.createFromCanonical Ed25519.sign .sha256 sk
              canonicalDoc canonicalConfig with
      | none => bad
      | some pv => okWith [("proofValue", .string pv)]

def vcEddsaVerifyFromCanonical (pkHex canonicalDoc canonicalConfig proofValue : String) :
    String :=
  let verified : Bool :=
    match byteArrayOfHex? pkHex with
    | none => false
    | some pk =>
        L4Factoidal.VC.DataIntegrity.verifyFromCanonical Ed25519.verify .sha256 pk
          canonicalDoc canonicalConfig proofValue
  okWith [("verified", .bool verified)]

/-! ## Data Integrity cryptosuites -/

open L4Factoidal.VC.Cryptosuite in
def curveOfName? : String → Option Curve
  | "Ed25519" => some .ed25519
  | "P-256" => some .p256
  | "P-384" => some .p384
  | _ => none

private def contextsLoader (contextsJson : String) : Option L4Factoidal.JSONLD.Loader :=
  match parseJson? contextsJson with
  | some (.object fs) =>
      some (L4Factoidal.VC.Context.vcLoader
        (fs.filterMap (fun (k, v) => match v with | .string b => some (k, b) | _ => none)))
  | _ => none

open L4Factoidal.VC.Cryptosuite in
def vcDiKey (curveName skHex : String) : String :=
  match curveOfName? curveName, byteArrayOfHex? skHex with
  | some c, some sk =>
      match L4Factoidal.VC.Cryptosuite.diSigner c sk ByteArray.empty with
      | some sg =>
          let mb := (sg.verificationMethod.splitOn "#").getLastD ""
          okWith [("publicKeyMultibase", .string mb), ("verificationMethod", .string sg.verificationMethod)]
      | none => errJson s!"vcDiKey: no {curveName} signer for this key on this target"
  | none, _ => errJson s!"vcDiKey: unknown curve {curveName} (Ed25519, P-256, P-384)"
  | _, none => errJson "vcDiKey: the secret key is not hexadecimal"

open L4Factoidal.VC.Cryptosuite in
def vcDiSecure (suiteName curveName skHex nonceHex proofPurpose created contextsJson documentJson : String) :
    String :=
  match Suite.ofName? suiteName, curveOfName? curveName, byteArrayOfHex? skHex,
      byteArrayOfHex? nonceHex, contextsLoader contextsJson, parseJson? documentJson with
  | none, _, _, _, _, _ => errJson s!"vcDiSecure: unknown cryptosuite {suiteName}"
  | _, none, _, _, _, _ => errJson s!"vcDiSecure: unknown curve {curveName}"
  | _, _, none, _, _, _ | _, _, _, none, _, _ => errJson "vcDiSecure: key or nonce is not hexadecimal"
  | _, _, _, _, none, _ => errJson "vcDiSecure: contexts must be a JSON object of IRI to text"
  | _, _, _, _, _, none => errJson "vcDiSecure: the document is not JSON"
  | some suite, some c, some sk, some nonce, some loader, some doc =>
      if c == .p384 then errJson (SuiteError.curveUnavailable "P-384").describe
      else match L4Factoidal.VC.Cryptosuite.diSigner c sk nonce with
        | none => errJson s!"vcDiSecure: no {curveName} signer for this key"
        | some sg =>
            match secureDocument loader sg suite proofPurpose created doc with
            | .error e => errJson s!"vcDiSecure: {e}"
            | .ok out => okWith [("document", out)]

open L4Factoidal.VC.Cryptosuite in
def vcDiVerify (expectedPurpose contextsJson documentJson : String) : String :=
  match contextsLoader contextsJson, parseJson? documentJson with
  | none, _ => errJson "vcDiVerify: contexts must be a JSON object of IRI to text"
  | _, none => errJson "vcDiVerify: the document is not JSON"
  | some loader, some doc =>
      match verifyDocument loader L4Factoidal.VC.Cryptosuite.diPrimitives doc expectedPurpose with
      | .ok () => okWith [("verified", .bool true)]
      | .error e => okWith [("verified", .bool false), ("reason", .string e.describe)]

/-! ## did:key -/

def didKeyResolve (did : String) : String :=
  match L4Factoidal.VC.DidKey.didKeyDocument did with
  | none =>
      errJson ("didKeyResolve: not a resolvable did:key (Ed25519 z6Mk... only): " ++ did)
  | some triples =>
      match L4Factoidal.Syntax.Graph.toNTriples triples with
      | .error e => errJson s!"didKeyResolve: {e}"
      | .ok nt => okWith [("did", .string did), ("nquads", .string nt)]

/-! ## Credential checks

The four judgments live in `L4Factoidal/VC/Credential.lean`, namespace `Doc`.
This module only maps a `Verdict` onto the envelope. -/

private def verdictEnvelope : L4Factoidal.VC.Verdict → String
  | .pass => okWith [("valid", .bool true)]
  | .fail reason => okWith [("valid", .bool false), ("reason", .string reason)]

/-- `v2ctxJson` is the text of the vendored VCDM 2.0 base context
(`third_party/contexts/credentials-v2.jsonld`); an unparseable one is an error
envelope, as in the F* entry. -/
def vcCheckCredential (v2ctxJson credentialJson : String) : String :=
  match parseJson? v2ctxJson with
  | none => errJson "vcCheckCredential (v2ctx): invalid JSON"
  | some ctx => verdictEnvelope (L4Factoidal.VC.Doc.checkFromString ctx credentialJson)

def vcCheckCredentialSubject (credentialJson : String) : String :=
  verdictEnvelope (L4Factoidal.VC.Doc.checkCredentialSubjectFromString credentialJson)

def vcCheckNoDataLoss (credentialJson : String) : String :=
  verdictEnvelope (L4Factoidal.VC.Doc.checkNoDataLossFromString credentialJson)

def vcCheckRelatedResourceDigests (registryJson credentialJson : String) : String :=
  verdictEnvelope
    (L4Factoidal.VC.Doc.checkRelatedResourceDigestsFromString registryJson credentialJson)

/-! ## Dispatch -/

/-- The op names this module serves. -/
def vcOpNames : List String :=
  [ "vcSha256Hex", "vcEd25519SecretToPublic", "vcEd25519Sign", "vcEd25519Verify"
  , "vcEddsaCreateFromCanonical", "vcEddsaVerifyFromCanonical"
  , "vcCheckCredential", "vcCheckCredentialSubject", "vcCheckNoDataLoss"
  , "vcCheckRelatedResourceDigests", "didKeyResolve", "vcDiKey", "vcDiSecure", "vcDiVerify" ]

private def arityError (op : String) (n got : Nat) : String :=
  errJson s!"{op} expects {n} argument{if n == 1 then "" else "s"}, got {got}"

/-- Serve one of `vcOpNames`, or `none` for any other op. -/
def callVc (op : String) (args : List String) : Option String :=
  match op, args with
  | "vcSha256Hex", [a]                     => some (vcSha256Hex a)
  | "vcEd25519SecretToPublic", [a]         => some (vcEd25519SecretToPublic a)
  | "vcEd25519Sign", [a, b]                => some (vcEd25519Sign a b)
  | "vcEd25519Verify", [a, b, c]           => some (vcEd25519Verify a b c)
  | "vcEddsaCreateFromCanonical", [a, b, c] => some (vcEddsaCreateFromCanonical a b c)
  | "vcEddsaVerifyFromCanonical", [a, b, c, d] =>
      some (vcEddsaVerifyFromCanonical a b c d)
  | "vcCheckCredential", [a, b]            => some (vcCheckCredential a b)
  | "vcCheckCredentialSubject", [a]        => some (vcCheckCredentialSubject a)
  | "vcCheckNoDataLoss", [a]               => some (vcCheckNoDataLoss a)
  | "vcCheckRelatedResourceDigests", [a, b] => some (vcCheckRelatedResourceDigests a b)
  | "didKeyResolve", [a]                   => some (didKeyResolve a)
  | "vcDiKey", [a, b]                      => some (vcDiKey a b)
  | "vcDiSecure", [a, b, c, d, e, f, g, h] => some (vcDiSecure a b c d e f g h)
  | "vcDiVerify", [a, b, c]                => some (vcDiVerify a b c)
  | "vcDiKey", _ => some (arityError op 2 args.length)
  | "vcDiSecure", _ => some (arityError op 8 args.length)
  | "vcDiVerify", _ => some (arityError op 3 args.length)
  | "vcSha256Hex", _ | "vcEd25519SecretToPublic", _ | "didKeyResolve", _
  | "vcCheckCredentialSubject", _ | "vcCheckNoDataLoss", _ =>
      some (arityError op 1 args.length)
  | "vcEd25519Sign", _ | "vcCheckCredential", _ | "vcCheckRelatedResourceDigests", _ =>
      some (arityError op 2 args.length)
  | "vcEd25519Verify", _ | "vcEddsaCreateFromCanonical", _ =>
      some (arityError op 3 args.length)
  | "vcEddsaVerifyFromCanonical", _ => some (arityError op 4 args.length)
  | _, _ => none

end L4Wasm.Ops
