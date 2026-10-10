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
import L4Factoidal.Crypto.SHA2
import L4Factoidal.VC.DataIntegrity
import L4Factoidal.VC.DidKey
import L4Factoidal.VC.Credential
import L4Factoidal.Syntax.NTriples

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

/-! ## did:key -/

def didKeyResolve (did : String) : String :=
  match L4Factoidal.VC.DidKey.didKeyDocument did with
  | none =>
      errJson ("didKeyResolve: not a resolvable did:key (Ed25519 z6Mk... only): " ++ did)
  | some triples =>
      match L4Factoidal.Syntax.Graph.toNTriples triples with
      | .error e => errJson s!"didKeyResolve: {e}"
      | .ok nt => okWith [("did", .string did), ("nquads", .string nt)]

/-! ## Dispatch -/

/-- The op names this module serves. -/
def vcOpNames : List String :=
  [ "vcSha256Hex", "vcEd25519SecretToPublic", "vcEd25519Sign", "vcEd25519Verify"
  , "vcEddsaCreateFromCanonical", "vcEddsaVerifyFromCanonical", "didKeyResolve" ]

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
  | "didKeyResolve", [a]                   => some (didKeyResolve a)
  | "vcSha256Hex", _ | "vcEd25519SecretToPublic", _ | "didKeyResolve", _ =>
      some (arityError op 1 args.length)
  | "vcEd25519Sign", _ => some (arityError op 2 args.length)
  | "vcEd25519Verify", _ | "vcEddsaCreateFromCanonical", _ =>
      some (arityError op 3 args.length)
  | "vcEddsaVerifyFromCanonical", _ => some (arityError op 4 args.length)
  | _, _ => none

end L4Wasm.Ops
