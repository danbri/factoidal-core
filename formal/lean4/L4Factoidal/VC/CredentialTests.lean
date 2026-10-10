/-
L4Factoidal.VC.CredentialTests — build-time checks for the VC 2.0
data-model rules, with the context-ordering rule pinned.
-/
import L4Factoidal.VC.Credential

namespace L4Factoidal.VC
open L4Factoidal.JSON

private def ctxOk : Json := .array [.string baseContext]
private def subj : Json := .object [("id", .string "did:example:s")]

private def goodVc : Json :=
  .object [("@context", ctxOk),
           ("type", .array [.string credentialType]),
           ("issuer", .string "did:example:issuer"),
           ("credentialSubject", subj)]

#guard (checkCredential goodVc).ok

-- THE CONTEXT-ORDERING RULE. The base context must be FIRST, not
-- merely present: JSON-LD context processing is order-dependent, so
-- a later entry can redefine terms an earlier one established.
-- Accepting a base context in second position would let a crafted
-- context silently redefine `issuer` or `credentialSubject`.
#guard (checkContext (.object [("@context",
          .array [.string baseContext, .string "https://ex.org/c"])])).ok
#guard !(checkContext (.object [("@context",
          .array [.string "https://ex.org/c", .string baseContext])])).ok

-- Other @context shapes.
#guard (checkContext (.object [("@context", .string baseContext)])).ok
#guard !(checkContext (.object [("@context", .string "https://ex.org/other")])).ok
#guard !(checkContext (.object [("@context", .array [])])).ok
#guard !(checkContext (.object [])).ok
-- An inline object entry is structurally fine after the base.
#guard (checkContext (.object [("@context",
          .array [.string baseContext, .object [("x", .string "y")]])])).ok
-- A non-IRI string entry is not.
#guard !(checkContext (.object [("@context",
          .array [.string baseContext, .string "not an iri"])])).ok

-- type membership, accepting the string and array forms.
#guard (checkTypeMembership (.object [("type", .string credentialType)]) credentialType).ok
#guard (checkTypeMembership (.object [("type",
          .array [.string "Other", .string credentialType])]) credentialType).ok
#guard !(checkTypeMembership (.object [("type", .array [.string "Other"])]) credentialType).ok
#guard !(checkTypeMembership (.object []) credentialType).ok

-- issuer: an IRI string or an object with an id.
#guard (checkIssuer (.object [("issuer", .string "did:example:i")])).ok
#guard (checkIssuer (.object [("issuer", .object [("id", .string "did:example:i")])])).ok
#guard !(checkIssuer (.object [("issuer", .object [])])).ok
#guard !(checkIssuer (.object [("issuer", .number "1")])).ok
#guard !(checkIssuer (.object [])).ok

-- An EMPTY credentialSubject fails: a credential asserting nothing
-- about anyone is not a credential.
#guard (checkCredentialSubject (.object [("credentialSubject", subj)])).ok
#guard !(checkCredentialSubject (.object [("credentialSubject", .object [])])).ok
#guard !(checkCredentialSubject (.object [("credentialSubject", .array [])])).ok
#guard !(checkCredentialSubject (.object [])).ok

-- Validity dates are optional but must be strings when present.
#guard (checkValidityDates (.object [])).ok
#guard (checkValidityDates (.object [("validFrom", .string "2026-01-01T00:00:00Z")])).ok
#guard !(checkValidityDates (.object [("validFrom", .number "1")])).ok

-- Verdicts carry a REASON, so a failure is actionable rather than a
-- bare false. The FIRST failure's reason survives a conjunction.
#guard match checkCredential (.object []) with
       | .fail r => r == "missing @context"
       | .pass   => false
#guard match all [.fail "first", .fail "second"] with
       | .fail r => r == "first"
       | .pass   => false

-- A presentation needs its own base type, not the credential's.
#guard (checkPresentation (.object [("@context", ctxOk),
          ("type", .array [.string presentationType])])).ok
#guard !(checkPresentation (.object [("@context", ctxOk),
          ("type", .array [.string credentialType])])).ok


/-! # `Doc` — the document-level checks

Build-time cases for `Credential.lean`'s `L4Factoidal.VC.Doc`, each stated in
both directions, so an implementation that passes (or fails) everything breaks
the build. `Harness/VcProbe.lean` scores the same functions over the vendored
`third_party/testing/vc` fixtures; the cases below are the shapes those
fixtures use, written out as text so they run in the build. -/

namespace Doc

open L4Factoidal.JSON

private def pass (s : String) : Bool :=
  match checkFromString .null s with
  | .pass => true
  | .fail _ => false

private def failsWith (s : String) (needle : String) : Bool :=
  match checkFromString .null s with
  | .pass => false
  | .fail r => (r.splitOn needle).length > 1

private def base : String := "\"@context\":[\"https://www.w3.org/ns/credentials/v2\"]"
private def vcType : String := "\"type\":[\"VerifiableCredential\"]"
private def subj : String := "\"credentialSubject\":{\"id\":\"did:example:s\"}"
private def vc (extra : String) : String :=
  "{" ++ base ++ "," ++ vcType ++ "," ++ subj ++ (if extra.isEmpty then "" else "," ++ extra) ++ "}"

-- The baseline passes, and bad JSON and a non-object top level are refused.
#guard pass (vc "")
#guard failsWith "{" "not well-formed JSON"
#guard failsWith "[]" "top-level JSON value must be an object"

-- issuer is OPTIONAL in this layer (the strict layer above requires it).
#guard pass (vc "\"issuer\":\"did:example:i\"")
#guard pass (vc "\"issuer\":{}")
#guard pass (vc "\"issuer\":{\"id\":\"did:example:i\",\"name\":\"Acme\"}")
#guard failsWith (vc "\"issuer\":\"not an iri\"") "issuer must be IRI-shaped"
#guard failsWith (vc "\"issuer\":7") "issuer must be a string or an object"
#guard failsWith (vc "\"issuer\":{\"id\":\"not an iri\"}") "issuer: id is not IRI-shaped"

-- credentialSubject: required, non-empty, every array entry non-empty.
#guard failsWith ("{" ++ base ++ "," ++ vcType ++ "}") "missing credentialSubject"
#guard failsWith ("{" ++ base ++ "," ++ vcType ++ ",\"credentialSubject\":{}}")
  "credentialSubject has no claims"
#guard failsWith ("{" ++ base ++ "," ++ vcType ++ ",\"credentialSubject\":[{\"a\":1},{}]}")
  "credentialSubject has no claims"
#guard failsWith ("{" ++ base ++ "," ++ vcType ++ ",\"credentialSubject\":[]}")
  "credentialSubject array is empty"
#guard pass ("{" ++ base ++ "," ++ vcType ++ ",\"credentialSubject\":[{\"a\":1},{\"b\":2}]}")
-- The subject's own id is ONE IRI string, not an array.
#guard failsWith ("{" ++ base ++ "," ++ vcType ++ ",\"credentialSubject\":{\"id\":[\"did:example:a\"]}}")
  "id must be a single IRI string"

-- holder: an object holder REQUIRES an id, unlike an object issuer.
private def vp (extra : String) : String :=
  "{" ++ base ++ ",\"type\":[\"VerifiablePresentation\"]" ++ (if extra.isEmpty then "" else "," ++ extra) ++ "}"
#guard pass (vp "")
#guard pass (vp "\"holder\":\"did:example:h\"")
#guard pass (vp "\"holder\":{\"id\":\"did:example:h\"}")
#guard failsWith (vp "\"holder\":{\"name\":\"Acme\"}") "holder: missing id"

-- credentialSchema requires id and type; the other typed fields only type.
#guard pass (vc "\"credentialSchema\":{\"id\":\"https://ex.org/s\",\"type\":\"JsonSchema\"}")
#guard failsWith (vc "\"credentialSchema\":{\"type\":\"JsonSchema\"}") "credentialSchema: missing id"
#guard failsWith (vc "\"credentialSchema\":{\"id\":\"https://ex.org/s\"}") "credentialSchema: missing type"
#guard pass (vc "\"credentialStatus\":[{\"type\":\"StatusList\"},{\"type\":\"Other\"}]")
#guard failsWith (vc "\"credentialStatus\":[{\"type\":\"StatusList\"},{}]") "credentialStatus: missing type"
#guard failsWith (vc "\"termsOfUse\":{\"id\":\"https://ex.org/t\"}") "termsOfUse: missing type"
#guard failsWith (vc "\"evidence\":\"x\"") "evidence must be an object or an array of objects"
#guard failsWith (vc "\"proof\":{\"id\":\"https://ex.org/p\"}") "proof: missing type"
#guard pass (vc "\"proof\":{\"type\":\"DataIntegrityProof\"}")

-- name and description: a string, a language map, or an array of language maps.
#guard pass (vc "\"name\":\"Plain\"")
#guard pass (vc "\"name\":{\"@value\":\"Hola\",\"@language\":\"es\"}")
#guard pass (vc "\"name\":[{\"@value\":\"a\"},{\"@value\":\"b\",\"@language\":\"en\"}]")
#guard failsWith (vc "\"name\":{\"@value\":\"Hola\",\"url\":\"x\"}") "name language-map object has a disallowed property"
#guard failsWith (vc "\"description\":[{\"@language\":\"en\"}]") "description language-map array contains a malformed entry"
#guard failsWith (vc "\"name\":5") "name must be a string"

-- The validity period: well-formed dateTimes, validFrom not after validUntil.
#guard pass (vc "\"validFrom\":\"2020-01-01T00:00:00Z\",\"validUntil\":\"2099-01-01T00:00:00Z\"")
#guard pass (vc "\"validFrom\":\"2020-01-01T00:00:00Z\",\"validUntil\":\"2020-01-01T00:00:00Z\"")
#guard failsWith (vc "\"validFrom\":\"2099-01-01T00:00:00Z\",\"validUntil\":\"2020-01-01T00:00:00Z\"")
  "validFrom must not be after validUntil"
#guard failsWith (vc "\"validFrom\":\"yesterday\"") "validFrom is not a well-formed xsd:dateTime"
#guard failsWith (vc "\"validUntil\":\"2020-13-01T00:00:00Z\"") "validUntil is not a well-formed xsd:dateTime"
#guard failsWith (vc "\"validFrom\":20200101") "validFrom must be a string"

-- relatedResource: objects with an IRI id and a digest; ids unique.
#guard pass (vc "\"relatedResource\":{\"id\":\"https://ex.org/r\",\"digestMultibase\":\"uAAAA\"}")
#guard pass (vc "\"relatedResource\":[{\"id\":\"https://ex.org/r\",\"digestSRI\":\"sha256-AAAA\",\"mediaType\":\"text/plain\"}]")
#guard failsWith (vc "\"relatedResource\":[\"https://ex.org/r\"]") "relatedResource entry must be an object"
#guard failsWith (vc "\"relatedResource\":{\"id\":\"https://ex.org/r\"}")
  "at least one of digestSRI or digestMultibase is required"
#guard failsWith (vc "\"relatedResource\":{\"digestSRI\":\"sha256-AAAA\"}") "relatedResource: missing id"
#guard failsWith (vc "\"relatedResource\":{\"id\":\"https://ex.org/r\",\"digestSRI\":\"sha256-AAAA\",\"mediaType\":3}")
  "mediaType must be a string"
#guard failsWith (vc ("\"relatedResource\":[{\"id\":\"https://ex.org/r\",\"digestSRI\":\"sha256-AAAA\"},"
    ++ "{\"id\":\"https://ex.org/r\",\"digestSRI\":\"sha256-BBBB\"}]"))
  "duplicate id"

-- @context: the base IRI must be FIRST. This layer reuses the strict layer's rule.
#guard failsWith ("{\"@context\":[\"https://ex.org/c\",\"https://www.w3.org/ns/credentials/v2\"]," ++ vcType ++ "," ++ subj ++ "}")
  "must be the FIRST @context entry"
#guard failsWith ("{" ++ vcType ++ "," ++ subj ++ "}") "missing @context"
#guard failsWith ("{" ++ base ++ ",\"type\":[\"Other\"]," ++ subj ++ "}") "missing the base VerifiableCredential"

-- A presentation's embedded credentials: an envelope needs an id, a full
-- credential is checked in full, a bare string is refused.
private def innerVc : String :=
  "{" ++ base ++ "," ++ vcType ++ "," ++ subj ++ "}"
#guard pass (vp ("\"verifiableCredential\":[" ++ innerVc ++ "]"))
#guard pass (vp ("\"verifiableCredential\":" ++ innerVc))
#guard pass (vp "\"verifiableCredential\":[{\"id\":\"data:application/jwt,x\",\"type\":\"EnvelopedVerifiableCredential\"}]")
#guard failsWith (vp "\"verifiableCredential\":[{\"type\":\"EnvelopedVerifiableCredential\"}]")
  "enveloped verifiableCredential entry is missing id"
#guard failsWith (vp "\"verifiableCredential\":[\"eyJhbGciOi\"]")
  "verifiableCredential entry must be a JSON object"
#guard failsWith (vp "\"verifiableCredential\":[{\"type\":\"Other\"}]")
  "neither VerifiableCredential nor EnvelopedVerifiableCredential"
#guard failsWith (vp ("\"verifiableCredential\":[{" ++ base ++ "," ++ vcType ++ "}]"))
  "missing credentialSubject"
#guard failsWith (vp "\"verifiableCredential\":3")
  "verifiableCredential must be an object or an array of objects"

/-! ## The `type` term-resolution gate

The vendored VCDM 2.0 base context makes its terms protected; the stand-in
below has the same shape for one term. -/

private def v2stub : Json :=
  match parseJson? "{\"@context\":{\"@protected\":true,\"VerifiableCredential\":\"https://www.w3.org/2018/credentials#VerifiableCredential\"}}" with
  | some j => j
  | none => .null

private def gate (ctxEntries typeList : String) : Verdict :=
  checkFromString v2stub
    ("{\"@context\":[\"https://www.w3.org/ns/credentials/v2\"" ++ ctxEntries ++ "],\"type\":" ++ typeList ++ "," ++ subj ++ "}")

-- Redefining a protected base term with a different mapping is an error; the
-- same mapping restated is not.
#guard (gate "" "[\"VerifiableCredential\"]").ok
#guard !(gate ",{\"VerifiableCredential\":\"https://evil.example/Other\"}" "[\"VerifiableCredential\"]").ok
#guard (gate ",{\"VerifiableCredential\":\"https://www.w3.org/2018/credentials#VerifiableCredential\"}"
  "[\"VerifiableCredential\"]").ok
-- An inline protected term cannot be redefined by a later inline context.
#guard !(gate ",{\"@protected\":true,\"Foo\":\"https://ex.org/Foo\"},{\"Foo\":\"https://ex.org/Bar\"}"
  "[\"VerifiableCredential\"]").ok
-- A type term mapped to a non-URL is refused; mapped to a URL it is accepted.
#guard !(gate ",{\"Ex\":\"https ://not-a-url\"}" "[\"VerifiableCredential\",\"Ex\"]").ok
#guard (gate ",{\"Ex\":\"https://ex.org/Ex\"}" "[\"VerifiableCredential\",\"Ex\"]").ok
-- An unmapped term is refused only when @vocab was nullified and nothing remote
-- could define it.
#guard !(gate ",{\"@vocab\":null}" "[\"VerifiableCredential\",\"Ghost\"]").ok
#guard (gate ",{\"@vocab\":null},\"https://ex.org/remote\"" "[\"VerifiableCredential\",\"Ghost\"]").ok
#guard (gate "" "[\"VerifiableCredential\",\"Ghost\"]").ok

/-! ## relatedResource digests against a registry -/

-- The registry the host supplies: the SHA-256 of the vendored 2024-07-20 VCDM
-- 2.0 context (third_party/contexts/PROVENANCE.md), as lowercase hex.
private def registry : String :=
  "[{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestsHex\":[\"24a18c90e9856d526111f29376e302d970b2bd10182e33959995b0207d7043b9\"]}]"

private def digestOk (rr : String) : Bool :=
  match checkRelatedResourceDigestsFromString registry (vc ("\"relatedResource\":" ++ rr)) with
  | .pass => true
  | .fail _ => false

-- digestMultibase `u` is base64url of the raw digest; the test suite's own
-- fixture value for this resource is `uJKGM…`.
#guard digestOk "{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestMultibase\":\"uJKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7k\"}"
-- One altered character is the spec's mismatch error.
#guard !digestOk "{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestMultibase\":\"uJKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7j\"}"
-- digestSRI: standard base64 with padding, and the dash splits at the FIRST dash.
#guard digestOk "{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestSRI\":\"sha256-JKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7k=\"}"
#guard !digestOk "{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestSRI\":\"sha256-JKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7j=\"}"
#guard !digestOk "{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestSRI\":\"JKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7k\"}"
-- An algorithm the registry does not cover is unverifiable offline: it passes.
#guard digestOk "{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestSRI\":\"sha512-AAAA\"}"
-- A resource the registry does not know is unverifiable offline: it passes.
#guard digestOk "{\"id\":\"https://ex.org/unknown\",\"digestMultibase\":\"uAAAA\"}"
-- Both digests must match when both are declared.
#guard !digestOk ("{\"id\":\"https://www.w3.org/ns/credentials/v2\","
  ++ "\"digestMultibase\":\"uJKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7k\","
  ++ "\"digestSRI\":\"sha256-AAAA\"}")
-- A multibase prefix other than `u` and `z` cannot match a computed digest.
#guard !digestOk "{\"id\":\"https://www.w3.org/ns/credentials/v2\",\"digestMultibase\":\"mAAAA\"}"
-- A malformed registry, document or top level is refused with a reason.
#guard (match checkRelatedResourceDigestsFromString "[" "{}" with
        | .fail r => (r.splitOn "digest registry is not well-formed JSON").length > 1
        | .pass => false)
#guard (match checkRelatedResourceDigestsFromString "[]" "[]" with
        | .fail r => (r.splitOn "top-level JSON value must be an object").length > 1
        | .pass => false)
-- No relatedResource member: nothing to verify.
#guard (checkRelatedResourceDigestsFromString registry (vc "")).ok

/-! ## DATA_LOSS_DETECTION_ERROR -/

private def loss (s : String) : Verdict := checkNoDataLossFromString s

private def lossDoc (ctx types subject : String) : String :=
  "{\"@context\":" ++ ctx ++ ",\"type\":" ++ types ++ ",\"credentialSubject\":" ++ subject ++ "}"

private def ctxDefined : String :=
  "{\"Known\":\"https://ex.org/Known\",\"name\":\"https://schema.org/name\"}"

#guard (loss (lossDoc ctxDefined "[\"Known\"]" "{\"name\":\"x\"}")).ok
-- An undefined type term would be dropped by a lenient processor.
#guard !(loss (lossDoc ctxDefined "[\"Unknown\"]" "{\"name\":\"x\"}")).ok
#guard (match loss (lossDoc ctxDefined "[\"Known\",\"Unknown\"]" "{\"name\":\"x\"}") with
        | .fail r => (r.splitOn "DATA_LOSS_DETECTION_ERROR").length > 1
        | .pass => false)
-- So would an undefined credentialSubject key; `id` and `@id` are not keys.
#guard !(loss (lossDoc ctxDefined "[\"Known\"]" "{\"nick\":\"x\"}")).ok
#guard (loss (lossDoc ctxDefined "[\"Known\"]" "{\"id\":\"did:example:s\",\"@id\":\"did:example:s\",\"name\":\"x\"}")).ok
#guard !(loss (lossDoc ctxDefined "[\"Known\"]" "[{\"name\":\"x\"},{\"nick\":\"y\"}]")).ok
-- An absolute IRI as a type, and a compact IRI whose prefix is defined, resolve.
#guard (loss (lossDoc ctxDefined "[\"https://ex.org/Absolute\"]" "{\"name\":\"x\"}")).ok
-- @vocab defines everything vocabulary-relative.
#guard (loss (lossDoc "{\"@vocab\":\"https://ex.org/\"}" "[\"Anything\"]" "{\"anything\":\"x\"}")).ok
-- An array context folds in order.
#guard (loss (lossDoc "[{\"@vocab\":\"https://ex.org/\"},{\"x\":\"https://ex.org/x\"}]" "[\"T\"]" "{\"k\":1}")).ok
-- A bare remote IRI cannot be fetched here: the check fails rather than skipping.
#guard (match loss (lossDoc "\"https://www.w3.org/ns/credentials/v2\"" "[\"VerifiableCredential\"]" "{\"a\":1}") with
        | .fail r => (r.splitOn "could not process @context").length > 1
        | .pass => false)
#guard (match loss "{\"type\":[\"T\"]}" with
        | .fail r => (r.splitOn "missing @context").length > 1
        | .pass => false)
#guard (match loss "[]" with
        | .fail r => (r.splitOn "top-level JSON value must be an object").length > 1
        | .pass => false)
-- No credentialSubject member: only the type terms are checked.
#guard (loss ("{\"@context\":" ++ ctxDefined ++ ",\"type\":[\"Known\"]}")).ok
#guard !(loss ("{\"@context\":" ++ ctxDefined ++ ",\"type\":[\"Unknown\"]}")).ok

/-! ## credentialSubject without the `@context` gate -/

#guard (checkCredentialSubjectFromString ("{\"@context\":\"https://www.w3.org/2018/credentials/v1\"," ++ vcType ++ "," ++ subj ++ "}")).ok
#guard !(checkCredentialSubjectFromString ("{\"@context\":\"https://www.w3.org/2018/credentials/v1\"," ++ vcType ++ "}")).ok
#guard !(checkCredentialSubjectFromString ("{" ++ vcType ++ ",\"credentialSubject\":{}}")).ok
-- A document that is not credential-shaped has no subject to check.
#guard (checkCredentialSubjectFromString "{\"type\":[\"VerifiablePresentation\"]}").ok
#guard !(checkCredentialSubjectFromString "not json").ok

end Doc

end L4Factoidal.VC
