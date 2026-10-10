/-
L4Factoidal.VC.Credential — the Verifiable Credentials 2.0 data-model
checks, ported from `formal/fstar/VC.Credential.fst`.

Spec: VC Data Model 2.0 (https://www.w3.org/TR/vc-data-model-2.0/)
§4 — `@context`, `type`, `id`, `issuer`, `credentialSubject` and the
validity dates.

Verdicts carry a REASON string rather than being a bare boolean.
A credential-verification failure that says only "false" is
unactionable, and the VC test suite distinguishes failure modes.

## Two layers

The definitions in `namespace L4Factoidal.VC` (`checkCredential`,
`checkPresentation`, ...) are the first, strict layer: a credential MUST
have an `issuer`, and so on, as VCDM 2.0 §4 words it.

`namespace L4Factoidal.VC.Doc`, at the end of this file, is the port of the
rest of `VC.Credential.fst` (stage 2, 2026-07-06, and the later
`relatedResource`, version-agnostic and data-loss entry points) that
`bin/npm-entry/entry_extras.ml` calls: `Doc.checkFromString` is
`vc_check_from_string`, `Doc.checkCredentialSubjectFromString` is
`vc_check_credential_subject_from_string`, `Doc.checkNoDataLossFromString` is
`vc_check_no_data_loss_from_string` and `Doc.checkRelatedResourceDigestsFromString`
is `vc_check_related_resource_digests_from_string`. It is scored against the
vendored `third_party/testing/vc` fixtures by `Harness/VcProbe.lean`, whose
`-ok` and `-fail` file-name suffixes carry the expected verdict. It is
looser than the first layer where the fixtures are: an absent `issuer`
passes, because most `-ok` fixtures omit it.

Differences from the F* module, each deliberate:

  * `looksLikeIri` also refuses a TAB. The F* predicate refuses only a space.
  * `validFrom` and `validUntil` use the XSD 1.1 lexical mapping of
    `XSD/Datatypes.lean` (a month 13 is refused), where the F*
    `XSD.dt_parse_ms` reads six integers and accepts it.
  * Two `xsd:dateTime` values compare through the ±14:00 window of XML Schema
    1.1 §3.2.7.4 when one has a timezone and the other has none, where the F*
    `dt_cmp` calls that pair incomparable. An incomparable pair passes in both.
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Parser
import L4Factoidal.JSONLD.Context
import L4Factoidal.VC.Context
import L4Factoidal.VC.Multibase
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.VC

open L4Factoidal.JSON

inductive Verdict where
  | pass
  | fail (reason : String)
deriving Repr, DecidableEq, Inhabited

def Verdict.ok : Verdict → Bool
  | .pass => true
  | .fail _ => false

/-- Both must pass; the FIRST failure's reason is kept, so the
    message names the earliest problem rather than the last. -/
def Verdict.both : Verdict → Verdict → Verdict
  | .fail r, _ => .fail r
  | _, v => v

def all (vs : List Verdict) : Verdict := vs.foldl Verdict.both .pass

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

/-- A cheap IRI shape test: a scheme separator and no whitespace. The
    full grammar lives in `RDF.Core`; this is the structural check the
    F* module makes at this layer. -/
def looksLikeIri (s : String) : Bool :=
  s.toList.contains ':' && !(s.toList.any (fun c => c == ' ' || c == '\t'))

def baseContext : String := "https://www.w3.org/ns/credentials/v2"
def credentialType : String := "VerifiableCredential"
def presentationType : String := "VerifiablePresentation"
def envelopedCredentialType : String := "EnvelopedVerifiableCredential"

/-- One `@context` entry. A string must look like an IRI; an inline
    object or `null` is structurally acceptable per the JSON-LD
    grammar. -/
def contextEntryOk (v : Json) : Bool :=
  match v with
  | .string s => looksLikeIri s
  | .object _ => true
  | .null     => true
  | _         => false

/-- §4.1 `@context`.

    THE RULE THAT MATTERS: the base VC 2.0 context IRI must be the
    FIRST entry, not merely present. JSON-LD context processing is
    ORDER-DEPENDENT — a later entry can redefine terms an earlier one
    established — so a credential listing the base context second has
    different semantics from one listing it first, and accepting both
    would let a crafted context silently redefine `issuer` or
    `credentialSubject`. -/
def checkContext (v : Json) : Verdict :=
  match field? "@context" v with
  | none => .fail "missing @context"
  | some (.string s) =>
      if s == baseContext then .pass
      else .fail "bare-string @context must equal the base VC 2.0 context IRI"
  | some (.array items) =>
      match items with
      | [] => .fail "@context is an empty array"
      | first :: _ =>
          if !(items.all contextEntryOk) then
            .fail "an @context entry is neither a well-formed IRI string, an object, nor null"
          else match first with
            | .string s =>
                if s == baseContext then .pass
                else .fail "the base VC 2.0 context IRI must be the FIRST @context entry"
            | _ => .fail "the first @context entry must be the base VC 2.0 context IRI string"
  | some _ => .fail "@context must be a string or an array"

/-- The `type` value as a list of strings, accepting the string or
    array form. -/
def decodeTypeList (v : Json) : List String :=
  match v with
  | .string s => [s]
  | .array items => items.filterMap (fun i => match i with
      | .string s => some s
      | _ => none)
  | _ => []

/-- §4.2 `type` must include the base type. -/
def checkTypeMembership (v : Json) (required : String) : Verdict :=
  match field? "type" v with
  | none => .fail "missing type"
  | some t =>
      let types := decodeTypeList t
      if types.isEmpty then .fail "type is empty or not string-valued"
      else if types.contains required then .pass
      else .fail ("type must include " ++ required)

/-- §4.3 `id`, when present, must be a single IRI string. Absence is
    allowed unless `required`. -/
def checkIdField (required : Bool) (label : String) (v : Json) : Verdict :=
  match field? "id" v with
  | none => if required then .fail (label ++ " is missing id") else .pass
  | some (.string s) =>
      if looksLikeIri s then .pass else .fail (label ++ " id is not an IRI")
  | some _ => .fail (label ++ " id must be a string")

/-- §4.5 `issuer`: either an IRI string or an object carrying an
    `id`. -/
def checkIssuer (v : Json) : Verdict :=
  match field? "issuer" v with
  | none => .fail "missing issuer"
  | some (.string s) =>
      if looksLikeIri s then .pass else .fail "issuer string is not an IRI"
  | some o =>
      match o with
      | .object _ => checkIdField true "issuer object" o
      | _ => .fail "issuer must be a string or an object"

/-- §4.4 `credentialSubject` must be present and non-empty. An EMPTY
    object is a failure: a credential asserting nothing about anyone
    is not a credential. -/
def checkCredentialSubject (v : Json) : Verdict :=
  match field? "credentialSubject" v with
  | none => .fail "missing credentialSubject"
  | some (.object []) => .fail "credentialSubject is empty"
  | some (.object _) => .pass
  | some (.array []) => .fail "credentialSubject array is empty"
  | some (.array _) => .pass
  | some _ => .fail "credentialSubject must be an object or an array"

/-- §4.6/§4.7 validity dates, when present, must be strings. Their
    ORDERING is checked by the caller against a clock — this module
    stays a total function of its input, so it does not read a clock
    itself. -/
def checkValidityDates (v : Json) : Verdict :=
  let dateOk (k : String) : Verdict :=
    match field? k v with
    | none => .pass
    | some (.string _) => .pass
    | some _ => .fail (k ++ " must be a string")
  Verdict.both (dateOk "validFrom") (dateOk "validUntil")

/-- Whole-credential structural check. -/
def checkCredential (v : Json) : Verdict :=
  all [ checkContext v,
        checkTypeMembership v credentialType,
        checkIdField false "credential" v,
        checkIssuer v,
        checkCredentialSubject v,
        checkValidityDates v ]

/-- A presentation carries `VerifiablePresentation` instead, and has
    no issuer or subject of its own. -/
def checkPresentation (v : Json) : Verdict :=
  all [ checkContext v,
        checkTypeMembership v presentationType,
        checkIdField false "presentation" v ]

end L4Factoidal.VC

/-! # `L4Factoidal.VC.Doc` — the document-level checks

Port of the stage 2 half of `formal/fstar/VC.Credential.fst`. See the module
header for how it relates to the strict layer above. -/

namespace L4Factoidal.VC.Doc

open L4Factoidal.JSON
open L4Factoidal.VC
open L4Factoidal.VC.Multibase (hexOfBytes base58Decode? base64ToHex)

private def stringMember? (name : String) (v : Json) : Option String :=
  match field? name v with
  | some (.string s) => some s
  | _ => none

private def stringItems (items : List Json) : List String :=
  items.filterMap fun j => match j with
    | .string s => some s
    | _ => none

/-- The `type` member of a DOCUMENT as a list of strings: a string is a
one-element list, an array keeps its string elements, anything else (or
absence) is the empty list. Port of `vc_decode_type_list`. -/
def docTypes (v : Json) : List String :=
  match field? "type" v with
  | some t => decodeTypeList t
  | none => []

/-- The first failure, as `Verdict.both` keeps it, over a list of checks. -/
def checkAll (f : Json → Verdict) : List Json → Verdict
  | [] => .pass
  | h :: t =>
      match f h with
      | .fail r => .fail r
      | .pass => checkAll f t

/-! ## Base type, ids, required type -/

/-- §4.2: `type` includes `VerifiableCredential` or `VerifiablePresentation`.
Port of `vc_check_type_membership`. -/
def checkBaseType (v : Json) : Verdict :=
  let types := docTypes v
  if types.contains credentialType || types.contains presentationType then .pass
  else .fail "type array/string is missing the base VerifiableCredential/VerifiablePresentation type"

/-- `id`, when present, is ONE IRI-shaped string. Port of
`vc_check_optional_id_field`. -/
def checkOptionalId (required : Bool) (label : String) (v : Json) : Verdict :=
  match field? "id" v with
  | none => if required then .fail (label ++ ": missing id") else .pass
  | some (.string s) =>
      if looksLikeIri s then .pass else .fail (label ++ ": id is not IRI-shaped")
  | some _ => .fail (label ++ ": id must be a single IRI string, not an array/null/other")

/-- `type` is present and a string. Port of `vc_check_required_type_field`. -/
def checkRequiredType (label : String) (v : Json) : Verdict :=
  match field? "type" v with
  | some (.string _) => .pass
  | some _ => .fail (label ++ ": type must be a string")
  | none => .fail (label ++ ": missing type")

/-! ## credentialSubject, issuer, holder -/

def checkSubjectObject : Json → Verdict
  | .object fields =>
      if fields.isEmpty then .fail "credentialSubject has no claims (empty object)"
      else checkOptionalId false "credentialSubject" (.object fields)
  | _ => .fail "credentialSubject entry must be an object"

/-- Present, non-empty, and every entry an object whose own `id` is one IRI.
Port of `vc_check_credential_subject`. -/
def checkSubject (v : Json) : Verdict :=
  match field? "credentialSubject" v with
  | none => .fail "missing credentialSubject"
  | some (.object fields) => checkSubjectObject (.object fields)
  | some (.array []) => .fail "credentialSubject array is empty"
  | some (.array items) => checkAll checkSubjectObject items
  | some _ => .fail "credentialSubject must be an object or an array of objects"

/-- A language-map entry carries `@value` (a string) and no property other
than `@language` and `@direction`. -/
def langMapEntryOk : Json → Bool
  | .object fields =>
      fields.all (fun f => f.1 == "@value" || f.1 == "@language" || f.1 == "@direction")
      && (match field? "@value" (.object fields) with
          | some (.string _) => true
          | _ => false)
  | _ => false

/-- `name` and `description`: a string, one language-map object, or an array of
language-map objects. Port of `vc_check_lang_map_field`. -/
def checkLangMapField (name : String) (v : Json) : Verdict :=
  match field? name v with
  | none => .pass
  | some (.string _) => .pass
  | some (.object fields) =>
      if langMapEntryOk (.object fields) then .pass
      else .fail (name ++ " language-map object has a disallowed property or missing @value")
  | some (.array items) =>
      if items.all langMapEntryOk then .pass
      else .fail (name ++ " language-map array contains a malformed entry")
  | some _ =>
      .fail (name ++ " must be a string, a language-map object, or an array of language-map objects")

/-- `issuer` is OPTIONAL here (most `-ok` fixtures omit it); when present, a
string is IRI-shaped and an object has an optional IRI-shaped `id` and
language-map `name` and `description`. Port of `vc_check_issuer`. -/
def checkIssuer (v : Json) : Verdict :=
  match field? "issuer" v with
  | none => .pass
  | some (.string s) => if looksLikeIri s then .pass else .fail "issuer must be IRI-shaped"
  | some (.object fields) =>
      let obj := Json.object fields
      all [ checkOptionalId false "issuer" obj,
            checkLangMapField "name" obj,
            checkLangMapField "description" obj ]
  | some _ => .fail "issuer must be a string or an object"

/-- `holder`: unlike `issuer`, an object holder REQUIRES an `id`. Port of
`vc_check_holder`. -/
def checkHolder (v : Json) : Verdict :=
  match field? "holder" v with
  | none => .pass
  | some (.string s) => if looksLikeIri s then .pass else .fail "holder must be IRI-shaped"
  | some (.object fields) => checkOptionalId true "holder" (.object fields)
  | some _ => .fail "holder must be a string or an object"

/-! ## credentialStatus, credentialSchema, termsOfUse, evidence,
refreshService, proof: one object or an array of objects, each with a
string `type`; only `credentialSchema` requires an `id`. -/

/-- One entry of such a field. `idRequired` is true for `credentialSchema`. -/
def checkTypedObject (label : String) (idRequired : Bool) : Json → Verdict
  | .object fields =>
      Verdict.both (checkRequiredType label (.object fields))
        (checkOptionalId idRequired label (.object fields))
  | _ => .fail (label ++ " entry must be an object")

/-- `proof` checks only `type`; the proof shape is `DataIntegrity.lean`'s job. -/
def checkProofObject : Json → Verdict
  | .object fields => checkRequiredType "proof" (.object fields)
  | _ => .fail "proof entry must be an object"

def checkObjectOrArrayField (checker : Json → Verdict) (name : String) (v : Json) : Verdict :=
  match field? name v with
  | none => .pass
  | some (.object fields) => checker (.object fields)
  | some (.array items) => checkAll checker items
  | some _ => .fail (name ++ " must be an object or an array of objects")

/-! ## relatedResource (VCDM 2.0 §5.3) -/

/-- One entry: an object with an IRI-shaped `id`, at least one of `digestSRI`
and `digestMultibase` (as strings), and a string `mediaType` when present. -/
def checkRelatedResourceObject : Json → Verdict
  | .object fields =>
      let v := Json.object fields
      match checkOptionalId true "relatedResource" v with
      | .fail r => .fail r
      | .pass =>
          let hasSri := (stringMember? "digestSRI" v).isSome
          let hasMb := (stringMember? "digestMultibase" v).isSome
          if !(hasSri || hasMb) then
            .fail "relatedResource: at least one of digestSRI or digestMultibase is required"
          else
            match field? "mediaType" v with
            | none => .pass
            | some (.string _) => .pass
            | some _ => .fail "relatedResource: mediaType must be a string"
  | _ => .fail "relatedResource entry must be an object"

def hasDup (seen : List String) : List String → Bool
  | [] => false
  | h :: t => if seen.contains h then true else hasDup (h :: seen) t

/-- Every entry is well formed and the `id`s are unique. -/
def checkRelatedResourceList (items : List Json) : Verdict :=
  match checkAll checkRelatedResourceObject items with
  | .fail r => .fail r
  | .pass =>
      if hasDup [] (items.filterMap (stringMember? "id")) then
        .fail "relatedResource: duplicate id among related resource objects"
      else .pass

def checkRelatedResource (v : Json) : Verdict :=
  match field? "relatedResource" v with
  | none => .pass
  | some (.object fields) => checkRelatedResourceObject (.object fields)
  | some (.array items) => checkRelatedResourceList items
  | some _ => .fail "relatedResource must be an object or an array of objects"

/-! ## relatedResource digest VERIFICATION (VCDM 2.0 §5.3)

"If the digest provided by the issuer does not match the digest computed for
the retrieved resource, the conforming verifier implementation MUST produce an
error." This module does no I/O, so the retrieved resource is supplied by the
CALLER as a digest registry: a JSON array `[{"id": <resource URL>,
"digestsHex": [<lowercase hex>, …]}]` of the digests (SHA-256 and SHA-384,
possibly several revisions of a resource that changed over time) computed from
vendored copies of the resource's content bytes.

The SEMANTICS are here: how a declared `digestMultibase` or `digestSRI` value
decodes, and what "matches" means, a lowercase-hex comparison against ANY known
revision's digest. The offline policy: a resource id absent from the registry,
or a digest algorithm the registry does not cover, is UNVERIFIABLE offline and
passes (checking it would need a fetch); a KNOWN resource whose declared digest
matches no known revision is the spec's mismatch error. -/

/-- The digests the registry holds for resource `rid`, from its FIRST entry
with that `id`. `none` when no entry names it. -/
def registryDigestsFor : List Json → String → Option (List String)
  | [], _ => none
  | e :: tl, rid =>
      match stringMember? "id" e with
      | some i =>
          if i == rid then
            match field? "digestsHex" e with
            | some (.array items) => some (stringItems items)
            | _ => some []
          else registryDigestsFor tl rid
      | none => registryDigestsFor tl rid

/-- A declared `digestMultibase` as lowercase hex. Multibase `u` is base64url
without padding, `z` is base58btc; any other prefix decodes to `none`, which
cannot match a computed digest. -/
def digestMultibaseToHex (s : String) : Option String :=
  match s.toList with
  | c :: rest =>
      if c == 'u' then base64ToHex (String.ofList rest)
      else if c == 'z' then (base58Decode? (String.ofList rest)).map hexOfBytes
      else none
  | [] => none

/-- Split `<algo>-<base64>` at the FIRST dash: the base64url payload may itself
contain a dash, the algorithm label never does. -/
def splitAtDash (cs : List Char) : Option (List Char × List Char) :=
  match cs.span (· != '-') with
  | (pre, _ :: post) => some (pre, post)
  | (_, []) => none

/-- The algorithms every registry entry is DEFINED to cover. -/
def registryCoveredAlgo (algo : String) : Bool := algo == "sha256" || algo == "sha384"

def checkRrDigestObject (entries : List Json) (v : Json) : Verdict :=
  match stringMember? "id" v with
  | none => .pass   -- a missing or non-string id is `checkRelatedResource`'s concern
  | some rid =>
      match registryDigestsFor entries rid with
      | none => .pass   -- an unknown resource is unverifiable offline
      | some known =>
          let mbOk : Bool :=
            match stringMember? "digestMultibase" v with
            | some s =>
                match digestMultibaseToHex s with
                | some hx => known.contains hx
                | none => false
            | none => true
          if !mbOk then
            .fail "relatedResource: digestMultibase does not match the digest computed for the resource"
          else
            let sriOk : Bool :=
              match stringMember? "digestSRI" v with
              | some s =>
                  match splitAtDash s.toList with
                  | some (algoCs, valCs) =>
                      if registryCoveredAlgo (String.ofList algoCs) then
                        match base64ToHex (String.ofList valCs) with
                        | some hx => known.contains hx
                        | none => false
                      else true   -- outside the registry contract: unverifiable offline
                  | none => false   -- no "<algo>-" prefix: matches no computed digest
              | none => true
            if !sriOk then
              .fail "relatedResource: digestSRI does not match the digest computed for the resource"
            else .pass

/-- Port of `vc_check_related_resource_digests`. -/
def checkRelatedResourceDigests (registry v : Json) : Verdict :=
  let entries := match registry with
    | .array es => es
    | _ => []
  match field? "relatedResource" v with
  | none => .pass
  | some (.object fields) => checkRrDigestObject entries (.object fields)
  | some (.array items) => checkAll (checkRrDigestObject entries) items
  | some _ => .pass   -- shape errors are `checkRelatedResource`'s concern

/-- Port of `vc_check_related_resource_digests_from_string`. -/
def checkRelatedResourceDigestsFromString (registryJson input : String) : Verdict :=
  match parseJson? registryJson with
  | none => .fail "digest registry is not well-formed JSON"
  | some reg =>
      match parseJson? input with
      | none => .fail "input is not well-formed JSON"
      | some (.object fields) => checkRelatedResourceDigests reg (.object fields)
      | some _ => .fail "top-level JSON value must be an object"

/-! ## Validity period (VCDM 2.0 §4.9) -/

/-- `validFrom` / `validUntil`, when present, are well-formed `xsd:dateTime`
lexical forms. -/
def checkTemporalLexical (name : String) (v : Json) : Verdict :=
  match field? name v with
  | none => .pass
  | some (.string s) =>
      if (L4Factoidal.XSD.parseDateTimeLex .dateTime s).isSome then .pass
      else .fail (name ++ " is not a well-formed xsd:dateTime lexical form")
  | some _ => .fail (name ++ " must be a string")

/-- `validFrom` is not after `validUntil`. An incomparable pair, and a value the
lexical check already refused, pass here: the lexical check reports them. -/
def checkTemporalOrdering (v : Json) : Verdict :=
  match stringMember? "validFrom" v, stringMember? "validUntil" v with
  | some sf, some su =>
      match L4Factoidal.XSD.parseDateTimeLex .dateTime sf,
            L4Factoidal.XSD.parseDateTimeLex .dateTime su with
      | some a, some b =>
          match L4Factoidal.XSD.dtCompare a b with
          | some .gt => .fail "validFrom must not be after validUntil"
          | _ => .pass
      | _, _ => .pass
  | _, _ => .pass

def checkValidityPeriod (v : Json) : Verdict :=
  all [ checkTemporalLexical "validFrom" v,
        checkTemporalLexical "validUntil" v,
        checkTemporalOrdering v ]

/-! ## The document -/

/-- The checks shared by a top-level document AND a fully embedded credential.
Port of `vc_check_credential_shaped`. Every check besides `@context`, `type` and
`credentialSubject` is safe on a presentation, whose corresponding field is
absent and passes. -/
def checkCredentialShaped (v : Json) : Verdict :=
  match all [ checkContext v,
              checkBaseType v,
              checkOptionalId false "document" v,
              checkIssuer v,
              checkHolder v,
              checkLangMapField "name" v,
              checkLangMapField "description" v,
              checkObjectOrArrayField (checkTypedObject "credentialStatus" false)
                "credentialStatus" v,
              checkObjectOrArrayField (checkTypedObject "credentialSchema" true)
                "credentialSchema" v,
              checkObjectOrArrayField (checkTypedObject "termsOfUse" false) "termsOfUse" v,
              checkObjectOrArrayField (checkTypedObject "evidence" false) "evidence" v,
              checkObjectOrArrayField (checkTypedObject "refreshService" false)
                "refreshService" v,
              checkObjectOrArrayField checkProofObject "proof" v,
              checkValidityPeriod v,
              checkRelatedResource v ] with
  | .fail r => .fail r
  | .pass =>
      if (docTypes v).contains credentialType then checkSubject v else .pass

/-- One `verifiableCredential` entry of a presentation: an envelope (checked
only for an `id`) or a full embedded credential. Port of
`vc_check_embedded_item`. -/
def checkEmbeddedItem : Json → Verdict
  | .object fields =>
      let v := Json.object fields
      let types := docTypes v
      if types.contains envelopedCredentialType then
        match stringMember? "id" v with
        | some _ => .pass
        | none => .fail "enveloped verifiableCredential entry is missing id"
      else if types.contains credentialType then checkCredentialShaped v
      else
        .fail "verifiableCredential entry has neither VerifiableCredential nor EnvelopedVerifiableCredential type"
  | _ => .fail "verifiableCredential entry must be a JSON object"

def checkEmbeddedCredentials (v : Json) : Verdict :=
  match field? "verifiableCredential" v with
  | none => .pass
  | some (.array items) => checkAll checkEmbeddedItem items
  | some (.object fields) => checkEmbeddedItem (.object fields)
  | some _ => .fail "verifiableCredential must be an object or an array of objects"

/-- Port of `vc_check_document`. `v2ctx` is the parsed vendored VCDM 2.0 base
context (`third_party/contexts/credentials-v2.jsonld`), supplied by the caller,
so the check stays a total function with no I/O. The context type-resolution
gate runs only after the structural checks pass. -/
def checkDocument (v2ctx v : Json) : Verdict :=
  match checkCredentialShaped v with
  | .fail r => .fail r
  | .pass =>
      match L4Factoidal.VC.Context.checkTypes v2ctx v (docTypes v) with
      | .violation r => .fail r
      | .ok =>
          if (docTypes v).contains presentationType then checkEmbeddedCredentials v
          else .pass

/-- Port of `vc_check_from_string`. -/
def checkFromString (v2ctx : Json) (input : String) : Verdict :=
  match parseJson? input with
  | none => .fail "input is not well-formed JSON"
  | some (.object fields) => checkDocument v2ctx (.object fields)
  | some _ => .fail "top-level JSON value must be an object"

/-! ## Version-agnostic entry points

Two checks that hold for a credential-shaped document whatever VCDM version
its base `@context` declares. -/

/-- Port of `vc_check_credential_subject_if_credential_shaped`. -/
def checkSubjectIfCredential (v : Json) : Verdict :=
  if (docTypes v).contains credentialType then checkSubject v else .pass

/-- Port of `vc_check_credential_subject_from_string`. -/
def checkCredentialSubjectFromString (input : String) : Verdict :=
  match parseJson? input with
  | none => .fail "input is not well-formed JSON"
  | some (.object fields) => checkSubjectIfCredential (.object fields)
  | some _ => .fail "top-level JSON value must be an object"

/-! ## DATA_LOSS_DETECTION_ERROR

Verifiable Credential Data Integrity 1.0, "Securing Data Losslessly": an
implementation MUST throw an error, which SHOULD be DATA_LOSS_DETECTION_ERROR,
when a JSON-LD processor drops data, such as an undefined term.

Scope: the two shapes the vc-di-eddsa suite exercises. An undefined `type`
entry (`termResolvesAsType`: vocabulary-relative, then document-relative), and
an undefined `credentialSubject` property key, one level down
(`termResolvesAsProperty`: vocabulary-relative only, the JSON-LD 1.1 rule for
member keys). It is not a recursive coverage checker. -/

def checkTypeTermsResolve (ac : L4Factoidal.JSONLD.ActiveContext) (v : Json) : Verdict :=
  if (docTypes v).all (L4Factoidal.JSONLD.termResolvesAsType ac) then .pass
  else .fail "undefined type term would be dropped by JSON-LD processing (DATA_LOSS_DETECTION_ERROR)"

/-- The property keys of a credentialSubject object, `id` and `@id` excluded. -/
def subjectKeys : Json → List String
  | .object fields => (fields.filter (fun f => f.1 != "id" && f.1 != "@id")).map (·.1)
  | _ => []

def checkSubjectTermsResolveOne (ac : L4Factoidal.JSONLD.ActiveContext) (subj : Json) : Verdict :=
  if (subjectKeys subj).all (L4Factoidal.JSONLD.termResolvesAsProperty ac) then .pass
  else .fail "undefined credentialSubject term would be dropped by JSON-LD processing (DATA_LOSS_DETECTION_ERROR)"

def checkSubjectTermsResolve (ac : L4Factoidal.JSONLD.ActiveContext) (v : Json) : Verdict :=
  match field? "credentialSubject" v with
  | none => .pass
  | some (.object fields) => checkSubjectTermsResolveOne ac (.object fields)
  | some (.array items) => checkAll (checkSubjectTermsResolveOne ac) items
  | some _ => .pass   -- a shape error is `checkSubject`'s concern

/-- Port of `vc_check_no_data_loss`. -/
def checkNoDataLoss (ac : L4Factoidal.JSONLD.ActiveContext) (v : Json) : Verdict :=
  Verdict.both (checkTypeTermsResolve ac v) (checkSubjectTermsResolve ac v)

/-- Port of `vc_check_no_data_loss_from_string`. `input` is the document's raw
JSON text with its `@context` ALREADY resolved to inline JSON. The loader is
the one that refuses every IRI, so a bare remote IRI string fails context
processing instead of being skipped: there is no empty-context fallback. -/
def checkNoDataLossFromString (input : String) : Verdict :=
  match parseJson? input with
  | none => .fail "input is not well-formed JSON"
  | some (.object fields) =>
      let v := Json.object fields
      match field? "@context" v with
      | none => .fail "missing @context"
      | some ctxv =>
          match L4Factoidal.JSONLD.activeContextFromJson L4Factoidal.JSONLD.Loader.none ctxv with
          | .error _ => .fail "could not process @context"
          | .ok ac => checkNoDataLoss ac v
  | some _ => .fail "top-level JSON value must be an object"

end L4Factoidal.VC.Doc
