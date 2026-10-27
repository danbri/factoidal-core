/-
L4Factoidal.CID.Document — the data model of Controlled Identifiers v1.0
(W3C Recommendation, 15 May 2025, https://www.w3.org/TR/cid-1.0/ §2):
controlled identifier documents, verification methods with their
verification material (Multikey, JsonWebKey), and the five verification
relationships (https://github.com/danbri/factoidal/issues/1100, items 1, 2
and 4).

`parseDocument` reads a JSON value (a JSON-LD document with the CID
context is the same JSON value) and checks every MUST of §2. Each failed
MUST is one constructor of `DocError`. The checks:

  * §2.1.1 `id`: present in the topmost map, a string, a URL. The base
    identifier is the canonical URL (§2.1.1), so it must be absolute.
  * §2.1.2 `controller`: a string or a set of strings, each a URL.
  * §2.1.3 `alsoKnownAs`: a set of strings, each a URI (RFC 3986, absolute).
  * §2.1.4 `service`: a set of maps; `id` (optional) a URL, no two services
    with the same `id`; `type` a string or a set of strings;
    `serviceEndpoint` a string, a map, or a non-empty set of strings and
    maps, each string a URL. (§2.1.4 also says "Each service map MUST
    contain id", and then "The id property is OPTIONAL"; Example 6 has no
    `id`. The optional reading is the one here; see the design record.)
  * §2.2 `verificationMethod`: a set of maps. Each map: `id` a URL, `type` a
    string, `controller` a URL, `expires` and `revoked` (optional) XML
    Schema `dateTimeStamp` strings (a time zone is required).
  * §2.2.1: at most one verification material property for the same
    material (`publicKeyJwk` and `publicKeyMultibase` together are refused).
  * §2.2.2 `Multikey`: `publicKeyMultibase` a Multibase value with a public
    header of the §2.2.2 table and the key length of that type
    (`CID.decodePublicMultikey`); a secret-key header is an error.
  * §2.2.3 `JsonWebKey`: `publicKeyJwk` a map with a `kty` string (RFC 7517
    §4.1), and no member of the "Private" class (`d`, the RSA CRT members,
    `k` of `oct`, `priv`).
  * A controlled identifier document is public. `secretKeyMultibase` and
    `secretKeyJwk` "MUST NOT be used if the data structure containing it is
    public" (§2.2.3), so either one in a document is an error.
  * §2.3 relationships: when present, a set of one or more entries, each a
    URL string or a verification method map (checked as above).

URLs. "Conforms to the URL syntax" is read as an RFC 3987 IRI reference
(`RDF.isAbsoluteIri`, `RDF.isRelativeIriRef`): the WHATWG "valid URL
string" admits relative references too, and Example 2 uses `#key-20240828`.
A relative reference is resolved against the document's `id` by RFC 3986
§5.2 (`Syntax.resolveIri`) before any comparison.

Every loop over the input is a tail call with an accumulator
(`mapExcept`).
-/
import L4Factoidal.CID.Multiformats
import L4Factoidal.JSON.Parser
import L4Factoidal.RDF.IriSyntax
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.CID

open L4Factoidal.JSON
open L4Factoidal.VC.Multibase (Bytes)

/-! ## Context and media type (§4.2, Appendix A) -/

/-- The JSON-LD context of §4.2. The document is vendored at
`third_party/contexts/cid-v1.jsonld` (SHA-256 `ea216ecc…de85`, as §4.2
states) and never fetched. -/
def contextV1 : String := "https://www.w3.org/ns/cid/v1"

/-- A context with at least the same declarations (§4.2.1). -/
def didContextV1 : String := "https://www.w3.org/ns/did/v1"

/-- The media type of Appendix A.1. -/
def mediaType : String := "application/cid"

/-- The media types a controlled identifier document is accepted in:
`application/cid` (Appendix A.1), and the three types the LWS suites
use today. -/
def acceptedMediaTypes : List String :=
  ["application/cid", "application/cid+json", "application/ld+json", "application/json"]

/-- The `Accept` header of a request for a controlled identifier document. -/
def acceptHeader : String := ", ".intercalate acceptedMediaTypes

/-- Is a `Content-Type` value one of `acceptedMediaTypes` (parameters
dropped, case ignored)? -/
def mediaTypeAccepted (contentType : String) : Bool :=
  let essence := ((contentType.splitOn ";").headD "").trimAscii.toString.toLower
  acceptedMediaTypes.contains essence

/-- §4.2.1 Context Injection: a document with no `@context` gets
`https://www.w3.org/ns/cid/v1` before JSON-LD processing. A document with
an `@context` keeps it. -/
def injectContext (j : Json) : Json :=
  match j with
  | .object fs =>
      if (j.field? "@context").isSome then j else .object (("@context", .string contextV1) :: fs)
  | _ => j

/-! ## URLs -/

/-- An absolute URL. -/
def isUrl (s : String) : Bool := RDF.isAbsoluteIri s

/-- A URL or a relative reference (not empty). -/
def isUrlRef (s : String) : Bool := !s.isEmpty && (RDF.isAbsoluteIri s || RDF.isRelativeIriRef s)

/-- The absolute URL of a reference, against a base (RFC 3986 §5.2). -/
def absolute (base ref : String) : String :=
  if RDF.isAbsoluteIri ref then ref else Syntax.resolveIri base ref

/-- The URL without its fragment. -/
def withoutFragment (u : String) : String := (u.splitOn "#").headD u

/-! ## Verification relationships (§2.3) -/

inductive Relationship where
  | authentication
  | assertionMethod
  | keyAgreement
  | capabilityInvocation
  | capabilityDelegation
  deriving Repr, DecidableEq

def Relationship.name : Relationship → String
  | .authentication => "authentication"
  | .assertionMethod => "assertionMethod"
  | .keyAgreement => "keyAgreement"
  | .capabilityInvocation => "capabilityInvocation"
  | .capabilityDelegation => "capabilityDelegation"

def Relationship.all : List Relationship :=
  [.authentication, .assertionMethod, .keyAgreement, .capabilityInvocation, .capabilityDelegation]

/-- The relationship a property name (a Data Integrity `proofPurpose`) names. -/
def Relationship.ofName? (s : String) : Option Relationship := Relationship.all.find? (·.name == s)

/-! ## The data model -/

/-- The verification material of a method (§2.2.1). -/
inductive Material where
  /-- A `Multikey` public key (§2.2.2): its type and the key bytes after the header. -/
  | multikey (kt : KeyType) (key : Bytes)
  /-- `publicKeyMultibase` of a method type that this specification does
  not define, as written (a valid Multibase value). -/
  | multibase (value : String)
  /-- `publicKeyJwk` (§2.2.3): a map with `kty` and no private member. -/
  | jwk (j : Json)
  /-- No verification material (both properties are OPTIONAL). -/
  | none
  deriving Repr, DecidableEq

/-- A verification method (§2.2). `id` and `controller` are as written;
`absolute` resolves them. -/
structure Method where
  id : String
  type : String
  controller : String
  expires : Option String
  revoked : Option String
  material : Material
  json : Json
  deriving Repr, DecidableEq

/-- An entry of a verification relationship (§2.2.4): a reference or an
embedded method. -/
inductive Entry where
  | ref (url : String)
  | embedded (m : Method)
  deriving Repr, DecidableEq

/-- A service (§2.1.4). -/
structure Service where
  id : Option String
  types : List String
  endpoint : Json
  deriving Repr, DecidableEq

/-- A conforming controlled identifier document. -/
structure Document where
  id : String
  controllers : List String
  alsoKnownAs : List String
  services : List Service
  methods : List Method
  relationships : List (Relationship × List Entry)
  json : Json
  deriving Repr, DecidableEq

/-! ## Errors: one per MUST of §2 -/

inductive DocError where
  /-- The text is not JSON. -/
  | notJson
  /-- The document is not a map. -/
  | notMap
  /-- §2.1.1: "MUST contain an id value in the topmost map". -/
  | idMissing
  /-- §2.1.1: `id` "MUST be a string that conforms to the rules in the URL Standard". -/
  | idNotUrl
  /-- §2.1.2: a string or a set of strings, each a URL. -/
  | controllerInvalid
  /-- §2.1.3: a set of URIs. -/
  | alsoKnownAsInvalid
  /-- §2.1.4: `service` "MUST be a set of services". -/
  | serviceNotSet
  /-- §2.1.4: "each service is described by a map". -/
  | serviceNotMap
  /-- §2.1.4: service `id` "MUST be a URL". -/
  | serviceIdInvalid
  /-- §2.1.4: "MUST NOT include multiple service entries with the same id". -/
  | serviceIdDuplicate (id : String)
  /-- §2.1.4: `type` REQUIRED, a string or a set of strings. -/
  | serviceTypeInvalid
  /-- §2.1.4: `serviceEndpoint` REQUIRED, a string, a map or a set of them; strings are URLs. -/
  | serviceEndpointInvalid
  /-- §2.2: `verificationMethod` "MUST be a set of verification methods". -/
  | verificationMethodNotSet
  /-- §2.2: "each verification method is expressed using a map". -/
  | methodNotMap
  /-- §2.2: method `id` a URL. -/
  | methodIdInvalid
  /-- §2.2: method `type` a string. -/
  | methodTypeInvalid (id : String)
  /-- §2.2: method `controller` a URL. -/
  | methodControllerInvalid (id : String)
  /-- §2.2: `expires` a `dateTimeStamp`. -/
  | methodExpiresInvalid (id : String)
  /-- §2.2: `revoked` a `dateTimeStamp`. -/
  | methodRevokedInvalid (id : String)
  /-- §2.2.1: "MUST NOT contain multiple verification material properties for the same material". -/
  | methodMultipleMaterial (id : String)
  /-- §2.2.2, §2.2.3: the material property is not the one the type defines. -/
  | methodMaterialMismatch (id type prop : String)
  /-- §2.2.2: `publicKeyMultibase` of a `Multikey`. -/
  | multikeyInvalid (id : String) (e : MultikeyError)
  /-- §2.2.2: `publicKeyMultibase` "MUST be a Multibase encoded value". -/
  | multibaseInvalid (id : String)
  /-- §2.2.3: `publicKeyJwk` "MUST be a map representing a JSON Web Key". -/
  | jwkInvalid (id : String)
  /-- §2.2.3: "MUST NOT include any members of the private information class". -/
  | jwkPrivateMember (id member : String)
  /-- §2.2.3: secret key material in a public document. -/
  | secretMaterial (id prop : String)
  /-- §2.3: the relationship value "MUST be a set". -/
  | relationshipNotSet (r : Relationship)
  /-- §2.3: "a set of one or more verification methods". -/
  | relationshipEmpty (r : Relationship)
  /-- §2.3: an entry that is neither a URL nor a verification method map. -/
  | relationshipEntryInvalid (r : Relationship)
  deriving Repr, DecidableEq

def DocError.describe : DocError → String
  | .notJson => "the controlled identifier document is not JSON"
  | .notMap => "the controlled identifier document is not a map"
  | .idMissing => "the controlled identifier document has no id"
  | .idNotUrl => "the id of the controlled identifier document is not an absolute URL"
  | .controllerInvalid => "controller is not a URL or a set of URLs"
  | .alsoKnownAsInvalid => "alsoKnownAs is not a set of URIs"
  | .serviceNotSet => "service is not a set"
  | .serviceNotMap => "a service is not a map"
  | .serviceIdInvalid => "a service id is not a URL"
  | .serviceIdDuplicate i => s!"two services have the id {i}"
  | .serviceTypeInvalid => "a service type is not a string or a set of strings"
  | .serviceEndpointInvalid => "a serviceEndpoint is not a URL, a map, or a set of them"
  | .verificationMethodNotSet => "verificationMethod is not a set"
  | .methodNotMap => "a verification method is not a map"
  | .methodIdInvalid => "a verification method id is not a URL"
  | .methodTypeInvalid i => s!"verification method {i} has no type string"
  | .methodControllerInvalid i => s!"the controller of verification method {i} is not a URL"
  | .methodExpiresInvalid i => s!"expires of verification method {i} is not a dateTimeStamp"
  | .methodRevokedInvalid i => s!"revoked of verification method {i} is not a dateTimeStamp"
  | .methodMultipleMaterial i => s!"verification method {i} has both publicKeyJwk and publicKeyMultibase"
  | .methodMaterialMismatch i t p => s!"verification method {i} of type {t} has {p}"
  | .multikeyInvalid i e => s!"verification method {i}: {e.describe}"
  | .multibaseInvalid i => s!"publicKeyMultibase of verification method {i} is not a Multibase value"
  | .jwkInvalid i => s!"publicKeyJwk of verification method {i} is not a JSON Web Key"
  | .jwkPrivateMember i m => s!"publicKeyJwk of verification method {i} has the private member {m}"
  | .secretMaterial i p => s!"verification method {i} publishes {p}"
  | .relationshipNotSet r => s!"{r.name} is not a set"
  | .relationshipEmpty r => s!"{r.name} is an empty set"
  | .relationshipEntryInvalid r => s!"an entry of {r.name} is neither a URL nor a verification method"

/-! ## Checks -/

/-- Map every element, stopping at the first error. A tail call with an
accumulator. -/
def mapExcept {α β ε : Type} (f : α → Except ε β) : List α → List β → Except ε (List β)
  | [], acc => .ok acc.reverse
  | a :: as, acc =>
      match f a with
      | .error e => .error e
      | .ok b => mapExcept f as (b :: acc)

/-- Is the string an XML Schema 1.1 `dateTimeStamp` (a `dateTime` with a time zone)? -/
def isDateTimeStamp (s : String) : Bool :=
  match XSD.parseDateTimeLex .dateTime s with
  | some v => v.tz.isSome
  | none => false

/-- The instant of a `dateTimeStamp`, in seconds since 1970-01-01T00:00:00Z. -/
def dateTimeStampSeconds? (s : String) : Option XSD.Dec :=
  match XSD.parseDateTimeLex .dateTime s with
  | some v => if v.tz.isSome then some (XSD.timeOnTimeline v) else none
  | none => none

/-- The member names of the JOSE "Private" information class: `d` (EC, OKP,
RSA), the RSA CRT members, `k` (`oct`), and `priv` (AKP). -/
def jwkPrivateMembers : List String := ["d", "p", "q", "dp", "dq", "qi", "oth", "k", "priv"]

/-- The secret-key properties of §2.2.2 and §2.2.3. -/
def secretProps : List String := ["secretKeyMultibase", "secretKeyJwk"]

/-- §2.2.3: `publicKeyJwk`. -/
def checkJwk (id : String) (j : Json) : Except DocError Json :=
  match j with
  | .object _ =>
      match j.field? "kty" with
      | some (.string _) =>
          match jwkPrivateMembers.find? (fun n => (j.field? n).isSome) with
          | some n => .error (.jwkPrivateMember id n)
          | none => .ok j
      | _ => .error (.jwkInvalid id)
  | _ => .error (.jwkInvalid id)

/-- The verification material of a method of type `ty` (§2.2.1–§2.2.3). -/
def parseMaterial (id ty : String) (j : Json) : Except DocError Material :=
  match j.field? "publicKeyMultibase", j.field? "publicKeyJwk" with
  | some _, some _ => .error (.methodMultipleMaterial id)
  | some mb, none =>
      if ty == "JsonWebKey" then .error (.methodMaterialMismatch id ty "publicKeyMultibase")
      else match mb with
        | .string s =>
            if ty == "Multikey" then
              match decodePublicMultikey s with
              | .ok (kt, key) => .ok (.multikey kt key)
              | .error e => .error (.multikeyInvalid id e)
            else if isMultibase s then .ok (.multibase s)
            else .error (.multibaseInvalid id)
        | _ => .error (.multibaseInvalid id)
  | none, some k =>
      if ty == "Multikey" then .error (.methodMaterialMismatch id ty "publicKeyJwk")
      else (checkJwk id k).map .jwk
  | none, none => .ok .none

/-- An optional `dateTimeStamp` property. -/
def timeProp (j : Json) (name : String) (err : DocError) : Except DocError (Option String) :=
  match j.field? name with
  | none => .ok none
  | some (.string t) => if isDateTimeStamp t then .ok (some t) else .error err
  | some _ => .error err

/-- A verification method map (§2.2, §2.2.1–§2.2.3). -/
def parseMethod (j : Json) : Except DocError Method :=
  match j with
  | .object _ =>
      match j.field? "id" with
      | some (.string id) =>
          if !isUrlRef id then .error .methodIdInvalid
          else match j.field? "type" with
            | some (.string ty) =>
                match j.field? "controller" with
                | some (.string ctl) =>
                    if !isUrlRef ctl then .error (.methodControllerInvalid id)
                    else match timeProp j "expires" (.methodExpiresInvalid id),
                               timeProp j "revoked" (.methodRevokedInvalid id) with
                      | .error e, _ => .error e
                      | _, .error e => .error e
                      | .ok expires, .ok revoked =>
                          match secretProps.find? (fun p => (j.field? p).isSome) with
                          | some p => .error (.secretMaterial id p)
                          | none =>
                              match parseMaterial id ty j with
                              | .error e => .error e
                              | .ok material =>
                                  .ok { id, type := ty, controller := ctl, expires, revoked,
                                        material, json := j }
                | _ => .error (.methodControllerInvalid id)
            | _ => .error (.methodTypeInvalid id)
      | _ => .error .methodIdInvalid
  | _ => .error .methodNotMap

/-- A string or a set of strings, each satisfying `ok`. -/
def stringOrSet (ok : String → Bool) : Json → Option (List String)
  | .string s => if ok s then some [s] else none
  | .array xs =>
      let ss := xs.filterMap Json.asString?
      if ss.length == xs.length && ss.all ok then some ss else none
  | _ => none

/-- A `serviceEndpoint` value (§2.1.4). -/
def endpointOk : Json → Bool
  | .string s => isUrlRef s
  | .object _ => true
  | .array xs =>
      !xs.isEmpty && xs.all fun x =>
        match x with
        | .string s => isUrlRef s
        | .object _ => true
        | _ => false
  | _ => false

/-- A service map (§2.1.4). -/
def parseService (j : Json) : Except DocError Service :=
  match j with
  | .object _ =>
      let idE : Except DocError (Option String) := match j.field? "id" with
        | none => .ok none
        | some (.string s) => if isUrlRef s then .ok (some s) else .error .serviceIdInvalid
        | some _ => .error .serviceIdInvalid
      match idE with
      | .error e => .error e
      | .ok id =>
          match (j.field? "type").bind (stringOrSet (fun _ => true)) with
          | none => .error .serviceTypeInvalid
          | some types =>
              match j.field? "serviceEndpoint" with
              | some ep => if endpointOk ep then .ok { id, types, endpoint := ep } else .error .serviceEndpointInvalid
              | none => .error .serviceEndpointInvalid
  | _ => .error .serviceNotMap

/-- The first id that occurs twice, scanning with the ids seen so far. -/
def firstDuplicate : List String → List String → Option String
  | [], _ => none
  | x :: xs, seen => if seen.contains x then some x else firstDuplicate xs (x :: seen)

/-- One relationship entry (§2.2.4). -/
def parseEntry (r : Relationship) (j : Json) : Except DocError Entry :=
  match j with
  | .string s => if isUrlRef s then .ok (.ref s) else .error (.relationshipEntryInvalid r)
  | .object _ => (parseMethod j).map .embedded
  | _ => .error (.relationshipEntryInvalid r)

/-- One relationship property, if present (§2.3). -/
def parseRelationship (doc : Json) (r : Relationship) : Except DocError (Relationship × List Entry) :=
  match doc.field? r.name with
  | none => .ok (r, [])
  | some (.array []) => .error (.relationshipEmpty r)
  | some (.array xs) => (mapExcept (parseEntry r) xs []).map (r, ·)
  | some _ => .error (.relationshipNotSet r)

/-- Parse and check a controlled identifier document (§2). -/
def parseDocument (j : Json) : Except DocError Document := do
  match j with
  | .object _ => pure ()
  | _ => throw .notMap
  let id ← match j.field? "id" with
    | none => throw .idMissing
    | some (.string s) => if isUrl s then pure s else throw .idNotUrl
    | some _ => throw .idNotUrl
  let controllers ← match j.field? "controller" with
    | none => pure []
    | some c => match stringOrSet isUrlRef c with
      | some cs => pure cs
      | none => throw .controllerInvalid
  let alsoKnownAs ← match j.field? "alsoKnownAs" with
    | none => pure []
    | some (.array xs) =>
        let ss := xs.filterMap Json.asString?
        if ss.length == xs.length && ss.all isUrl then pure ss else throw .alsoKnownAsInvalid
    | some _ => throw .alsoKnownAsInvalid
  let services ← match j.field? "service" with
    | none => pure []
    | some (.array xs) => mapExcept parseService xs []
    | some _ => throw .serviceNotSet
  match firstDuplicate (services.filterMap fun s => s.id.map (absolute id)) [] with
  | some d => throw (.serviceIdDuplicate d)
  | none => pure ()
  let methods ← match j.field? "verificationMethod" with
    | none => pure []
    | some (.array xs) => mapExcept parseMethod xs []
    | some _ => throw .verificationMethodNotSet
  let relationships ← mapExcept (parseRelationship j) Relationship.all []
  pure { id, controllers, alsoKnownAs, services, methods, relationships, json := j }

/-- Parse the text of a controlled identifier document. -/
def parseDocumentText (text : String) : Except DocError Document :=
  match parseJson? text with
  | some j => parseDocument j
  | none => .error .notJson

/-! ## Relationships (§2.3, §2.2.4) -/

/-- The entries of one relationship. -/
def Document.entries (d : Document) (r : Relationship) : List Entry :=
  ((d.relationships.find? (·.1 == r)).map (·.2)).getD []

/-- The absolute URL an entry names. -/
def Entry.url (base : String) : Entry → String
  | .ref u => absolute base u
  | .embedded m => absolute base m.id

/-- Is the method `vmId` associated with the relationship, by reference
or by value (§3.3)? -/
def Document.associated (d : Document) (r : Relationship) (vmId : String) : Bool :=
  (d.entries r).any (fun e => e.url d.id == vmId)

/-- A method of a relationship: defined in this document, or a reference
to a method of another document (which §3.3 retrieves from there). -/
inductive Resolved where
  | method (m : Method)
  | external (url : String)
  deriving Repr, DecidableEq

/-- `relationship(doc, purpose)`: the methods a verification relationship
names (§2.3). An embedded method is itself; a reference into this
document is the method of `verificationMethod` or of a relationship with
that absolute `id`; a reference into another document is `external`. A
reference into this document that names no method is dropped: "If a
referenced verification method definition is not in the latest controlled
identifier document used to dereference it, then that verification method
is considered invalid or revoked" (§2.3). -/
def relationship (d : Document) (r : Relationship) : List Resolved :=
  let defined := d.methods ++ Relationship.all.flatMap fun r' =>
    (d.entries r').filterMap fun e => match e with
      | .embedded m => some m
      | .ref _ => none
  (d.entries r).filterMap fun e =>
    match e with
    | .embedded m => some (.method m)
    | .ref u =>
        let a := absolute d.id u
        if withoutFragment a == d.id then
          (defined.find? (fun m => absolute d.id m.id == a)).map .method
        else some (.external a)

/-! ## Expiry and revocation (§2.2) -/

/-- Is the method in force at `now` (seconds since the epoch)? A method is
not used "at or after the time of expiration" or of revocation (§2.2). -/
def methodInForce (now : Int) (m : Method) : Bool :=
  [m.expires, m.revoked].all fun t =>
    match t with
    | none => true
    | some s =>
        match dateTimeStampSeconds? s with
        | some at_ => XSD.Dec.cmp (XSD.Dec.ofInt now) at_ == .lt
        | none => false

/-- §2.2.3 RECOMMENDED: the `kid` of a `publicKeyJwk` is the fragment of
the method `id` (or is in its path or query). `true` when there is no
`kid`. A SHOULD, so a lint and not an error. -/
def kidConsistent (m : Method) : Bool :=
  match m.material with
  | .jwk j =>
      match j.getString? "kid" with
      | some k => ((m.id.splitOn k).length > 1)
      | none => true
  | _ => true

/-! ## Theorems -/

/-- A parsed method has no secret-key property. -/
theorem parseMethod_no_secret {j : Json} {m : Method} (h : parseMethod j = .ok m) :
    m.json = j ∧ secretProps.find? (fun p => (j.field? p).isSome) = none := by
  unfold parseMethod at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h
  · simp at h
  · split at h <;> try simp at h
    split at h <;> try simp at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp at h
      · split at h
        · simp at h
        · rename_i hs
          split at h
          · simp at h
          · simp only [Except.ok.injEq] at h
            subst h
            exact ⟨rfl, hs⟩

/-- A `publicKeyJwk` that passed `checkJwk` has no private member. -/
theorem checkJwk_no_private {id : String} {j k : Json} (h : checkJwk id j = .ok k) :
    k = j ∧ jwkPrivateMembers.find? (fun n => (j.field? n).isSome) = none := by
  unfold checkJwk at h
  split at h
  · split at h
    · split at h
      · simp at h
      · rename_i hn
        simp only [Except.ok.injEq] at h
        exact ⟨h.symm, hn⟩
    · simp at h
  · simp at h

end L4Factoidal.CID
