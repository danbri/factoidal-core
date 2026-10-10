/-
L4Factoidal.VC.Context — the JSON-LD contexts a Verifiable Credential
and its Data Integrity proof resolve against, and the loader that
serves them OFFLINE.

The first half of this module is NOT a port of `formal/fstar/VC.Context.fst`.
The Lean tree has a full JSON-LD 1.1 processor (`JSONLD/`), so the
contexts of the Data Integrity pipeline are consumed by the real
algorithm; what that half supplies is the DATA the F* tree keeps in
`bin/vc-api-shim/server.mjs` and `bin/vc-runner/vc_runner.ml`:

  * which vendored context file answers which context IRI
    (`third_party/contexts/`, provenance and licence in its
    `PROVENANCE.md`; the W3C `did/v1`, `multikey/v1`, `ed25519-2020/v1`
    contexts come from `third_party/jsonld-context-cache/`, see the
    `jsonld-context-cache` skill);
  * the proof-options context rule of the shim's `proofContextFor`: a
    proof's canonical form needs the Data Integrity vocabulary
    (`DataIntegrityProof`, `cryptosuite`, `verificationMethod`,
    `proofPurpose`, `created`, `proofValue`). VCDM 2.0's base context
    defines it (scoped under `VerifiableCredential`/`proof`); the VCDM
    1.1 base context does not, and JSON-LD DROPS undefined terms
    silently, which would produce a truncated, non-interoperable
    signature input. So the proof options get
    `https://w3id.org/security/data-integrity/v2` appended unless the
    document's context already carries VCDM 2.0 or that context
    (appending it ON TOP of VCDM 2.0 redefines protected terms and the
    processor rightly rejects the document).

The loader is a PARAMETER, as throughout the JSON-LD port: this module
only maps IRIs to file names and builds a `Loader` from bodies that the
executable read in `IO` (`Harness/VcProbe.lean`). No file system access
here; no empty-context fallback anywhere (a theorem of the JSON-LD
stage, `contextProcess_string_none_loader`).

The second half, "Type-value term resolution", IS a port of
`VC.Context.fst`: the purpose-built term-resolution walker that the
structural validator `VC/Credential.lean` (`Doc.checkDocument`) runs over a
credential's own `@context` array to decide whether each `type` value
resolves (protected-term redefinition, non-URL type mappings, `@vocab: null`).
It is a deliberately narrow, offline walker and not a JSON-LD context
processor: it reads term definitions out of the vendored VCDM 2.0 base
context data and out of inline contexts, and nothing else.
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JSONLD.Loader

namespace L4Factoidal.VC.Context

open L4Factoidal.JSON
open L4Factoidal.JSONLD

/-- VCDM 2.0 base context IRI. -/
def vcV2ContextIri : String := "https://www.w3.org/ns/credentials/v2"

/-- Data Integrity v2 context IRI. -/
def dataIntegrityV2ContextIri : String := "https://w3id.org/security/data-integrity/v2"

/-- Context IRI → file name under `third_party/contexts/` (the mapping
recorded in that directory's `PROVENANCE.md`). -/
def vendoredContextFiles : List (String × String) := [
  (vcV2ContextIri, "credentials-v2.jsonld"),
  ("https://www.w3.org/ns/credentials/examples/v2", "credentials-examples-v2.jsonld"),
  (dataIntegrityV2ContextIri, "security-data-integrity-v2.jsonld"),
  ("https://w3id.org/security/multikey/v1", "security-multikey-v1.jsonld"),
  ("https://www.w3.org/2018/credentials/v1", "credentials-v1.jsonld") ]

/-- A loader over an `(IRI, body)` table the caller has read from disk —
`vendoredContextFiles` resolved, plus whatever the context cache holds. -/
def vcLoader (bodies : List (String × String)) : Loader := tableLoader bodies

/-- Does a `@context` value (string or array) name this IRI? -/
def contextIncludes (ctx : Json) (iri : String) : Bool :=
  match ctx with
  | .string s => s == iri
  | .array items => items.any (fun i => match i with | .string s => s == iri | _ => false)
  | _ => false

/-- The `@context` a proof-options document is canonicalised under
(module header): the securing document's own context, with the Data
Integrity v2 context appended unless VCDM 2.0 or that context is
already listed. Always an array. -/
def proofContextFor (docContext : Option Json) : Json :=
  let base : List Json := match docContext with
    | some (.array items) => items
    | some (.null) => []
    | some j => [j]
    | none => []
  let ctx := Json.array base
  if contextIncludes ctx vcV2ContextIri || contextIncludes ctx dataIntegrityV2ContextIri then ctx
  else Json.array (base ++ [Json.string dataIntegrityV2ContextIri])

/-! ## Type-value term resolution (port of `VC.Context.fst`)

Reference: VC Data Model 2.0, W3C Recommendation 2025-05-15
(https://www.w3.org/TR/vc-data-model-2.0/); JSON-LD 1.1, W3C Recommendation
2020-07-16, §4.1.10 Protected Term Definitions.

The walker answers three questions about a document's own `@context` array:

 1. Does an inline context REDEFINE a PROTECTED term (one the base VCDM 2.0
    context, or an earlier `"@protected": true` inline context, already
    defined) with a DIFFERENT mapping? JSON-LD 1.1 forbids it.
 2. Does a `type` value that is a defined TERM map to a NON-URL IRI?
 3. Is a `type` value UNMAPPED, that is not a URL, not a defined term, and
    out of reach of any `@vocab` fallback because `{"@vocab": null}`
    nullified it, with no unknown remote context that could still define it?

Conservative choices, each kept so that no `-ok` fixture of the VCDM 2.0 test
suite is rejected:

  * An unknown remote context (any `@context` string other than the VCDM 2.0
    base IRI) "could define anything". A `type` value that cannot be resolved
    otherwise is not flagged when one is present.
  * An unmapped `type` term is flagged ONLY when `@vocab` was set to `null`
    explicitly and no unknown remote context is present. A merely absent
    `@vocab` never triggers it.
  * "URL-shaped" means "contains `:` and no space", the predicate
    `Doc.looksLikeIri` of `Credential.lean` uses, and not a full IRI parse. -/

/-- A resolved term definition: the IRI it maps to (`none` for a keyword or
for an object without a plain string `@id`), and whether redefining it with a
different mapping is an error. -/
structure TermDef where
  iri         : Option String
  isProtected : Bool

/-- What `@vocab` was set to: never, to `null`, or to a string. -/
inductive VocabState where
  | unset
  | null
  | set (vocab : String)

/-- The accumulated context state. Newest definitions are PREPENDED, so the
first match wins in `lookupTerm`. -/
structure State where
  terms         : List (String × TermDef)
  vocab         : VocabState
  unknownRemote : Bool

/-- A processing step: an updated state, or a protected-term violation. -/
inductive Step where
  | ok (st : State)
  | violation (reason : String)

/-- The final verdict on the `type` values. -/
inductive TypeResult where
  | ok
  | violation (reason : String)
deriving Repr, DecidableEq, Inhabited

/-- "URL-shaped": contains `:` and no space. -/
def isUrlShaped (s : String) : Bool :=
  s.toList.contains ':' && !(s.toList.contains ' ')

/-- A context map key that is a JSON-LD keyword (leading `@`). -/
def isKeywordKey (k : String) : Bool :=
  match k.toList with
  | '@' :: _ => true
  | _ => false

private def fieldLookup (fields : List (String × Json)) (k : String) : Option Json :=
  (fields.find? (fun f => f.1 == k)).map (·.2)

/-- The IRI a term-definition value maps to. -/
def termIriOfValue : Json → Option String
  | .string s => some s
  | .object fields =>
      match fieldLookup fields "@id" with
      | some (.string s) => some s
      | _ => none
  | _ => none

/-- Is the context object marked `"@protected": true`? -/
def objProtected (fields : List (String × Json)) : Bool :=
  match fieldLookup fields "@protected" with
  | some (.bool b) => b
  | _ => false

/-- A context object's fields as term definitions, keyword keys skipped. -/
def termsOfFields (isProt : Bool) : List (String × Json) → List (String × TermDef)
  | [] => []
  | (k, v) :: tl =>
      if isKeywordKey k then termsOfFields isProt tl
      else (k, { iri := termIriOfValue v, isProtected := isProt }) :: termsOfFields isProt tl

/-- The base VCDM 2.0 term map, read from the vendored context document
(top-level shape `{"@context": {…}}`). -/
def baseTerms (v2ctx : Json) : List (String × TermDef) :=
  match v2ctx.field? "@context" with
  | some (.object fields) => termsOfFields (objProtected fields) fields
  | _ => []

def lookupTerm : List (String × TermDef) → String → Option TermDef
  | [], _ => none
  | (k', d) :: tl, k => if k' == k then some d else lookupTerm tl k

def setTerm (st : State) (k : String) (iri : Option String) (prot : Bool) : State :=
  { st with terms := (k, { iri := iri, isProtected := prot }) :: st.terms }

def applyVocab (cur : VocabState) (fields : List (String × Json)) : VocabState :=
  match fieldLookup fields "@vocab" with
  | some .null => .null
  | some (.string s) => .set s
  | _ => cur

/-- Fold one inline context object's term definitions into the state. A key
that is already protected, redefined with a DIFFERENT IRI, is a violation;
restating it with the same mapping, or defining a new or unprotected term,
updates the map. A term is protected afterwards iff this object is protected
or its prior binding was. -/
def applyTerms (objProt : Bool) (st : State) : List (String × Json) → Step
  | [] => .ok st
  | (k, v) :: tl =>
      if isKeywordKey k then applyTerms objProt st tl
      else
        let newIri := termIriOfValue v
        match lookupTerm st.terms k with
        | some d =>
            if d.isProtected && d.iri != newIri then
              .violation ("redefinition of protected term '" ++ k ++ "'")
            else applyTerms objProt (setTerm st k newIri (objProt || d.isProtected)) tl
        | none => applyTerms objProt (setTerm st k newIri objProt) tl

def applyInline (st : State) (fields : List (String × Json)) : Step :=
  let prot := objProtected fields
  applyTerms prot { st with vocab := applyVocab st.vocab fields } fields

/-- Process the document's own `@context` entries in order. The base context
loads the vendored term map; any other string is an unknown remote context. -/
def processEntries (base : List (String × TermDef)) (st : State) : List Json → Step
  | [] => .ok st
  | e :: tl =>
      match e with
      | .string s =>
          if s == vcV2ContextIri then
            processEntries base { st with terms := base ++ st.terms } tl
          else processEntries base { st with unknownRemote := true } tl
      | .object fields =>
          match applyInline st fields with
          | .violation r => .violation r
          | .ok st' => processEntries base st' tl
      | _ => processEntries base st tl

def buildState (v2ctx doc : Json) : Step :=
  let base := baseTerms v2ctx
  let st0 : State := { terms := [], vocab := .unset, unknownRemote := false }
  match doc.field? "@context" with
  | some (.array entries) => processEntries base st0 entries
  | some (.string s) => processEntries base st0 [.string s]
  | _ => .ok st0

/-- Resolve one `type` value against the built state. -/
def resolveType (st : State) (t : String) : TypeResult :=
  if isUrlShaped t then .ok
  else
    match lookupTerm st.terms t with
    | some d =>
        match d.iri with
        | some m =>
            if isUrlShaped m then .ok
            else .violation ("type term '" ++ t ++ "' is mapped to a non-URL IRI")
        | none => .ok
    | none =>
        match st.vocab with
        | .null =>
            if st.unknownRemote then .ok
            else .violation ("type term '" ++ t ++ "' is unmapped (no term definition; @vocab nullified)")
        | _ => .ok

def resolveTypes (st : State) : List String → TypeResult
  | [] => .ok
  | t :: tl =>
      match resolveType st t with
      | .ok => resolveTypes st tl
      | v => v

/-- Build the context state from the vendored VCDM 2.0 context and the
document, then resolve every declared `type` value. Port of
`vcx_check_types`. -/
def checkTypes (v2ctx doc : Json) (typeValues : List String) : TypeResult :=
  match buildState v2ctx doc with
  | .violation r => .violation r
  | .ok st => resolveTypes st typeValues

end L4Factoidal.VC.Context
