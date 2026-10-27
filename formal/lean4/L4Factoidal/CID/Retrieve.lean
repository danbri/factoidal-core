/-
L4Factoidal.CID.Retrieve — Controlled Identifiers v1.0 §3.3 Retrieve
Verification Method, §3.4 Fragment Resolution and §3.5 Processing Errors
(https://www.w3.org/TR/cid-1.0/; https://github.com/danbri/factoidal/issues/1100,
items 3 and 6).

## Who fetches

§3.3 step 4 dereferences the controller document URL. The engine does no
I/O (iron rule 7). `documentUrlOf` computes the URL to fetch (steps 1–3);
the caller fetches it, with its own guard (the authorization server uses
`Authz.lookup`: https only, no private address); `retrieveFromDocument`
runs steps 5–12 on what came back. `retrieveWith` does both over a table of
documents the host has already fetched and answers `need url` for a
document it does not have, so the host loop is: call, fetch what is named,
call again.

## The checks, in the order of §3.3

1. `vmIdentifier` is not a valid (absolute) URL: INVALID_VERIFICATION_METHOD_URL.
2–3. The document URL is `vmIdentifier` without its fragment; the fragment is the rest.
5. The document is not conforming (`parseDocument`):
   INVALID_CONTROLLED_IDENTIFIER_DOCUMENT.
6. Its `id` is not the document URL: INVALID_CONTROLLED_IDENTIFIER_DOCUMENT_ID.
7. Fragment Resolution (§3.4) finds the map.
8. No map, or the map is not a conforming verification method:
   INVALID_VERIFICATION_METHOD.
9. The absolute `id` of the method is not `vmIdentifier`: INVALID_VERIFICATION_METHOD.
10. The absolute `controller` of the method is not the document URL:
    INVALID_VERIFICATION_METHOD.
11. The relationship does not name the method, by reference or by value:
    INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD.

`retrieveFromDocument_sound` states what an `ok` answer established.

Expiry and revocation are not steps of §3.3; a caller that verifies a
proof also checks `methodInForce` (§2.2).
-/
import L4Factoidal.CID.Document

namespace L4Factoidal.CID

open L4Factoidal.JSON

/-! ## §3.4 Fragment Resolution -/

/-- Does a map have an `id` equal to the fully qualified fragment or to
the fragment? -/
def idMatches (fq frag : String) (fs : List (String × Json)) : Bool :=
  match (Json.object fs).getString? "id" with
  | some i => i == fq || i == frag
  | none => false

/-- Depth-first, document order: the map itself, then its members in
order. A work list and a fuel bound (the size of the document), so the
loop is a tail call. -/
def fragmentLoop (fq frag : String) : Nat → List Json → Option Json
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, j :: rest =>
      match j with
      | .object fs =>
          if idMatches fq frag fs then some j
          else fragmentLoop fq frag n (fs.map (·.2) ++ rest)
      | .array xs => fragmentLoop fq frag n (xs ++ rest)
      | _ => fragmentLoop fq frag n rest

/-- §3.4: the map in `document` whose `id` is `document.id` followed by
`fragment`, or `fragment` itself. `fragment` includes the `#`. -/
def resolveFragment (document : Json) (fragment : String) : Option Json :=
  let canonical := (document.getString? "id").getD ""
  fragmentLoop (canonical ++ fragment) fragment (Json.sizeFast document + 1) [document]

/-! ## §3.5 Processing Errors -/

/-- Why a map is not the verification method §3.3 asked for. -/
inductive MethodProblem where
  /-- No map has the fragment as its `id`. -/
  | notFound
  /-- The map is not a conforming verification method. -/
  | notConforming (e : DocError)
  /-- The absolute `id` is not `vmIdentifier`. -/
  | idMismatch (got : String)
  /-- The absolute `controller` is not the document URL. -/
  | controllerMismatch (got : String)
  deriving Repr, DecidableEq

/-- The processing errors of §3.5, with what caused them. -/
inductive ProcessingError where
  | invalidVerificationMethodUrl (vm : String)
  | invalidControlledIdentifierDocument (e : DocError)
  | invalidControlledIdentifierDocumentId (got expected : String)
  | invalidVerificationMethod (p : MethodProblem)
  | invalidRelationshipForVerificationMethod (r : Relationship)
  deriving Repr, DecidableEq

/-- The §3.5 name. -/
def ProcessingError.name : ProcessingError → String
  | .invalidVerificationMethodUrl _ => "INVALID_VERIFICATION_METHOD_URL"
  | .invalidControlledIdentifierDocument _ => "INVALID_CONTROLLED_IDENTIFIER_DOCUMENT"
  | .invalidControlledIdentifierDocumentId _ _ => "INVALID_CONTROLLED_IDENTIFIER_DOCUMENT_ID"
  | .invalidVerificationMethod _ => "INVALID_VERIFICATION_METHOD"
  | .invalidRelationshipForVerificationMethod _ => "INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD"

/-- §3.5: "The type value of the error object MUST be a URL that starts
with the value https://w3id.org/security# and ends with the value in the
section listed below." -/
def ProcessingError.typeUrl (e : ProcessingError) : String := "https://w3id.org/security#" ++ e.name

def ProcessingError.title : ProcessingError → String
  | .invalidVerificationMethodUrl _ => "The verification method URL is malformed"
  | .invalidControlledIdentifierDocument _ => "The controlled identifier document is malformed"
  | .invalidControlledIdentifierDocumentId _ _ => "The controlled identifier document id is wrong"
  | .invalidVerificationMethod _ => "The verification method is malformed"
  | .invalidRelationshipForVerificationMethod _ =>
      "The verification method is not in the expected verification relationship"

def ProcessingError.detail : ProcessingError → String
  | .invalidVerificationMethodUrl vm => s!"{vm} is not an absolute URL"
  | .invalidControlledIdentifierDocument e => e.describe
  | .invalidControlledIdentifierDocumentId got exp =>
      s!"the document retrieved from {exp} has the id {got}"
  | .invalidVerificationMethod .notFound => "the document has no map with that fragment as its id"
  | .invalidVerificationMethod (.notConforming e) => e.describe
  | .invalidVerificationMethod (.idMismatch got) => s!"the method id resolves to {got}"
  | .invalidVerificationMethod (.controllerMismatch got) =>
      s!"the method controller resolves to {got}, not to the document URL"
  | .invalidRelationshipForVerificationMethod r => s!"{r.name} does not name the method"

/-- The RFC 9457 problem details object (§3.5). -/
def ProcessingError.problem (e : ProcessingError) : Json :=
  .object [("type", .string e.typeUrl), ("title", .string e.title), ("detail", .string e.detail)]

/-! ## §3.3 Retrieve Verification Method -/

/-- Steps 1–3: the controller document URL and the fragment (with its `#`;
empty when there is none). -/
def documentUrlOf (vmId : String) : Except ProcessingError (String × String) :=
  if !isUrl vmId then .error (.invalidVerificationMethodUrl vmId)
  else match vmId.splitOn "#" with
    | [u] => .ok (u, "")
    | [u, f] => .ok (u, "#" ++ f)
    | _ => .error (.invalidVerificationMethodUrl vmId)

/-- Steps 5–12, on the dereferenced document. -/
def retrieveFromDocument (vmId : String) (rel : Relationship) (document : Json) :
    Except ProcessingError Method :=
  match documentUrlOf vmId with
  | .error e => .error e
  | .ok (docUrl, frag) =>
      match parseDocument document with
      | .error e => .error (.invalidControlledIdentifierDocument e)
      | .ok d =>
          if d.id != docUrl then .error (.invalidControlledIdentifierDocumentId d.id docUrl)
          else match (if frag.isEmpty then none else resolveFragment document frag) with
            | none => .error (.invalidVerificationMethod .notFound)
            | some vmJson =>
                match parseMethod vmJson with
                | .error e => .error (.invalidVerificationMethod (.notConforming e))
                | .ok m =>
                    if absolute d.id m.id != vmId then
                      .error (.invalidVerificationMethod (.idMismatch (absolute d.id m.id)))
                    else if absolute d.id m.controller != docUrl then
                      .error (.invalidVerificationMethod (.controllerMismatch (absolute d.id m.controller)))
                    else if !d.associated rel vmId then
                      .error (.invalidRelationshipForVerificationMethod rel)
                    else .ok m

/-- Steps 5–12 on the text of the document. -/
def retrieveFromText (vmId : String) (rel : Relationship) (text : String) :
    Except ProcessingError Method :=
  match parseJson? text with
  | some j => retrieveFromDocument vmId rel j
  | none => .error (.invalidControlledIdentifierDocument .notJson)

/-- The answer of `retrieveWith`. -/
inductive Retrieval where
  /-- The host must fetch this URL (§3.3 step 4) and call again. -/
  | need (url : String)
  | ok (m : Method)
  | error (e : ProcessingError)
  deriving Repr, DecidableEq

/-- §3.3 over the documents the host has fetched: `(URL, text)` pairs. -/
def retrieveWith (docs : List (String × String)) (vmId : String) (rel : Relationship) : Retrieval :=
  match documentUrlOf vmId with
  | .error e => .error e
  | .ok (u, _) =>
      match docs.find? (·.1 == u) with
      | none => .need u
      | some (_, text) =>
          match retrieveFromText vmId rel text with
          | .ok m => .ok m
          | .error e => .error e

/-! ## Theorems -/

/-- §3.4: Fragment Resolution answers only a map whose `id` is the fully
qualified fragment or the fragment. -/
theorem fragmentLoop_sound {fq frag : String} :
    ∀ (n : Nat) (work : List Json) (r : Json), fragmentLoop fq frag n work = some r →
      ∃ fs, r = .object fs ∧ idMatches fq frag fs = true := by
  intro n
  induction n with
  | zero => intro work r h; simp [fragmentLoop] at h
  | succ n ih =>
      intro work r h
      match work with
      | [] => simp [fragmentLoop] at h
      | j :: rest =>
          simp only [fragmentLoop] at h
          split at h
          · rename_i fs
            split at h
            · rename_i hm
              simp only [Option.some.injEq] at h
              exact ⟨fs, h.symm, hm⟩
            · exact ih _ _ h
          · exact ih _ _ h
          · exact ih _ _ h

theorem resolveFragment_sound {doc : Json} {frag : String} {r : Json}
    (h : resolveFragment doc frag = some r) :
    ∃ fs, r = .object fs ∧ idMatches ((doc.getString? "id").getD "" ++ frag) frag fs = true :=
  fragmentLoop_sound _ _ _ h

/-- The document URL of steps 2–3 is the identifier without its fragment. -/
theorem documentUrlOf_url {vmId u f : String} (h : documentUrlOf vmId = .ok (u, f)) :
    u = withoutFragment vmId := by
  unfold documentUrlOf at h
  split at h
  · simp at h
  · split at h
    · rename_i u' heq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      simp [withoutFragment, heq, h.1]
    · rename_i u' f' heq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      simp [withoutFragment, heq, h.1]
    · simp at h

/-- **What §3.3 established.** A method that `retrieveFromDocument` returns
came from a conforming document whose `id` is the document URL of
`vmId`; it is a conforming verification method; its absolute `id` is
`vmId`; its absolute `controller` is the document URL; the requested
relationship names it; and it has no secret-key property. -/
theorem retrieveFromDocument_sound {vmId : String} {rel : Relationship} {doc : Json} {m : Method}
    (h : retrieveFromDocument vmId rel doc = .ok m) :
    ∃ docUrl frag d,
      documentUrlOf vmId = .ok (docUrl, frag) ∧
      parseDocument doc = .ok d ∧ d.id = docUrl ∧
      parseMethod m.json = .ok m ∧
      absolute d.id m.id = vmId ∧
      absolute d.id m.controller = docUrl ∧
      d.associated rel vmId = true ∧
      secretProps.find? (fun p => (m.json.field? p).isSome) = none := by
  unfold retrieveFromDocument at h
  split at h
  · simp at h
  · rename_i docUrl frag hu
    split at h
    · simp at h
    · rename_i d hd
      split at h
      · simp at h
      · rename_i hid
        split at h
        · simp at h
        · rename_i vmJson _
          split at h
          · simp at h
          · rename_i m' hm
            split at h
            · simp at h
            · rename_i hmid
              split at h
              · simp at h
              · rename_i hctl
                split at h
                · simp at h
                · rename_i hrel
                  simp only [Except.ok.injEq] at h
                  subst h
                  obtain ⟨hj, hs⟩ := parseMethod_no_secret hm
                  refine ⟨docUrl, frag, d, hu, hd, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simpa using hid
                  · rw [hj]; exact hm
                  · simpa using hmid
                  · simpa using hctl
                  · simpa using hrel
                  · rw [hj]; exact hs

/-- `retrieveWith` answers `ok` only through `retrieveFromDocument` on a
document the host fetched from the document URL of `vmId`. -/
theorem retrieveWith_ok {docs : List (String × String)} {vmId : String} {rel : Relationship}
    {m : Method} (h : retrieveWith docs vmId rel = .ok m) :
    ∃ u frag text j, documentUrlOf vmId = .ok (u, frag) ∧ (u, text) ∈ docs ∧
      parseJson? text = some j ∧ retrieveFromDocument vmId rel j = .ok m := by
  unfold retrieveWith at h
  cases hu : documentUrlOf vmId with
  | error e => simp [hu] at h
  | ok p =>
    obtain ⟨u, frag⟩ := p
    simp only [hu] at h
    cases hf : docs.find? (·.1 == u) with
    | none => simp [hf] at h
    | some q =>
      obtain ⟨u', text⟩ := q
      simp only [hf] at h
      cases hr : retrieveFromText vmId rel text with
      | error e => simp [hr] at h
      | ok m' =>
        simp only [hr, Retrieval.ok.injEq] at h
        subst h
        have hmem := List.mem_of_find?_eq_some hf
        have hfst : u' = u := by simpa using List.find?_some hf
        subst hfst
        unfold retrieveFromText at hr
        cases hj : parseJson? text with
        | none => simp [hj] at hr
        | some j =>
          simp only [hj] at hr
          exact ⟨u', frag, text, j, rfl, hmem, hj, hr⟩

end L4Factoidal.CID
