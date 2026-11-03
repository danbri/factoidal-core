/-
L4Factoidal.CID.Validate — the §2 checks of Controlled Identifiers v1.0
(https://www.w3.org/TR/cid-1.0/) as a report: every failed MUST that can be
found, each with its name and the place in the document
(https://github.com/danbri/factoidal/issues/1100, item 9: `cidValidate`).

`parseDocument` (`CID/Document.lean`) stops at the first failed MUST. A
caller who corrects a document wants all of them, and wants to know where
each one is. `check` gives:

  * `valid`: exactly whether `parseDocument` accepts the document
    (`check_valid_iff`). The report never decides validity by itself.
  * `issues`: when not valid, the failures found by checking each member of
    the topmost map, each element of `service`, `verificationMethod` and the
    five relationships separately. The error `parseDocument` stops at is
    always one of them (`check_lists_parse_error`). When valid, no issues
    (`check_valid_no_issues`).

Each issue has the `DocError` (its `code` is the constructor name, its
message `DocError.describe`) and an RFC 6901 JSON Pointer to the member that
failed: `/verificationMethod/2/publicKeyJwk/d`, `/service/0/type`, `/id`.
`""` is the whole document (not JSON, not a map). A duplicate service id is
reported at `/service`, and an invalid `controller` or `alsoKnownAs` at the
member, not at the element.

Every loop is a fold or a tail call with an accumulator.
-/
import L4Factoidal.CID.Document

namespace L4Factoidal.CID

open L4Factoidal.JSON

/-! ## Names and places -/

/-- The name of the error: the constructor name. Stable; the npm function
`cidValidate` answers it as `code`. -/
def DocError.code : DocError → String
  | .notJson => "notJson"
  | .notMap => "notMap"
  | .idMissing => "idMissing"
  | .idNotUrl => "idNotUrl"
  | .controllerInvalid => "controllerInvalid"
  | .alsoKnownAsInvalid => "alsoKnownAsInvalid"
  | .serviceNotSet => "serviceNotSet"
  | .serviceNotMap => "serviceNotMap"
  | .serviceIdInvalid => "serviceIdInvalid"
  | .serviceIdDuplicate _ => "serviceIdDuplicate"
  | .serviceTypeInvalid => "serviceTypeInvalid"
  | .serviceEndpointInvalid => "serviceEndpointInvalid"
  | .verificationMethodNotSet => "verificationMethodNotSet"
  | .methodNotMap => "methodNotMap"
  | .methodIdInvalid => "methodIdInvalid"
  | .methodTypeInvalid _ => "methodTypeInvalid"
  | .methodControllerInvalid _ => "methodControllerInvalid"
  | .methodExpiresInvalid _ => "methodExpiresInvalid"
  | .methodRevokedInvalid _ => "methodRevokedInvalid"
  | .methodMultipleMaterial _ => "methodMultipleMaterial"
  | .methodMaterialMismatch _ _ _ => "methodMaterialMismatch"
  | .multikeyInvalid _ _ => "multikeyInvalid"
  | .multibaseInvalid _ => "multibaseInvalid"
  | .jwkInvalid _ => "jwkInvalid"
  | .jwkPrivateMember _ _ => "jwkPrivateMember"
  | .secretMaterial _ _ => "secretMaterial"
  | .relationshipNotSet _ => "relationshipNotSet"
  | .relationshipEmpty _ => "relationshipEmpty"
  | .relationshipEntryInvalid _ => "relationshipEntryInvalid"

/-- RFC 6901 §3: `~` is `~0` and `/` is `~1` in a reference token. -/
def pointerToken (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '~' then "~0" else if c == '/' then "~1" else c.toString)

/-- The place of an error of one map (a service or a method), relative to
that map. -/
def DocError.inMap : DocError → String
  | .methodIdInvalid => "/id"
  | .methodTypeInvalid _ => "/type"
  | .methodControllerInvalid _ => "/controller"
  | .methodExpiresInvalid _ => "/expires"
  | .methodRevokedInvalid _ => "/revoked"
  | .methodMaterialMismatch _ _ p => "/" ++ pointerToken p
  | .multikeyInvalid _ _ => "/publicKeyMultibase"
  | .multibaseInvalid _ => "/publicKeyMultibase"
  | .jwkInvalid _ => "/publicKeyJwk"
  | .jwkPrivateMember _ m => "/publicKeyJwk/" ++ pointerToken m
  | .secretMaterial _ p => "/" ++ pointerToken p
  | .serviceIdInvalid => "/id"
  | .serviceTypeInvalid => "/type"
  | .serviceEndpointInvalid => "/serviceEndpoint"
  | _ => ""

/-- One failed MUST and where it is. -/
structure Issue where
  error : DocError
  path : String
  deriving Repr, DecidableEq

/-- The report of `check`. -/
structure Report where
  valid : Bool
  issues : List Issue
  deriving Repr

/-! ## Collecting the failures -/

/-- Check each element of a set with `f`, from index `i`; a failed element
gives one issue at `/member/i` and the place in the element. -/
def elementIssues {α : Type} (member : String) (f : Json → Except DocError α)
    (inside : Json → DocError → String) : Nat → List Json → List Issue → List Issue
  | _, [], acc => acc.reverse
  | i, x :: xs, acc =>
      match f x with
      | .ok _ => elementIssues member f inside (i + 1) xs acc
      | .error e =>
          elementIssues member f inside (i + 1) xs
            ({ error := e, path := "/" ++ member ++ "/" ++ toString i ++ inside x e } :: acc)

/-- Inside an element: the place of the error when the element is a map. -/
def mapInside (x : Json) (e : DocError) : String :=
  match x with
  | .object _ => e.inMap
  | _ => ""

def idIssues (j : Json) : List Issue :=
  match j.field? "id" with
  | none => [{ error := .idMissing, path := "/id" }]
  | some (.string s) => if isUrl s then [] else [{ error := .idNotUrl, path := "/id" }]
  | some _ => [{ error := .idNotUrl, path := "/id" }]

def controllerIssues (j : Json) : List Issue :=
  match j.field? "controller" with
  | none => []
  | some c => if (stringOrSet isUrlRef c).isSome then [] else [{ error := .controllerInvalid, path := "/controller" }]

def alsoKnownAsIssues (j : Json) : List Issue :=
  match j.field? "alsoKnownAs" with
  | none => []
  | some (.array xs) =>
      let ss := xs.filterMap Json.asString?
      if ss.length == xs.length && ss.all isUrl then [] else [{ error := .alsoKnownAsInvalid, path := "/alsoKnownAs" }]
  | some _ => [{ error := .alsoKnownAsInvalid, path := "/alsoKnownAs" }]

def serviceIssues (j : Json) : List Issue :=
  match j.field? "service" with
  | none => []
  | some (.array xs) =>
      let each := elementIssues "service" parseService mapInside 0 xs []
      let base := (j.getString? "id").getD ""
      let ids := (xs.filterMap fun x => (parseService x).toOption).filterMap fun s => s.id.map (absolute base)
      match firstDuplicate ids [] with
      | some d => each ++ [{ error := .serviceIdDuplicate d, path := "/service" }]
      | none => each
  | some _ => [{ error := .serviceNotSet, path := "/service" }]

def methodIssues (j : Json) : List Issue :=
  match j.field? "verificationMethod" with
  | none => []
  | some (.array xs) => elementIssues "verificationMethod" parseMethod mapInside 0 xs []
  | some _ => [{ error := .verificationMethodNotSet, path := "/verificationMethod" }]

def relationshipIssues (j : Json) (r : Relationship) : List Issue :=
  match j.field? r.name with
  | none => []
  | some (.array []) => [{ error := .relationshipEmpty r, path := "/" ++ r.name }]
  | some (.array xs) => elementIssues r.name (parseEntry r) mapInside 0 xs []
  | some _ => [{ error := .relationshipNotSet r, path := "/" ++ r.name }]

/-- Every failure found member by member, in document-model order. -/
def collectIssues (j : Json) : List Issue :=
  match j with
  | .object _ =>
      idIssues j ++ controllerIssues j ++ alsoKnownAsIssues j ++ serviceIssues j ++ methodIssues j ++
        Relationship.all.flatMap (relationshipIssues j)
  | _ => [{ error := .notMap, path := "" }]

/-- The place of the error `parseDocument` stops at, when the members do not
give it (none known: the whole document). -/
def fallbackIssue (e : DocError) : Issue := { error := e, path := "" }

/-- **The report.** Valid exactly when `parseDocument` accepts the document. -/
def check (j : Json) : Report :=
  match parseDocument j with
  | .ok _ => { valid := true, issues := [] }
  | .error e =>
      let found := collectIssues j
      { valid := false,
        issues := if found.any (·.error == e) then found else fallbackIssue e :: found }

/-- The report of a text: not JSON is one issue at `""`. -/
def checkText (text : String) : Report :=
  match parseJson? text with
  | some j => check j
  | none => { valid := false, issues := [fallbackIssue .notJson] }

/-! ## Theorems -/

/-- `valid` is the answer of `parseDocument`. -/
theorem check_valid_iff (j : Json) : (check j).valid = true ↔ ∃ d, parseDocument j = .ok d := by
  unfold check
  cases h : parseDocument j with
  | ok d => simp
  | error e => simp

/-- A valid report has no issues. -/
theorem check_valid_no_issues (j : Json) (h : (check j).valid = true) : (check j).issues = [] := by
  unfold check at *
  cases hp : parseDocument j with
  | ok d => rfl
  | error e => simp [hp] at h

/-- The error `parseDocument` stops at is one of the issues. -/
theorem check_lists_parse_error {j : Json} {e : DocError} (h : parseDocument j = .error e) :
    (check j).valid = false ∧ ∃ i ∈ (check j).issues, i.error = e := by
  unfold check
  simp only [h]
  refine ⟨trivial, ?_⟩
  by_cases hf : (collectIssues j).any (·.error == e) = true
  · simp only [hf, if_true]
    obtain ⟨i, hi, he⟩ := List.any_eq_true.mp hf
    exact ⟨i, hi, by simpa using he⟩
  · simp only [hf]
    exact ⟨fallbackIssue e, List.mem_cons_self, rfl⟩

/-- `checkText` agrees with `parseDocumentText`. -/
theorem checkText_valid_iff (t : String) :
    (checkText t).valid = true ↔ ∃ d, parseDocumentText t = .ok d := by
  unfold checkText parseDocumentText
  cases parseJson? t with
  | some j => exact check_valid_iff j
  | none => simp

end L4Factoidal.CID
