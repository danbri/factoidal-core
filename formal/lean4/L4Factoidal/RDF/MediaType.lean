/-
L4Factoidal.RDF.MediaType — which Internet media type names which RDF syntax
(https://github.com/danbri/factoidal/issues/975, hand-over finding 1).

`formatOfMediaType` maps the media type of a document to its `RdfFormat`.
Each syntax's W3C Recommendation registers one media type and one file
extension, in its appendix or section "Internet Media Type, File Extension and
Macintosh File Type" (JSON-LD: "IANA Considerations"):

| syntax | media type | extension | registration |
|---|---|---|---|
| Turtle | `text/turtle` | `.ttl` | RDF 1.1 Turtle (W3C Recommendation, 25 February 2014) |
| N-Triples | `application/n-triples` | `.nt` | RDF 1.1 N-Triples (W3C Recommendation, 25 February 2014) |
| N-Quads | `application/n-quads` | `.nq` | RDF 1.1 N-Quads (W3C Recommendation, 25 February 2014) |
| TriG | `application/trig` | `.trig` | RDF 1.1 TriG (W3C Recommendation, 25 February 2014) |
| RDF/XML | `application/rdf+xml` | `.rdf` | RDF 1.1 XML Syntax (W3C Recommendation, 25 February 2014); RFC 3870 |
| JSON-LD | `application/ld+json` | `.jsonld` | JSON-LD 1.1 (W3C Recommendation, 16 July 2020) |

The RDF 1.2 drafts of these syntaxes keep the same media types and extensions.

`text/n3` (Notation3, a W3C Team Submission) has no reader in this library,
so it gives `none`. Types that no registration above names (`text/plain`,
`application/json`, `application/x-turtle`) give `none`.

## Parameters and letter case

RFC 9110 section 8.3.1 ("Media Type"): a media type is `type "/" subtype`
followed by parameters, each after a `;`; the type and the subtype are
case-insensitive. `mediaTypeEssence` keeps the text before the first `;`,
removes spaces and horizontal tabs at both ends, and lower-cases ASCII
letters. The parameters do not change the format (`formatOfMediaType_params`):
the six registrations above define no parameter that selects a different
syntax (`charset` of Turtle, N-Triples, N-Quads and TriG is UTF-8 only;
JSON-LD's `profile` selects a document form, not a syntax).

## The file-name extension

`formatOfDocument mediaType name` uses the media type when there is one. Only
when the media type is absent (its essence is empty) does it use the
extension of the name, and only the extensions of the registrations above
(`formatOfRegisteredExtension`; `.owl` and `.xml` are not registered for
RDF/XML). An unknown media type does not fall back to the extension.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Format

namespace L4Factoidal.RDF

/-- Space or horizontal tab: the optional white space around a media type
(RFC 9110 section 5.6.3, `OWS`). -/
def isOws (c : Char) : Bool := c == ' ' || c == '\t'

/-- The characters of the essence: before the first `;`, white space removed
at both ends, ASCII letters lower-cased. -/
def essenceChars (cs : List Char) : List Char :=
  (((cs.takeWhile (· ≠ ';')).dropWhile isOws).reverse.dropWhile isOws).reverse.map Char.toLower

/-- The media type without parameters, trimmed, in lower case:
`"Text/Turtle; charset=UTF-8"` gives `"text/turtle"`. -/
def mediaTypeEssence (mt : String) : String := String.ofList (essenceChars mt.toList)

/-- The format of a media-type essence (the table of the module header). -/
def formatOfEssence : String → Option RdfFormat
  | "text/turtle" => some .turtle
  | "application/n-triples" => some .nt
  | "application/n-quads" => some .nquads
  | "application/trig" => some .trig
  | "application/rdf+xml" => some .rdfxml
  | "application/ld+json" => some .jsonld
  | _ => none

/-- The format of a media type, with or without parameters. -/
def formatOfMediaType (mt : String) : Option RdfFormat := formatOfEssence (mediaTypeEssence mt)

/-- The registered media type of a format. -/
def mediaTypeOf : RdfFormat → String
  | .turtle => "text/turtle"
  | .nt => "application/n-triples"
  | .nquads => "application/n-quads"
  | .trig => "application/trig"
  | .rdfxml => "application/rdf+xml"
  | .jsonld => "application/ld+json"

/-- The registered file extension of a format, with its leading dot. -/
def registeredExtensionOf : RdfFormat → String
  | .turtle => ".ttl"
  | .nt => ".nt"
  | .nquads => ".nq"
  | .trig => ".trig"
  | .rdfxml => ".rdf"
  | .jsonld => ".jsonld"

/-- The format of a registered extension (leading dot; ASCII case ignored). -/
def formatOfRegisteredExtension (ext : String) : Option RdfFormat :=
  match ext.toLower with
  | ".ttl" => some .turtle
  | ".nt" => some .nt
  | ".nq" => some .nquads
  | ".trig" => some .trig
  | ".rdf" => some .rdfxml
  | ".jsonld" => some .jsonld
  | _ => none

/-- The format of a file name or URL path by its last extension, from the
registered extensions only. -/
def formatOfRegisteredPath (name : String) : Option RdfFormat :=
  match (System.FilePath.mk name).extension with
  | some ext => formatOfRegisteredExtension ("." ++ ext)
  | none => none

/-- **The format of a document.** The media type when there is one; the
registered extension of the name only when the media type is absent. -/
def formatOfDocument (mediaType name : String) : Option RdfFormat :=
  if mediaTypeEssence mediaType = "" then formatOfRegisteredPath name
  else formatOfMediaType mediaType

/-! ## Theorems -/

theorem formatOfEssence_empty : formatOfEssence "" = none := rfl

/-- A media type that names a format is not absent: `formatOfDocument` gives
that format, whatever the name. -/
theorem formatOfDocument_of_mediaType {mt : String} {f : RdfFormat} (name : String)
    (h : formatOfMediaType mt = some f) : formatOfDocument mt name = some f := by
  unfold formatOfDocument
  by_cases he : mediaTypeEssence mt = ""
  · unfold formatOfMediaType at h
    rw [he, formatOfEssence_empty] at h
    cases h
  · rw [if_neg he]
    exact h

/-- With no media type, `formatOfDocument` is the registered extension of the
name. -/
theorem formatOfDocument_absent {mt : String} (name : String) (h : mediaTypeEssence mt = "") :
    formatOfDocument mt name = formatOfRegisteredPath name := by
  unfold formatOfDocument
  rw [if_pos h]

/-- An unknown media type gives no format; the name is not read. -/
theorem formatOfDocument_unknown {mt : String} (name : String) (hne : mediaTypeEssence mt ≠ "")
    (h : formatOfMediaType mt = none) : formatOfDocument mt name = none := by
  unfold formatOfDocument
  rw [if_neg hne]
  exact h

theorem takeWhile_append_semicolon (a b : List Char) (ha : ∀ c ∈ a, c ≠ ';') :
    (a ++ ';' :: b).takeWhile (· ≠ ';') = a := by
  induction a with
  | nil => simp
  | cons c a ih =>
    have hc : c ≠ ';' := ha c List.mem_cons_self
    simp only [List.cons_append, List.takeWhile_cons, hc, ne_eq, not_false_eq_true, decide_true,
      if_true]
    rw [ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))]

theorem takeWhile_no_semicolon (a : List Char) (ha : ∀ c ∈ a, c ≠ ';') :
    a.takeWhile (· ≠ ';') = a := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    have hc : c ≠ ';' := ha c List.mem_cons_self
    simp only [List.takeWhile_cons, hc, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))]

/-- **Parameters do not change the essence.** For a media type `mt` with no
`;`, `mt; params` has the essence of `mt`. -/
theorem mediaTypeEssence_params (mt params : String) (h : ∀ c ∈ mt.toList, c ≠ ';') :
    mediaTypeEssence (mt ++ ";" ++ params) = mediaTypeEssence mt := by
  unfold mediaTypeEssence essenceChars
  have e : (mt ++ ";" ++ params).toList = mt.toList ++ ';' :: params.toList := by
    simp [String.toList_append]
  rw [e, takeWhile_append_semicolon _ _ h]
  rw [takeWhile_no_semicolon _ h]

/-- Parameters do not change the format. -/
theorem formatOfMediaType_params (mt params : String) (h : ∀ c ∈ mt.toList, c ≠ ';') :
    formatOfMediaType (mt ++ ";" ++ params) = formatOfMediaType mt := by
  unfold formatOfMediaType
  rw [mediaTypeEssence_params mt params h]

/-! ## Build-time checks (the full table: `RDF/MediaTypeTests.lean`) -/

#guard [RdfFormat.nt, .turtle, .nquads, .trig, .rdfxml, .jsonld].all fun f =>
  formatOfMediaType (mediaTypeOf f) == some f
#guard formatOfMediaType "text/turtle; charset=utf-8" == some .turtle

#print axioms formatOfDocument_of_mediaType
#print axioms formatOfDocument_absent
#print axioms formatOfDocument_unknown
#print axioms mediaTypeEssence_params
#print axioms formatOfMediaType_params

end L4Factoidal.RDF
