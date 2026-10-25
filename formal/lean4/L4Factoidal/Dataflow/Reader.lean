/-
L4Factoidal.Dataflow.Reader — the interface type of an RDF reader
(https://github.com/danbri/factoidal/issues/975, "Architecture acceptance",
item 2, the first component kind).

## The contract

`ReaderContract extra fmt mode base n text out` is the contract of the batch
reader of the syntax `fmt` with the document scope `n` (phase C). With `raw`
the list that the parser of the syntax gives (`parseDocumentRaw`) and `ds` its
set:

* the set: `SetOf ds raw`, and `ds.den = raw.den`;
* the scope: `out = ds.scopeDocument n`, `out.InScope n`, `out.IsSet`;
* the meaning: `out.den = raw.den.rename (docLabel n)` (exact image) and
  `DatasetDen.Iso raw.den out.den`;
* RDF 1.2 terms: `eraseLabels out = eraseLabels ds`. The scope step changes
  blank-node labels only.

## The interface type

`RdfReader` is a reader of one syntax: its source-layer readers (`extra`), its
syntax (`fmt`), a run from a `ReaderInput` (the decoded text, the RDF version
mode, the base IRI) to the dataset and the prefixes the document declared,
and three proof fields:

* `set`: the dataset of a successful run is the set of quads of the parse
  (`SetOf`), so it is a set;
* `sound`: a successful run satisfies `ReaderContract` for every scope number
  `n`, with `out.1.scopeDocument n` as the output;
* `fails`: the run fails exactly when the parser of the syntax fails, with the
  same error.

So a value of type `RdfReader` cannot exist without the proofs. The prefixes
are extra output: no contract is stated about them.

`documentReader extra fmt` is the reader that `Source.parseDocumentWithPrefixes`
gives (`parseDocumentWithPrefixes_map_fst`: its dataset is the dataset of
`Source.parseDocument`). `readers extra : RdfFormat → RdfReader` is the table
with one reader for each syntax. The wasm dispatch reads every RDF document
through this table (`Wasm/Ops/Parse.lean`).

The input is decoded text, not bytes: the wasm ops receive a JavaScript
string. The UTF-8 decode of a `Document` is `decodeStage`
(`Dataflow/Instances.lean`).

Not in the FOUNDATION manifest: the contract names `parseDocumentRaw`, which
calls implementation parsers (the Turtle walk `parseTurtleText`,
`parseNQuadsFast`), not a grammar relation of the W3C specification.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Source
import L4Factoidal.RDF.DocumentScope

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDF.Source
open L4Factoidal.Syntax

/-! ## Blank-node labels only -/

/-- The dataset with every blank-node label replaced by the empty label: what
is left when the labels are ignored. -/
def eraseLabels (ds : Dataset) : Dataset := ds.renameBnodes (fun _ => "")

/-- **The document scope changes blank-node labels only.** IRIs, literals and
triple terms (nested ones too) are kept. -/
theorem eraseLabels_scopeDocument (n : Nat) (ds : Dataset) :
    eraseLabels (ds.scopeDocument n) = eraseLabels ds := by
  unfold eraseLabels Dataset.scopeDocument
  rw [Dataset.renameBnodes_comp]
  rfl

/-- `SetOf` keeps the denotation. -/
theorem SetOf.den_eq {ds raw : Dataset} (h : SetOf ds raw) : ds.den = raw.den :=
  DatasetDen.ext (fun gn t => h.memQuad t gn) (fun n => h.names n)

/-! ## The contract -/

/-- The contract of the reader of syntax `fmt` with the document scope `n`. -/
def ReaderContract (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode) (base : Option String)
    (n : Nat) (text : String) (out : Dataset) : Prop :=
  ∃ raw ds, parseDocumentRaw extra fmt mode base text = .ok raw ∧ SetOf ds raw ∧
    ds.den = raw.den ∧ out = ds.scopeDocument n ∧ out.IsSet ∧ out.InScope n ∧
    out.den = raw.den.rename (docLabel n) ∧ DatasetDen.Iso raw.den out.den ∧
    eraseLabels out = eraseLabels ds

/-- A set of the raw parse, scoped by `n`, satisfies the contract. -/
theorem readerContract_of_set {extra : Extra} {fmt : RdfFormat} {mode : Syntax.Mode}
    {base : Option String} {text : String} {raw ds : Dataset}
    (hr : parseDocumentRaw extra fmt mode base text = .ok raw) (hs : SetOf ds raw) (n : Nat) :
    ReaderContract extra fmt mode base n text (ds.scopeDocument n) := by
  have hden := SetOf.den_eq hs
  refine ⟨raw, ds, hr, hs, hden, rfl, Dataset.scopeDocument_isSet n hs.isSet,
    ds.scopeDocument_inScope n, ?_, ?_, eraseLabels_scopeDocument n ds⟩
  · rw [← hden]
    exact Dataset.den_renameBnodes (docLabel n) ds
  · rw [← hden]
    exact ds.den_iso_scopeDocument n

/-- `parseDocument` fails exactly when the parser of the syntax fails, with the
same error. -/
theorem parseDocument_error_iff (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode)
    (base : Option String) (text : String) (e : ParseError) :
    parseDocument extra fmt mode base text = .error e ↔
      parseDocumentRaw extra fmt mode base text = .error e := by
  unfold parseDocument
  split
  · exact Iff.rfl
  · cases parseDocumentRaw extra fmt mode base text with
    | error e' => simp [Except.map]
    | ok raw => simp [Except.map]

/-! ## The interface type -/

/-- The input of a reader: the decoded text of one document, the RDF version
mode, and the base IRI. -/
structure ReaderInput where
  text : String
  mode : Syntax.Mode := .rdf11
  base : Option String := none

/-- The prefixes a document declared, most recent binding first, as the
Turtle and TriG parsers hold them (`[]` for the other syntaxes). -/
abbrev PrefixList := List (String × String)

/-- **A reader of one RDF syntax, with its contract as fields.** -/
structure RdfReader where
  /-- The source-layer readers linked in (`Source.withJsonLd` for JSON-LD). -/
  extra : Extra
  /-- The syntax. -/
  fmt : RdfFormat
  /-- Read one document: its dataset and the prefixes it declared. -/
  run : ReaderInput → Except ParseError (Dataset × PrefixList)
  /-- The dataset of a successful run is the set of quads of the parse. -/
  set : ∀ inp out, run inp = .ok out →
    ∃ raw, parseDocumentRaw extra fmt inp.mode inp.base inp.text = .ok raw ∧ SetOf out.1 raw
  /-- A successful run satisfies the reader contract, for every scope number. -/
  sound : ∀ inp out, run inp = .ok out →
    ∀ n, ReaderContract extra fmt inp.mode inp.base n inp.text (out.1.scopeDocument n)
  /-- The run fails exactly when the parser of the syntax fails, with the
  same error. -/
  fails : ∀ inp e, run inp = .error e ↔
    parseDocumentRaw extra fmt inp.mode inp.base inp.text = .error e

namespace RdfReader

/-- The dataset of a run, without the prefixes. -/
def dataset (r : RdfReader) (inp : ReaderInput) : Except ParseError Dataset :=
  (r.run inp).map Prod.fst

/-- The dataset of a successful run is a set of quads. -/
theorem isSet (r : RdfReader) {inp : ReaderInput} {out : Dataset × PrefixList}
    (h : r.run inp = .ok out) : out.1.IsSet := by
  obtain ⟨_, -, hs⟩ := r.set inp out h
  exact hs.isSet

end RdfReader

/-! ## The reader of `parseDocumentWithPrefixes` -/

/-- **`parseDocumentWithPrefixes` gives the dataset of `parseDocument`**; the
prefixes are extra output. -/
theorem parseDocumentWithPrefixes_map_fst (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode)
    (base : Option String) (text : String) :
    (parseDocumentWithPrefixes extra fmt mode base text).map Prod.fst =
      parseDocument extra fmt mode base text := by
  cases fmt with
  | turtle =>
    simp only [parseDocumentWithPrefixes, parseDocument, givesSet, Bool.false_eq_true, if_false,
      parseDocumentRaw]
    rw [← parseTurtleTextWithPrefixes_map_fst]
    cases parseTurtleTextWithPrefixes text base mode <;> rfl
  | trig =>
    simp only [parseDocumentWithPrefixes, parseDocument, givesSet, if_true, parseDocumentRaw]
    exact parseTriGWithPrefixes_map_fst text base mode
  | nt | nquads | rdfxml | jsonld =>
    simp only [parseDocumentWithPrefixes]
    cases parseDocument extra _ mode base text <;> rfl

theorem parseDocumentWithPrefixes_ok {extra : Extra} {fmt : RdfFormat} {mode : Syntax.Mode}
    {base : Option String} {text : String} {out : Dataset × PrefixList}
    (h : parseDocumentWithPrefixes extra fmt mode base text = .ok out) :
    parseDocument extra fmt mode base text = .ok out.1 := by
  rw [← parseDocumentWithPrefixes_map_fst, h]
  rfl

theorem parseDocumentWithPrefixes_error_iff (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode)
    (base : Option String) (text : String) (e : ParseError) :
    parseDocumentWithPrefixes extra fmt mode base text = .error e ↔
      parseDocument extra fmt mode base text = .error e := by
  rw [← parseDocumentWithPrefixes_map_fst]
  cases parseDocumentWithPrefixes extra fmt mode base text with
  | error e' => simp [Except.map]
  | ok v => simp [Except.map]

/-- The reader of syntax `fmt` that `Source.parseDocumentWithPrefixes` gives. -/
def documentReader (extra : Extra) (fmt : RdfFormat) : RdfReader where
  extra := extra
  fmt := fmt
  run inp := parseDocumentWithPrefixes extra fmt inp.mode inp.base inp.text
  set := by
    intro inp out h
    exact parseDocument_set extra fmt inp.mode inp.base inp.text out.1 (parseDocumentWithPrefixes_ok h)
  sound := by
    intro inp out h n
    obtain ⟨raw, hr, hs⟩ :=
      parseDocument_set extra fmt inp.mode inp.base inp.text out.1 (parseDocumentWithPrefixes_ok h)
    exact readerContract_of_set hr hs n
  fails := by
    intro inp e
    rw [parseDocumentWithPrefixes_error_iff]
    exact parseDocument_error_iff extra fmt inp.mode inp.base inp.text e

/-- **The readers, one for each syntax.** Every RDF document the wasm dispatch
reads goes through this table. -/
def readers (extra : Extra) : RdfFormat → RdfReader := documentReader extra

theorem readers_fmt (extra : Extra) (fmt : RdfFormat) : (readers extra fmt).fmt = fmt := rfl

theorem readers_dataset (extra : Extra) (fmt : RdfFormat) (inp : ReaderInput) :
    (readers extra fmt).dataset inp = parseDocument extra fmt inp.mode inp.base inp.text :=
  parseDocumentWithPrefixes_map_fst extra fmt inp.mode inp.base inp.text

/-- The N-Quads text of a dataset handle, read by the N-Quads reader of the
table. -/
def readNQuadsText (mode : Syntax.Mode) (text : String) : Except ParseError Dataset :=
  (readers {} .nquads).dataset { text, mode }

/-- It is `parseNQuadsFast`. -/
theorem readNQuadsText_eq (mode : Syntax.Mode) (text : String) :
    readNQuadsText mode text = parseNQuadsFast text mode := by
  unfold readNQuadsText
  rw [readers_dataset]
  rfl

/-- A run of a reader as a dataset that carries its set proof (the subtype
`RDF.CertifiedDataset` abbreviates). -/
def RdfReader.certified (r : RdfReader) (inp : ReaderInput) :
    Except ParseError { ds : Dataset // ds.IsSet } :=
  match h : r.run inp with
  | .ok out => .ok ⟨out.1, r.isSet h⟩
  | .error e => .error e

/-- Without the proof it is the dataset of the run. -/
theorem RdfReader.certified_val (r : RdfReader) (inp : ReaderInput) :
    (r.certified inp).map Subtype.val = r.dataset inp := by
  unfold RdfReader.certified RdfReader.dataset
  split
  · next out h => simp [h, Except.map]
  · next e h => simp [h, Except.map]

/-- The N-Quads text of a dataset handle, read with its set proof. -/
def readNQuadsCertified (mode : Syntax.Mode) (text : String) :
    Except ParseError { ds : Dataset // ds.IsSet } :=
  (readers {} .nquads).certified { text, mode }

theorem readNQuadsCertified_val (mode : Syntax.Mode) (text : String) :
    (readNQuadsCertified mode text).map Subtype.val = readNQuadsText mode text :=
  RdfReader.certified_val _ _

/-! ### One named reader for each syntax (the registry names them) -/

def ntriplesDocumentReader : RdfReader := readers {} .nt
def nquadsDocumentReader : RdfReader := readers {} .nquads
def turtleDocumentReader : RdfReader := readers {} .turtle
def trigDocumentReader : RdfReader := readers {} .trig
def rdfxmlDocumentReader : RdfReader := readers {} .rdfxml

#print axioms eraseLabels_scopeDocument
#print axioms readerContract_of_set
#print axioms parseDocument_error_iff
#print axioms RdfReader.isSet
#print axioms RdfReader.certified_val
#print axioms parseDocumentWithPrefixes_map_fst
#print axioms documentReader
#print axioms readers_dataset
#print axioms readNQuadsText_eq

end L4Factoidal.Dataflow
