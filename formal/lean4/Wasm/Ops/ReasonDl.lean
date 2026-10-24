/-
Wasm.Ops.ReasonDl — checked OWL consistency and OWL entailment.
Consistency reads the original default graph and answers only with a checked
model or a checked refutation. Entailment answers `false` only with a checked
countermodel; its `true` answers still use the RL closure and the refuter.

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  owlIsConsistent(nquads, optsJson)
      -> {"ok":true,"consistent":true|false|null,"reason"?:"…"}
  owlEntails(premiseNquads, conclusionNquads, optsJson)
      -> {"ok":true,"entailed":true|false|null,
          "via":"closure"|"refutation","reason"?:"…"}

These two ops were in `Wasm/Ops/Reason.lean` until 2026-10-10. They moved
to their own module so that the core dispatch (`Wasm/CoreDispatch.lean`,
https://github.com/danbri/factoidal/issues/713 stage 4) serves the RDFS and
OWL 2 RL closures without importing the tableau refuter; only the full
dispatch (`Wasm/Dispatch.lean`) imports this module.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Dataflow.Reader
import Wasm.Ops.ReasonDlCertified
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.OWL.RLClosure
-- The `@[csimp]` theorem that makes `OWL.RL.closureFix` compile to the
-- indexed closure (see the note in `Wasm/Ops/Reason.lean`).
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.NegationGoals
import L4Factoidal.OWL.DirectProfile
import Wasm.Ops.FromDataset
import L4Factoidal.RDF.Rdf11Terms

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-! ## Separate consistency and entailment assurance

Consistency uses the restricted AtomicDirect reader, the model checker
(`AtomicModel.checkModel_sound`) and the certificate checker
(`DirectCert.checkCertFuel_sound`) through ReasonDlCertified. Unsupported
syntax returns unknown with no unchecked fallback.

Entailment answers `false` only through `AtomicModel.entailsFuel`: a checked
model of the premise in which the conclusion fails
(`AtomicModel.checkCountermodel_sound`, `owlEntailsJson_false_sound`). Its
`true` answers use the legacy RL/refuter route; their punning refusal is
limited and is not a Direct Semantics soundness proof.
Records: `docs/20261021-owl-public-boundary.md`,
https://github.com/danbri/factoidal/issues/960. -/

/-- The refutation budget: `optsJson` is `""` or `{"fuel":"<nat>"}`
(fuel a decimal STRING — a large budget can exceed JS's safe-integer
range, so it crosses the ABI as text, same as the F* entry). Default
20000, matching `entry_jsoo.ml`'s `owl_refute_fuel_of_opts`; any
unreadable opts document or fuel string falls back to the default. -/
def owlRefuteFuelOfOpts (optsJson : String) : Nat :=
  let defaultFuel := 20000
  if optsJson == "" then defaultFuel
  else
    match parseJson optsJson with
    | .error _ => defaultFuel
    | .ok root =>
      match root.getString? "fuel" with
      | some s => (s.toNat?).getD defaultFuel
      | none   => defaultFuel

/-- The refusal for a dataset with an RDF 1.2 term
(https://github.com/danbri/factoidal/issues/958). The verdicts below are OWL 2
Direct Semantics verdicts. The RDF graph is read as an OWL 2 ontology by OWL 2
Mapping to RDF Graphs (§3, Mapping from RDF Graphs to the Structural
Specification), which is stated on RDF 1.1 graphs and has no rule for a
triple term; the OWL 2 Direct Semantics has no interpretation of one. Design
record: `docs/designissues/2026-10-18-rdf12-terms-canon-and-closures.md`. -/
def owlDlRdf12Refusal (op : String) : String :=
  s!"{op}: the input holds an RDF 1.2 triple term or directional language-tagged "
  ++ "string; OWL 2 Mapping to RDF Graphs (section 3) and the OWL 2 Direct "
  ++ "Semantics define no rule for these terms "
  ++ "(https://github.com/danbri/factoidal/issues/958)"

def owlDlPunningReason : String :=
  "unsupported-punning: a class or property IRI is also used as an individual; "
  ++ "the RDF-based closure does not preserve OWL Direct Semantics punning "
  ++ "(indeterminate)"

/-- Checked consistency over the original default graph. Unsupported syntax,
rejected certificates and exhausted fuel return null. `opts.fuel` bounds the
model search and the certificate checker. -/
def owlIsConsistentParsed (ds : Dataset) (optsJson : String) : String :=
  (owlConsistencyJson ds (owlRefuteFuelOfOpts optsJson)).toString

/-- The actual string producer serializes a JSON object whose definitive
field satisfies the original-default-graph contract. JSON serialization and
external parsing remain separate artifact-test boundaries. -/
theorem owlIsConsistentParsed_certified (ds : Dataset) (optsJson : String) :
    ∃ response : Json,
      owlIsConsistentParsed ds optsJson = response.toString ∧
      L4Factoidal.OWL.AtomicDirect.Meaning ds.default (response.getBool? "consistent") := by
  exact ⟨owlConsistencyJson ds (owlRefuteFuelOfOpts optsJson), rfl,
    owlConsistencyJson_sound ds (owlRefuteFuelOfOpts optsJson)⟩

/-- `owlIsConsistent(nquads, optsJson)`. -/
def owlIsConsistent (nq optsJson : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => owlIsConsistentParsed ds optsJson

/-- Conditional on the actual parser returning ds, the text entry point
serializes a justified verdict about ds.default. This is not a theorem
that the parser implements the complete N-Quads standard. -/
theorem owlIsConsistent_certified (nq optsJson : String) (ds : Dataset)
    (parsed : parseNQuadsFast nq .rdf12 = .ok ds) :
    ∃ response : Json,
      owlIsConsistent nq optsJson = response.toString ∧
      L4Factoidal.OWL.AtomicDirect.Meaning ds.default (response.getBool? "consistent") := by
  simpa only [owlIsConsistent, L4Factoidal.Dataflow.readNQuadsText_eq, parsed] using
    owlIsConsistentParsed_certified ds optsJson

#print axioms owlIsConsistentParsed_certified
#print axioms owlIsConsistent_certified

/-- The legacy entailment route: `via:"closure"` when every conclusion
triple is exactly (engine triple equality) in the OWL-RL closure of the
premise; `via:"refutation"` when the negated conclusion (`negationGoals`) is
refuted on every goal. It answers `true` or null, never `false`. -/
def owlEntailsLegacyJson (dsP dsC : Dataset) (fuel : Nat) : Json :=
  let gc := dsC.default
  let closure := L4Factoidal.OWL.RL.closureFix dsP.default
  if gc.all (fun t => Graph.mem t closure) then
    .object [("ok", .bool true), ("entailed", .bool true), ("via", .string "closure")]
  else
    match L4Factoidal.OWL.Refute.negationGoals gc with
    | none =>
        .object [("ok", .bool true), ("entailed", .null), ("via", .string "closure"),
                ("reason", .string
                  ("unsupported-conclusion: not in the OWL-RL closure, "
                   ++ "and the conclusion form cannot be soundly negated "
                   ++ "for refutation (indeterminate)"))]
    | some goals =>
      let results := goals.map (fun neg =>
        L4Factoidal.OWL.Refute.tableauConsistent (closure ++ neg) fuel)
      if results.all (· == some false) then
        .object [("ok", .bool true), ("entailed", .bool true), ("via", .string "refutation")]
      else if results.any (· == some true) then
        .object [("ok", .bool true), ("entailed", .null), ("via", .string "refutation"),
                ("reason", .string
                  ("incomplete-search: a negated conclusion was not "
                   ++ "refuted, but the search does not certify a "
                   ++ "countermodel (indeterminate)"))]
      else
        .object [("ok", .bool true), ("entailed", .null), ("via", .string "refutation"),
                ("reason", .string
                  (s!"budget-out: a refutation goal exhausted fuel {fuel} "
                   ++ "before closing (indeterminate); raise it via "
                   ++ "opts.fuel"))]

theorem owlEntailsLegacyJson_ne_false (dsP dsC : Dataset) (fuel : Nat) :
    (owlEntailsLegacyJson dsP dsC fuel).getBool? "entailed" ≠ some false := by
  unfold owlEntailsLegacyJson
  dsimp only
  split
  · simp [Json.getBool?, Json.field?, Json.asBool?]
  · split
    · simp [Json.getBool?, Json.field?, Json.asBool?]
    · split
      · simp [Json.getBool?, Json.field?, Json.asBool?]
      · split <;> simp [Json.getBool?, Json.field?, Json.asBool?]

/-- `owlEntails(premiseNquads, conclusionNquads, optsJson)` as a JSON value.
`false` comes only from a checked countermodel (`AtomicModel.entailsFuel`),
tried first; `true` comes from the legacy route. -/
def owlEntailsJson (dsP dsC : Dataset) (optsJson : String) : Json :=
  if !(dsP.isRdf11 && dsC.isRdf11) then
    .object [("ok", .bool false), ("error", .string (owlDlRdf12Refusal "owlEntails"))]
  else if L4Factoidal.OWL.DirectProfile.hasUnsupportedPunning (dsP.default ++ dsC.default) then
    .object [("ok", .bool true), ("entailed", .null), ("via", .string "closure"),
            ("reason", .string owlDlPunningReason)]
  else
    let fuel := owlRefuteFuelOfOpts optsJson
    match L4Factoidal.OWL.AtomicModel.entailsFuel dsP.default dsC.default fuel with
    | some answer =>
        .object [("ok", .bool true), ("entailed", .bool answer), ("via", .string "refutation"),
                ("reason", .string
                  ("countermodel: a checked finite model of the premise is not a model "
                   ++ "of the conclusion (OWL 2 Direct Semantics, admitted fragment)"))]
    | none => owlEntailsLegacyJson dsP dsC fuel

/-- An `entailed: false` answer means: both default graphs are admitted and
the premise does not entail the conclusion. -/
theorem owlEntailsJson_false_sound (dsP dsC : Dataset) (optsJson : String)
    (reported : (owlEntailsJson dsP dsC optsJson).getBool? "entailed" = some false) :
    L4Factoidal.OWL.AtomicDirect.Accepted dsP.default ∧
      L4Factoidal.OWL.AtomicDirect.Accepted dsC.default ∧
      ¬ L4Factoidal.OWL.AtomicModel.Entails dsP.default dsC.default := by
  unfold owlEntailsJson at reported
  split at reported
  · simp [Json.getBool?, Json.field?] at reported
  · split at reported
    · simp [Json.getBool?, Json.field?, Json.asBool?] at reported
    · dsimp only at reported
      split at reported
      · rename_i answer result
        have sound := L4Factoidal.OWL.AtomicModel.entailsFuel_sound dsP.default dsC.default
          (owlRefuteFuelOfOpts optsJson)
        rw [result] at sound
        simp [Json.getBool?, Json.field?, Json.asBool?] at reported
        subst reported
        exact sound
      · exact absurd reported (owlEntailsLegacyJson_ne_false dsP dsC _)

#print axioms owlEntailsLegacyJson_ne_false
#print axioms owlEntailsJson_false_sound

def owlEntailsParsed (dsP dsC : Dataset) (optsJson : String) : String :=
  (owlEntailsJson dsP dsC optsJson).toString

/-- `owlEntails(premiseNquads, conclusionNquads, optsJson)`. -/
def owlEntails (premiseNq conclusionNq optsJson : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 premiseNq with
  | .error e => errJson (fmtParseError e)
  | .ok dsP =>
    match L4Factoidal.Dataflow.readNQuadsText .rdf12 conclusionNq with
    | .error e => errJson (fmtParseError e)
    | .ok dsC => owlEntailsParsed dsP dsC optsJson

/-! ### The same ops over datasets the caller parsed (`FromDataset.lean`)

The command line's entries (issue 724). Each answers the envelope the text op
answers on the canonical N-Quads of its datasets, for every dataset. -/

def owlIsConsistentOf (ds : Dataset) (optsJson : String) : String :=
  withOpsDataset .rdf12 ds (fun d => owlIsConsistentParsed d optsJson)

theorem owlIsConsistentOf_eq (ds : Dataset) (optsJson : String) :
    owlIsConsistentOf ds optsJson = owlIsConsistent (Dataset.toCanonicalNQuads ds) optsJson := by
  unfold owlIsConsistentOf owlIsConsistent
  rw [withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

def owlEntailsOf (dsP dsC : Dataset) (optsJson : String) : String :=
  withOpsDataset .rdf12 dsP (fun p => withOpsDataset .rdf12 dsC (fun c => owlEntailsParsed p c optsJson))

theorem owlEntailsOf_eq (dsP dsC : Dataset) (optsJson : String) :
    owlEntailsOf dsP dsC optsJson =
      owlEntails (Dataset.toCanonicalNQuads dsP) (Dataset.toCanonicalNQuads dsC) optsJson := by
  unfold owlEntailsOf owlEntails
  rw [withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads dsP) .rdf12 with
  | error e => rfl
  | ok p =>
      simp only [withOpsDataset_eq, L4Factoidal.Dataflow.readNQuadsText_eq]
      cases parseNQuadsFast (Dataset.toCanonicalNQuads dsC) .rdf12 <;> rfl

/-! ### RDF 1.2 input (https://github.com/danbri/factoidal/issues/873) -/

#guard owlIsConsistent "<http://example.com/a> <http://example.com/says> <<( <http://example.com/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> )>> .\n<http://example.com/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.com/D> .\n<http://example.com/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> .\n" "" == errJson (owlDlRdf12Refusal "owlIsConsistent")
#guard owlEntails "<http://example.com/a> <http://example.com/says> <<( _:b1 <http://example.com/p> <http://example.com/o> )>> .\n" "<http://example.com/a> <http://example.com/says> <<( _:b1 <http://example.com/p> <http://example.com/o> )>> .\n" "" == errJson (owlDlRdf12Refusal "owlEntails")
#guard owlIsConsistent "<http://example.com/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> .\n" "" ==
  "{\"ok\":true,\"consistent\":true}"

/-! ### Public verdict regressions (npm 0.11.0 audit R10)
These are executable examples, not universal Direct Semantics proofs. -/

private def sameNq (a b : String) : String :=
  s!"<urn:{a}> <http://www.w3.org/2002/07/owl#sameAs> <urn:{b}> .\n"

private def differentNq (a b : String) : String :=
  s!"<urn:{a}> <http://www.w3.org/2002/07/owl#differentFrom> <urn:{b}> .\n"

#guard (owlIsConsistent (sameNq "a" "b" ++ differentNq "a" "b") "").startsWith
  "{\"ok\":true,\"consistent\":false"
#guard (owlIsConsistent (sameNq "a" "b" ++ differentNq "b" "a") "").startsWith
  "{\"ok\":true,\"consistent\":false"
#guard (owlIsConsistent (differentNq "a" "a") "").startsWith
  "{\"ok\":true,\"consistent\":false"
#guard (owlIsConsistent (sameNq "a" "b" ++ sameNq "b" "c" ++ differentNq "a" "c") "").startsWith
  "{\"ok\":true,\"consistent\":false"
#guard owlIsConsistent (sameNq "a" "b") "" == "{\"ok\":true,\"consistent\":true}"
#guard owlIsConsistent (differentNq "a" "b") "" == "{\"ok\":true,\"consistent\":true}"

private def punningNq : String :=
  "<urn:C> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .\n" ++
  "<urn:D> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .\n" ++
  sameNq "C" "D" ++
  "<urn:C> <http://www.w3.org/2002/07/owl#disjointWith> <urn:D> .\n" ++
  "<urn:x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:C> .\n"

#guard (owlIsConsistent punningNq "").startsWith
  "{\"ok\":true,\"consistent\":null"
#guard (owlEntails punningNq "<urn:x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:D> .\n" "").startsWith
  "{\"ok\":true,\"entailed\":null"
#guard (owlEntails "" "<urn:a> <urn:p> \"value\" .\n" "").startsWith
  "{\"ok\":true,\"entailed\":null"

end L4Wasm.Ops
