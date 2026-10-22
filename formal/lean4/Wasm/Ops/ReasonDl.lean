/-
Wasm.Ops.ReasonDl — checked atomic OWL consistency and legacy OWL entailment.
Consistency reads the original default graph; entailment still uses RL closure.

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

Consistency uses the restricted AtomicDirect reader and actual certificate
checker through ReasonDlCertified. Unsupported syntax returns unknown with
no unchecked fallback. This is an explicit capability reduction in the local
repair; general OWL reasoning and positive model construction are unfinished.

Entailment below still uses the legacy RL/refuter route. Its punning refusal
is limited and is not a Direct Semantics soundness proof. Consistency's new
proof must not be presented as certifying that separate operation.
Record: `docs/20261021-owl-public-boundary.md`. -/

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
(https://github.com/danbri/factoidal/issues/873). The verdicts below are OWL 2
Direct Semantics verdicts. The RDF graph is read as an OWL 2 ontology by OWL 2
Mapping to RDF Graphs (§3, Mapping from RDF Graphs to the Structural
Specification), which is stated on RDF 1.1 graphs and has no rule for a
triple term; the OWL 2 Direct Semantics has no interpretation of one. Design
record: `docs/designissues/2026-10-18-rdf12-terms-canon-and-closures.md`. -/
def owlDlRdf12Refusal (op : String) : String :=
  s!"{op}: the input holds an RDF 1.2 triple term or directional language-tagged "
  ++ "string; OWL 2 Mapping to RDF Graphs (section 3) and the OWL 2 Direct "
  ++ "Semantics define no rule for these terms "
  ++ "(https://github.com/danbri/factoidal/issues/873)"

def owlDlPunningReason : String :=
  "unsupported-punning: a class or property IRI is also used as an individual; "
  ++ "the RDF-based closure does not preserve OWL Direct Semantics punning "
  ++ "(indeterminate)"

/-- Checked consistency over the original default graph. Unsupported syntax
and rejected certificates return null. The compatibility options argument
is retained; fuel does not change the fixed certificate-checker bound. -/
def owlIsConsistentParsed (ds : Dataset) (_optsJson : String) : String :=
  (owlConsistencyJson ds).toString

/-- The actual string producer serializes a JSON object whose definitive
field satisfies the original-default-graph contract. JSON serialization and
external parsing remain separate artifact-test boundaries. -/
theorem owlIsConsistentParsed_certified (ds : Dataset) (optsJson : String) :
    ∃ response : Json,
      owlIsConsistentParsed ds optsJson = response.toString ∧
      L4Factoidal.OWL.AtomicDirect.Meaning ds.default (response.getBool? "consistent") := by
  exact ⟨owlConsistencyJson ds, rfl, owlConsistencyJson_sound ds⟩

/-- `owlIsConsistent(nquads, optsJson)`. -/
def owlIsConsistent (nq optsJson : String) : String :=
  match parseNQuadsFast nq .rdf12 with
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
  simpa only [owlIsConsistent, parsed] using owlIsConsistentParsed_certified ds optsJson

#print axioms owlIsConsistentParsed_certified
#print axioms owlIsConsistent_certified

/-- `owlEntails(premiseNquads, conclusionNquads, optsJson)`. The two
positive paths: `via:"closure"` when every conclusion
triple is exactly (engine triple equality) in the OWL-RL closure of
the premise; `via:"refutation"` when the negated conclusion
(`negationGoals`) is refuted on every goal. Without a checked countermodel,
absence from the closure and quiescent search both answer `null`. -/
def owlEntailsParsed (dsP dsC : Dataset) (optsJson : String) : String :=
  if !(dsP.isRdf11 && dsC.isRdf11) then errJson (owlDlRdf12Refusal "owlEntails") else
  if L4Factoidal.OWL.DirectProfile.hasUnsupportedPunning (dsP.default ++ dsC.default) then
    okWith [("entailed", .null), ("via", .string "closure"),
            ("reason", .string owlDlPunningReason)]
  else
      let gc := dsC.default
      let closure := L4Factoidal.OWL.RL.closureFix dsP.default
      let fuel := owlRefuteFuelOfOpts optsJson
      if gc.all (fun t => Graph.mem t closure) then
        okWith [("entailed", .bool true), ("via", .string "closure")]
      else
        match L4Factoidal.OWL.Refute.negationGoals gc with
        | none =>
            okWith [("entailed", .null), ("via", .string "closure"),
                    ("reason", .string
                      ("unsupported-conclusion: not in the OWL-RL closure, "
                       ++ "and the conclusion form cannot be soundly negated "
                       ++ "for refutation (indeterminate)"))]
        | some goals =>
          let results := goals.map (fun neg =>
            L4Factoidal.OWL.Refute.tableauConsistent (closure ++ neg) fuel)
          if results.all (· == some false) then
            okWith [("entailed", .bool true), ("via", .string "refutation")]
          else if results.any (· == some true) then
            okWith [("entailed", .null), ("via", .string "refutation"),
                    ("reason", .string
                      ("incomplete-search: a negated conclusion was not "
                       ++ "refuted, but the search does not certify a "
                       ++ "countermodel (indeterminate)"))]
          else
            okWith [("entailed", .null), ("via", .string "refutation"),
                    ("reason", .string
                      (s!"budget-out: a refutation goal exhausted fuel {fuel} "
                       ++ "before closing (indeterminate); raise it via "
                       ++ "opts.fuel"))]

/-- `owlEntails(premiseNquads, conclusionNquads, optsJson)`. -/
def owlEntails (premiseNq conclusionNq optsJson : String) : String :=
  match parseNQuadsFast premiseNq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok dsP =>
    match parseNQuadsFast conclusionNq .rdf12 with
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
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

def owlEntailsOf (dsP dsC : Dataset) (optsJson : String) : String :=
  withOpsDataset .rdf12 dsP (fun p => withOpsDataset .rdf12 dsC (fun c => owlEntailsParsed p c optsJson))

theorem owlEntailsOf_eq (dsP dsC : Dataset) (optsJson : String) :
    owlEntailsOf dsP dsC optsJson =
      owlEntails (Dataset.toCanonicalNQuads dsP) (Dataset.toCanonicalNQuads dsC) optsJson := by
  unfold owlEntailsOf owlEntails
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads dsP) .rdf12 with
  | error e => rfl
  | ok p =>
      simp only [withOpsDataset_eq]
      cases parseNQuadsFast (Dataset.toCanonicalNQuads dsC) .rdf12 <;> rfl

/-! ### RDF 1.2 input (https://github.com/danbri/factoidal/issues/873) -/

#guard owlIsConsistent "<http://example.com/a> <http://example.com/says> <<( <http://example.com/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> )>> .\n<http://example.com/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.com/D> .\n<http://example.com/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> .\n" "" == errJson (owlDlRdf12Refusal "owlIsConsistent")
#guard owlEntails "<http://example.com/a> <http://example.com/says> <<( _:b1 <http://example.com/p> <http://example.com/o> )>> .\n" "<http://example.com/a> <http://example.com/says> <<( _:b1 <http://example.com/p> <http://example.com/o> )>> .\n" "" == errJson (owlDlRdf12Refusal "owlEntails")
#guard (owlIsConsistent "<http://example.com/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> .\n" "").startsWith
  "{\"ok\":true,\"consistent\":null"

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
#guard (owlIsConsistent (sameNq "a" "b") "").startsWith
  "{\"ok\":true,\"consistent\":null"
#guard (owlIsConsistent (differentNq "a" "b") "").startsWith
  "{\"ok\":true,\"consistent\":null"

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
