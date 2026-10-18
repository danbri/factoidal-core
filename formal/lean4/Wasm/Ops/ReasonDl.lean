/-
Wasm.Ops.ReasonDl — owlIsConsistent / owlEntails: OWL DL reasoning by
refutation over the OWL 2 RL closure.

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
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.OWL.RLClosure
-- The `@[csimp]` theorem that makes `OWL.RL.closureFix` compile to the
-- indexed closure (see the note in `Wasm/Ops/Reason.lean`).
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.NegationGoals
import Wasm.Ops.FromDataset
import L4Factoidal.RDF.Rdf11Terms

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-! ## OWL DL reasoning by refutation (issue 586)

The chain is the F* npm entry's, engine for engine: the OWL-RL
closure of the default graph, then the three-valued clash-detecting
tableau (`L4Factoidal.OWL.Refute.tableauConsistent`, mirroring
`Tableau_Refute.tableau_consistent`). The Lean closure is this
tree's standard `OWL.RL.closureFix` (the same one `owlClosure`'s
"OWL-RL" mode serves; the F* entry reaches the equivalent rows
through `owl_rl_closure_with_reflexivity`, fuel 100 — same
architecture, no layering here). The `none` verdict is reported as
`null` with a budget-out reason, never a silent `false`.
No reasoning logic lives here: closure, refuter and `negationGoals`
are all `L4Factoidal` library code; these ops only parse, dispatch
and shape the JSON verdict. -/

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

/-- `owlIsConsistent(nquads, optsJson)`. `reason` is a plumbing-level
description of the verdict source (there is no clash-trace string in
the refuter); present on the false/null verdicts, omitted on true. -/
def owlIsConsistentParsed (ds : Dataset) (optsJson : String) : String :=
  if !ds.isRdf11 then errJson (owlDlRdf12Refusal "owlIsConsistent") else
    let closure := L4Factoidal.OWL.RL.closureFix ds.default
    let fuel := owlRefuteFuelOfOpts optsJson
    match L4Factoidal.OWL.Refute.tableauConsistent closure fuel with
    | some false =>
        okWith [("consistent", .bool false),
                ("reason", .string
                  ("the clash-detecting tableau derived a contradiction "
                   ++ "on every branch of the OWL-RL closure"))]
    | some true => okWith [("consistent", .bool true)]
    | none =>
        okWith [("consistent", .null),
                ("reason", .string
                  (s!"budget-out: tableau refutation fuel {fuel} exhausted "
                   ++ "before every branch closed (indeterminate, not "
                   ++ "inconsistent); raise it via opts.fuel"))]

/-- `owlIsConsistent(nquads, optsJson)`. -/
def owlIsConsistent (nq optsJson : String) : String :=
  match parseNQuadsFast nq .rdf12 with
  | .error e => errJson (fmtParseError e)
  | .ok ds => owlIsConsistentParsed ds optsJson

/-- `owlEntails(premiseNquads, conclusionNquads, optsJson)`. The two
verified paths of the F* entry: `via:"closure"` when every conclusion
triple is exactly (engine triple equality) in the OWL-RL closure of
the premise; `via:"refutation"` when the negated conclusion
(`negationGoals`) is refuted on every goal. A satisfiable goal is a
countermodel (`entailed:false`); an indeterminate goal with no
countermodel is `null`. -/
def owlEntailsParsed (dsP dsC : Dataset) (optsJson : String) : String :=
  if !(dsP.isRdf11 && dsC.isRdf11) then errJson (owlDlRdf12Refusal "owlEntails") else
      let gc := dsC.default
      let closure := L4Factoidal.OWL.RL.closureFix dsP.default
      let fuel := owlRefuteFuelOfOpts optsJson
      if gc.all (fun t => Graph.mem t closure) then
        okWith [("entailed", .bool true), ("via", .string "closure")]
      else
        match L4Factoidal.OWL.Refute.negationGoals gc with
        | none =>
            okWith [("entailed", .bool false), ("via", .string "closure"),
                    ("reason", .string
                      ("not in the OWL-RL closure, and the conclusion form "
                       ++ "cannot be soundly negated for refutation"))]
        | some goals =>
          let results := goals.map (fun neg =>
            L4Factoidal.OWL.Refute.tableauConsistent (closure ++ neg) fuel)
          if results.all (· == some false) then
            okWith [("entailed", .bool true), ("via", .string "refutation")]
          else if results.any (· == some true) then
            okWith [("entailed", .bool false), ("via", .string "refutation"),
                    ("reason", .string
                      ("a model satisfying the premise and the negated "
                       ++ "conclusion was constructed (conclusion not "
                       ++ "entailed)"))]
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
  "{\"ok\":true,\"consistent\":true"

end L4Wasm.Ops
