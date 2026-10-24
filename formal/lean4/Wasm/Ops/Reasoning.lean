/-
Wasm.Ops.Reasoning — the two OWL tableau operations of the npm entry.

  tableauMaterialise(nquads)
    -> {"ok":true,"nquads":"…","addedCount":N,"budgetHit":true|false}
  tableauDlInconsistent(nquads)
    -> {"ok":true,"inconsistent":true|false,"rlAlone":true|false}

Envelopes follow `bin/npm-entry/entry_extras.ml` (`tableau_materialise_json`,
`tableau_dl_inconsistent_json`) member for member; `budgetHit` is an
addition (see below). Only the DEFAULT graph is read, as in the F* entry.
`nquads` is N-Triples text, as it is there.

`tableauMaterialise` runs the class-expression materialisation pass
(`OWL.Mat.materialiseWithBudget`, the port of `Tableau.fst`) with the
library's default work budget. `budgetHit` is `true` when that budget
ran out: the memberships the graph would have gained are then not all
computed, and a caller reading an ABSENT membership as a negative
answer is reading a cap, not a proof. The F* function had no budget.

`tableauDlInconsistent` is the DL-regime pipeline the Lean OWL probe
runs under `--dl` (`Harness/OwlProbe.lean`, `premiseClosure`): OWL RL
closure, one materialisation pass, OWL RL closure again, then the clash
decision `OWL.RL.detectClashPlus` (the table rows plus the three sound
extension rows — the predicate the probe scores ConsistencyTest and
InconsistencyTest against). `rlAlone` is the same decision over the
first closure only, so a caller can see the cases where the tableau
changes the answer. If the materialisation pass adds nothing, the second
closure is the first.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.NTriples
import L4Factoidal.OWL.RLClosure
import L4Factoidal.OWL.Materialise

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- `tableauMaterialise(nquads)`. -/
def tableauMaterialise (nq : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
    let g := ds.default
    let (m, budgetHit) :=
      L4Factoidal.OWL.Mat.materialiseWithBudget g L4Factoidal.OWL.Mat.defaultBudget
    match Graph.toNTriples m with
    | .error e => errJson s!"tableauMaterialise: serialisation: {e}"
    | .ok lines =>
        okWith [("nquads", .string lines),
                ("addedCount", .number (toString (m.length - g.length))),
                ("budgetHit", .bool budgetHit)]

/-- `tableauDlInconsistent(nquads)`. -/
def tableauDlInconsistent (nq : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
    let gRl := L4Factoidal.OWL.RL.closureFix ds.default
    let (gMat, _) :=
      L4Factoidal.OWL.Mat.materialiseWithBudget gRl L4Factoidal.OWL.Mat.defaultBudget
    let gDl :=
      if gMat.length == gRl.length then gRl
      else L4Factoidal.OWL.RL.closureFix gMat
    okWith [("inconsistent", .bool (L4Factoidal.OWL.RL.detectClashPlus gDl)),
            ("rlAlone", .bool (L4Factoidal.OWL.RL.detectClashPlus gRl))]

/-! ## Build-time checks (positive and negative) -/

private def rdfTypeNq : String := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"

#guard tableauDlInconsistent s!"<http://e/a> {rdfTypeNq} <http://e/C> .\n"
         == "{\"ok\":true,\"inconsistent\":false,\"rlAlone\":false}"
#guard tableauDlInconsistent
         ("<http://e/C> <http://www.w3.org/2002/07/owl#disjointWith> <http://e/D> .\n"
          ++ s!"<http://e/a> {rdfTypeNq} <http://e/C> .\n"
          ++ s!"<http://e/a> {rdfTypeNq} <http://e/D> .\n")
         == "{\"ok\":true,\"inconsistent\":true,\"rlAlone\":true}"
#guard (tableauDlInconsistent "garbage").startsWith "{\"ok\":false"
#guard ((tableauMaterialise s!"<http://e/a> {rdfTypeNq} <http://e/C> .\n").splitOn
         "\"addedCount\":0").length == 2
#guard (tableauMaterialise "garbage").startsWith "{\"ok\":false"

end L4Wasm.Ops
