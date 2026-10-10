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
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.NegationGoals

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

/-- `owlIsConsistent(nquads, optsJson)`. `reason` is a plumbing-level
description of the verdict source (there is no clash-trace string in
the refuter); present on the false/null verdicts, omitted on true. -/
def owlIsConsistent (nq optsJson : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
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

/-- `owlEntails(premiseNquads, conclusionNquads, optsJson)`. The two
verified paths of the F* entry: `via:"closure"` when every conclusion
triple is exactly (engine triple equality) in the OWL-RL closure of
the premise; `via:"refutation"` when the negated conclusion
(`negationGoals`) is refuted on every goal. A satisfiable goal is a
countermodel (`entailed:false`); an indeterminate goal with no
countermodel is `null`. -/
def owlEntails (premiseNq conclusionNq optsJson : String) : String :=
  match parseNQuadsFast premiseNq with
  | .error e => errJson (fmtParseError e)
  | .ok dsP =>
    match parseNQuadsFast conclusionNq with
    | .error e => errJson (fmtParseError e)
    | .ok dsC =>
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

end L4Wasm.Ops
