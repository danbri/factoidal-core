/-
The JSON-object producer for the restricted, checked consistency path.

Only the dataset's default graph contributes logical axioms. The existing
whole-dataset RDF 1.1 refusal is retained. Unsupported default-graph syntax,
rejected certificates and exhausted fuel produce null, with no OWL-RL
fallback. `true` needs a checked model (`AtomicModel.checkModel_sound`);
`false` needs a checked refutation (`DirectCert.checkCertFuel_sound`); `fuel`
bounds the model search and the certificate checker
(https://github.com/danbri/factoidal/issues/960).

The theorem concerns the actual JSON AST field, including its first-match
lookup convention. It does not prove parsing, JSON serialization, extraction,
the JavaScript adapter, or full OWL admission.
-/
import Wasm.Ops.Support
import L4Factoidal.OWL.AtomicModel
import L4Factoidal.RDF.Rdf11Terms

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.JSON
open L4Factoidal.OWL

private def owlConsistencyRdf12Message : String :=
  "owlIsConsistent: the input holds an RDF 1.2 triple term or directional language-tagged "
  ++ "string; OWL 2 Mapping to RDF Graphs (section 3) and the OWL 2 Direct "
  ++ "Semantics define no rule for these terms "
  ++ "(https://github.com/danbri/factoidal/issues/958)"

private def owlConsistencyReason (fuel : Nat) (verdict : CertifiedDecision.WireVerdict) : String :=
  match verdict.consistent with
  | some false =>
      "a checked certificate proves a contradiction in the admitted OWL fragment "
      ++ "(atomic classes, owl:someValuesFrom, owl:TransitiveProperty, annotations)"
  | some true => "a checked finite model proves consistency in the admitted OWL fragment"
  | none =>
      match verdict.reason with
      | some .unsupported =>
          "unsupported-syntax: the whole default graph is outside the admitted OWL fragment "
          ++ "(atomic classes, owl:someValuesFrom, owl:TransitiveProperty, annotations) (indeterminate)"
      | some .budgetExhausted =>
          s!"budget-out: the model search and the certificate checker used fuel {fuel} "
          ++ "rounds without a verdict (indeterminate); raise it via opts.fuel"
      | _ =>
          "incomplete-search: the certificate checker did not establish a contradiction "
          ++ "and no model is certified (indeterminate)"

/-- The consistency envelope at a fuel bound. A `true` answer carries no
`reason` field; `false` and `null` carry one. -/
def owlConsistencyJson (ds : Dataset) (fuel : Nat) : Json :=
  if !ds.isRdf11 then
    .object [("ok", .bool false), ("error", .string owlConsistencyRdf12Message)]
  else
    let verdict := AtomicModel.decideFuel ds.default fuel
    .object ([("ok", .bool true),
      ("consistent", match verdict.consistent with
        | some answer => .bool answer
        | none => .null)] ++
      (if verdict.consistent == some true then []
       else [("reason", .string (owlConsistencyReason fuel verdict))]))

/-- Exact JSON-field soundness for every dataset and every fuel. `true`
means the whole default graph is admitted and has a model; `false` means it
is admitted and has none (`AtomicDirect.Meaning`). -/
theorem owlConsistencyJson_sound (ds : Dataset) (fuel : Nat) :
    AtomicDirect.Meaning ds.default ((owlConsistencyJson ds fuel).getBool? "consistent") := by
  unfold owlConsistencyJson
  split
  · simp [Json.getBool?, Json.field?, AtomicDirect.Meaning]
  · have sound := AtomicModel.decideFuel_sound ds.default fuel
    cases result : (AtomicModel.decideFuel ds.default fuel).consistent with
    | none =>
        simp [result, Json.getBool?, Json.field?, Json.asBool?, AtomicDirect.Meaning]
    | some answer =>
        rw [result] at sound
        cases answer <;> simpa [result, Json.getBool?, Json.field?, Json.asBool?] using sound

/-- Field presence and types: `consistent` is a Boolean or an explicit null,
and `reason` is present exactly when the answer is not `true`. -/
theorem owlConsistencyJson_success_schema (ds : Dataset) (fuel : Nat)
    (rdf11 : ds.isRdf11 = true) :
    (owlConsistencyJson ds fuel).field? "ok" = some (.bool true) ∧
    ((owlConsistencyJson ds fuel).field? "consistent" = some .null ∨
      ∃ answer, (owlConsistencyJson ds fuel).field? "consistent" = some (.bool answer)) ∧
    ((owlConsistencyJson ds fuel).field? "consistent" = some (.bool true) ↔
      (owlConsistencyJson ds fuel).field? "reason" = none) ∧
    (owlConsistencyJson ds fuel).field? "error" = none := by
  cases result : (AtomicModel.decideFuel ds.default fuel).consistent with
  | none => simp [owlConsistencyJson, rdf11, result, Json.field?]
  | some answer =>
      cases answer <;> simp [owlConsistencyJson, rdf11, result, Json.field?]

/-- Refusals are error envelopes and do not contain a semantic verdict. -/
theorem owlConsistencyJson_refusal_schema (ds : Dataset) (fuel : Nat)
    (rdf12 : ds.isRdf11 = false) :
    (owlConsistencyJson ds fuel).field? "ok" = some (.bool false) ∧
    (∃ message, (owlConsistencyJson ds fuel).field? "error" = some (.string message)) ∧
    (owlConsistencyJson ds fuel).field? "consistent" = none ∧
    (owlConsistencyJson ds fuel).field? "reason" = none := by
  simp [owlConsistencyJson, rdf12, Json.field?]

/-- No duplicate field can disagree with the field read by first-match lookup.
This applies to both successful verdicts and refusal envelopes. -/
theorem owlConsistencyJson_unique_fields (ds : Dataset) (fuel : Nat) :
    ∃ fields, owlConsistencyJson ds fuel = Json.object fields ∧
      (fields.map Prod.fst).Nodup := by
  unfold owlConsistencyJson
  split
  · exact ⟨_, rfl, by change (["ok", "error"] : List String).Nodup; decide⟩
  · refine ⟨_, rfl, ?_⟩
    split <;> split <;> simp

#print axioms owlConsistencyJson_sound
#print axioms owlConsistencyJson_success_schema
#print axioms owlConsistencyJson_refusal_schema
#print axioms owlConsistencyJson_unique_fields

end L4Wasm.Ops
