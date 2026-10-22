/-
The JSON-object producer for the restricted, checked consistency path.

Only the dataset's default graph contributes logical axioms. The existing
whole-dataset RDF 1.1 refusal is retained. Unsupported default-graph syntax
and rejected certificates produce null, with no OWL-RL fallback. The default
certificate is .close; fuel does not control this fixed saturation check.

The theorem concerns the actual JSON AST field, including its first-match
lookup convention. It does not prove parsing, JSON serialization, extraction,
the JavaScript adapter, full OWL admission, or owlEntails correctness.
-/
import Wasm.Ops.Support
import L4Factoidal.OWL.AtomicDirect
import L4Factoidal.RDF.Rdf11Terms

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.JSON
open L4Factoidal.OWL

private def owlConsistencyRdf12Message : String :=
  "owlIsConsistent: the input holds an RDF 1.2 triple term or directional language-tagged "
  ++ "string; OWL 2 Mapping to RDF Graphs (section 3) and the OWL 2 Direct "
  ++ "Semantics define no rule for these terms "
  ++ "(https://github.com/danbri/factoidal/issues/873)"

private def owlConsistencyReason (verdict : CertifiedDecision.WireVerdict) : String :=
  match verdict.consistent with
  | some false => "a checked certificate proves a contradiction in the admitted atomic OWL fragment"
  | some true => "a checked model proves consistency in the admitted atomic OWL fragment"
  | none =>
      match verdict.reason with
      | some .unsupported =>
          "unsupported-syntax: the whole default graph is outside the admitted atomic OWL fragment (indeterminate)"
      | _ =>
          "incomplete-search: the bounded certificate checker did not establish a contradiction; no model is certified (indeterminate)"

/-- Certificates may come from any untrusted search. They are checked against
the ontology read from the original default graph, without RL preprocessing.
The certificate's origin is not a soundness hypothesis. -/
def owlConsistencyJsonWithCert (ds : Dataset) (certificate : Cert) : Json :=
  if !ds.isRdf11 then
    .object [("ok", .bool false), ("error", .string owlConsistencyRdf12Message)]
  else
    let verdict := AtomicDirect.decide ds.default certificate
    .object [("ok", .bool true),
      ("consistent", match verdict.consistent with
        | some answer => .bool answer
        | none => .null),
      ("reason", .string (owlConsistencyReason verdict))]

/-- Production policy: fixed saturation/closure certificate; no model route. -/
def owlConsistencyJson (ds : Dataset) : Json :=
  owlConsistencyJsonWithCert ds .close

/-- Exact JSON-field soundness for every dataset and every proposed certificate.
Definitive answers require whole-default-graph admission, as part of Meaning. -/
theorem owlConsistencyJsonWithCert_sound (ds : Dataset) (certificate : Cert) :
    AtomicDirect.Meaning ds.default
      ((owlConsistencyJsonWithCert ds certificate).getBool? "consistent") := by
  unfold owlConsistencyJsonWithCert
  split
  · simp [Json.getBool?, Json.field?, AtomicDirect.Meaning]
  · have sound := AtomicDirect.decide_sound ds.default certificate
    cases result : (AtomicDirect.decide ds.default certificate).consistent with
    | none =>
        simp [result, Json.getBool?, Json.field?, Json.asBool?, AtomicDirect.Meaning]
    | some answer =>
        simpa [result, Json.getBool?, Json.field?, Json.asBool?] using sound

theorem owlConsistencyJson_sound (ds : Dataset) :
    AtomicDirect.Meaning ds.default
      ((owlConsistencyJson ds).getBool? "consistent") :=
  owlConsistencyJsonWithCert_sound ds .close

/-- The present producer has no checked-model route, even with an arbitrary
certificate. Certificate rejection cannot become a positive verdict. -/
theorem owlConsistencyJsonWithCert_ne_true (ds : Dataset) (certificate : Cert) :
    (owlConsistencyJsonWithCert ds certificate).getBool? "consistent" ≠ some true := by
  have noTrue : (AtomicDirect.decide ds.default certificate).consistent ≠ some true := by
    unfold AtomicDirect.decide AtomicDirect.checkedRefutation
    split
    · simp [AtomicDirect.erase]
    · split <;> simp [AtomicDirect.erase]
  unfold owlConsistencyJsonWithCert
  split
  · simp [Json.getBool?, Json.field?]
  · cases result : (AtomicDirect.decide ds.default certificate).consistent with
    | none => simp [result, Json.getBool?, Json.field?, Json.asBool?]
    | some answer =>
        cases answer with
        | false => simp [result, Json.getBool?, Json.field?, Json.asBool?]
        | true => exact False.elim (noTrue result)

/-- Field presence and types are part of the success contract: unknown is an
explicit JSON null, never a missing or wrongly typed consistent field. -/
theorem owlConsistencyJsonWithCert_success_schema (ds : Dataset) (certificate : Cert)
    (rdf11 : ds.isRdf11 = true) :
    (owlConsistencyJsonWithCert ds certificate).field? "ok" = some (.bool true) ∧
    ((owlConsistencyJsonWithCert ds certificate).field? "consistent" = some .null ∨
      (owlConsistencyJsonWithCert ds certificate).field? "consistent" = some (.bool false)) ∧
    (∃ reason, (owlConsistencyJsonWithCert ds certificate).field? "reason" = some (.string reason)) ∧
    (owlConsistencyJsonWithCert ds certificate).field? "error" = none := by
  cases result : (AtomicDirect.decide ds.default certificate).consistent with
  | none => simp [owlConsistencyJsonWithCert, rdf11, result, Json.field?]
  | some answer =>
      cases answer with
      | false => simp [owlConsistencyJsonWithCert, rdf11, result, Json.field?]
      | true =>
          have excluded := owlConsistencyJsonWithCert_ne_true ds certificate
          simp [owlConsistencyJsonWithCert, rdf11, result,
            Json.getBool?, Json.field?, Json.asBool?] at excluded

/-- Refusals are error envelopes and do not contain a semantic verdict. -/
theorem owlConsistencyJsonWithCert_refusal_schema (ds : Dataset) (certificate : Cert)
    (rdf12 : ds.isRdf11 = false) :
    (owlConsistencyJsonWithCert ds certificate).field? "ok" = some (.bool false) ∧
    (∃ message, (owlConsistencyJsonWithCert ds certificate).field? "error" = some (.string message)) ∧
    (owlConsistencyJsonWithCert ds certificate).field? "consistent" = none ∧
    (owlConsistencyJsonWithCert ds certificate).field? "reason" = none := by
  simp [owlConsistencyJsonWithCert, rdf12, Json.field?]

theorem owlConsistencyJson_success_schema (ds : Dataset) (rdf11 : ds.isRdf11 = true) :
    (owlConsistencyJson ds).field? "ok" = some (.bool true) ∧
    ((owlConsistencyJson ds).field? "consistent" = some .null ∨
      (owlConsistencyJson ds).field? "consistent" = some (.bool false)) ∧
    (∃ reason, (owlConsistencyJson ds).field? "reason" = some (.string reason)) ∧
    (owlConsistencyJson ds).field? "error" = none :=
  owlConsistencyJsonWithCert_success_schema ds .close rdf11

theorem owlConsistencyJson_refusal_schema (ds : Dataset) (rdf12 : ds.isRdf11 = false) :
    (owlConsistencyJson ds).field? "ok" = some (.bool false) ∧
    (∃ message, (owlConsistencyJson ds).field? "error" = some (.string message)) ∧
    (owlConsistencyJson ds).field? "consistent" = none ∧
    (owlConsistencyJson ds).field? "reason" = none :=
  owlConsistencyJsonWithCert_refusal_schema ds .close rdf12

/-- No duplicate field can disagree with the field read by first-match lookup.
This applies to both successful verdicts and refusal envelopes. -/
theorem owlConsistencyJsonWithCert_unique_fields (ds : Dataset) (certificate : Cert) :
    ∃ fields, owlConsistencyJsonWithCert ds certificate = Json.object fields ∧
      (fields.map Prod.fst).Nodup := by
  unfold owlConsistencyJsonWithCert
  split
  · exact ⟨_, rfl, by change (["ok", "error"] : List String).Nodup; decide⟩
  · exact ⟨_, rfl, by change (["ok", "consistent", "reason"] : List String).Nodup; decide⟩

theorem owlConsistencyJson_unique_fields (ds : Dataset) :
    ∃ fields, owlConsistencyJson ds = Json.object fields ∧
      (fields.map Prod.fst).Nodup :=
  owlConsistencyJsonWithCert_unique_fields ds .close

#print axioms owlConsistencyJsonWithCert_sound
#print axioms owlConsistencyJson_sound
#print axioms owlConsistencyJsonWithCert_ne_true
#print axioms owlConsistencyJsonWithCert_success_schema
#print axioms owlConsistencyJsonWithCert_refusal_schema
#print axioms owlConsistencyJson_success_schema
#print axioms owlConsistencyJson_refusal_schema
#print axioms owlConsistencyJsonWithCert_unique_fields
#print axioms owlConsistencyJson_unique_fields

end L4Wasm.Ops
