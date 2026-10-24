/-
L4Factoidal.Dataflow.Validator — the interface type of a SHACL validator
(https://github.com/danbri/factoidal/issues/975, "Architecture acceptance",
item 2, kind VALIDATOR).

## The semantics

`CoreConformance cfg data shapesRaw` is SHACL section 3.4 conformance
(`Spec.GraphConforms`) of the data graph to the shapes graph decoded from
`shapesRaw`, under the configuration `validatorCfg` (SHACL 1.2 node
expressions read from the shapes graph). `FullConformance` adds the
SHACL-SPARQL conditions (`Spec.GraphConformsWithSparql`, SHACL Part 2).

## The interface type

`LawfulValidator` holds a configuration, a `run` from the data graph and the
raw shapes graph to a report, and:

* `sound`: a conforming report implies `CoreConformance`. Proved by every value;
* `assumed_spec_iff`: a NAMED ASSUMPTION (`IOStage` style, a `Prop` the value
  does not prove), fixed by `spec_iff_stmt` to `ExactStatement`: when the run
  has no failure, the report conforms exactly when `FullConformance` holds.

The proved part of the exactness is `shaclValidator_conforms_iff_passes`: the
report conforms exactly when Core conformance holds and the two SHACL-SPARQL
passes (`sparqlViolationsForShape`, `customViolationsForShape`) report no
violation. The step from the two passes to the quantifiers of
`Spec.GraphConformsWithSparql` is the open obligation (the module header of
`SHACL/SparqlTheorems.lean`, item 2 of "not covered"); it is the content of
`assumed_spec_iff`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SHACL.NodeExpr
import L4Factoidal.SHACL.SparqlTheorems

namespace L4Factoidal.Dataflow

open L4Factoidal.SHACL

/-- The configuration `validateFull` evaluates with. -/
def validatorCfg (cfg : ValidationConfig) (data shapesRaw : RDF.Graph) : ValidationConfig :=
  { cfg with evalExpr := nodeExprEvaluator shapesRaw data }

/-- SHACL section 3.4 conformance of `data` to the decoded shapes graph. -/
def CoreConformance (cfg : ValidationConfig) (data shapesRaw : RDF.Graph) : Prop :=
  Spec.GraphConforms ((validatorCfg cfg data shapesRaw).envFor data
    (decodeShapesGraph shapesRaw).shapes) data (decodeShapesGraph shapesRaw)

/-- Core conformance and the SHACL-SPARQL conditions (SHACL Part 2). -/
def FullConformance (cfg : ValidationConfig) (data shapesRaw : RDF.Graph) : Prop :=
  Spec.GraphConformsWithSparql ((validatorCfg cfg data shapesRaw).envFor data
    (decodeShapesGraph shapesRaw).shapes) data shapesRaw (decodeShapesGraph shapesRaw)

/-- Exactness, as a statement. -/
def ExactStatement (cfg : ValidationConfig)
    (run : RDF.Graph × RDF.Graph → Except String ValidationReport) : Prop :=
  ∀ inp r, run inp = .ok r → r.failure = none →
    (r.conforms = true ↔ FullConformance cfg inp.1 inp.2)

/-- **A validator, with soundness against the SHACL semantics as a field.** -/
structure LawfulValidator where
  cfg : ValidationConfig
  /-- Data graph and raw shapes graph to the report; the error is a shapes
  graph the validator refuses. -/
  run : RDF.Graph × RDF.Graph → Except String ValidationReport
  /-- A conforming report implies SHACL Core conformance. -/
  sound : ∀ inp r, run inp = .ok r → r.conforms = true → CoreConformance cfg inp.1 inp.2
  /-- NAMED ASSUMPTION: the report is exact against `FullConformance`. Not
  proved by this value. -/
  assumed_spec_iff : Prop
  spec_iff_stmt : assumed_spec_iff = ExactStatement cfg run

/-- The refusal text: the unsupported features of the shapes graph. -/
def refusalText (sg : ShapesGraph) : String := String.intercalate ", " sg.unsupported

/-- The shipped validator, with configuration `cfg`: decode the shapes graph,
refuse one with unsupported features, else `validateFull`. -/
def shaclValidatorWith (cfg : ValidationConfig) : LawfulValidator where
  cfg := cfg
  run inp :=
    let sg := decodeShapesGraph inp.2
    if sg.unsupported.isEmpty then .ok (validateFull inp.1 inp.2 sg cfg)
    else .error (refusalText sg)
  sound := by
    rintro ⟨data, shapes⟩ r h hc
    dsimp only at h
    split at h
    · injection h with h
      subst h
      unfold validateFull at hc
      split at hc
      · simp at hc
      · exact validateWithSparql_sound_core data shapes _ _ hc
    · cases h
  assumed_spec_iff := ExactStatement cfg (fun inp =>
    let sg := decodeShapesGraph inp.2
    if sg.unsupported.isEmpty then .ok (validateFull inp.1 inp.2 sg cfg)
    else .error (refusalText sg))
  spec_iff_stmt := rfl

/-- The validator with the default configuration (the `shaclValidate` op). -/
def shaclValidator : LawfulValidator := shaclValidatorWith {}

/-- **The proved part of exactness.** Without a failure, the report conforms
exactly when Core conformance holds and the two SHACL-SPARQL passes report no
violation. -/
theorem shaclValidator_conforms_iff_passes (cfg : ValidationConfig) (data shapesRaw : RDF.Graph)
    (r : ValidationReport) (h : (shaclValidatorWith cfg).run (data, shapesRaw) = .ok r)
    (hf : r.failure = none) :
    r.conforms = true ↔
      (let sg := decodeShapesGraph shapesRaw
       let cfg' := validatorCfg cfg data shapesRaw
       Spec.GraphConforms (cfg'.envFor data sg.shapes) data sg ∧
       (∀ s ∈ sg.shapes,
         (cfg'.envFor data sg.shapes).conforms
           (sparqlViolationsForShape (cfg'.envFor data sg.shapes) data shapesRaw sg.shapes
              (distinctSubjects data) s).results = true) ∧
       (∀ s ∈ sg.shapes,
         (cfg'.envFor data sg.shapes).conforms
           (customViolationsForShape (cfg'.envFor data sg.shapes) data (distinctSubjects data)
              sg.shapes s (validateFuel sg.shapes)).results = true)) := by
  dsimp only [shaclValidatorWith] at h
  split at h
  · injection h with h
    subst h
    unfold validateFull at hf ⊢
    split at hf
    · rename_i hs
      simp [hs] at hf
    · rename_i hs
      simp only [hs]
      exact validateWithSparql_conforms_iff _ _ _ _
  · cases h

#print axioms shaclValidatorWith
#print axioms shaclValidator_conforms_iff_passes

end L4Factoidal.Dataflow
