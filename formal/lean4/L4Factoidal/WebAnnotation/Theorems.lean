/-
L4Factoidal.WebAnnotation.Theorems — how the Web Annotation
Recommendations (Data Model and Vocabulary, 2017-02-23) relate to the
specifications they build on, and properties of the suite's test procedure.

Versions are in the names: `wa2017` is the Web Annotation Recommendations
of 2017, `jsonld11` the JSON-LD 1.1 API (Recommendation, 2020), `yamlld10`
YAML-LD 1.0 (Editor's Draft, commit `fafcf7ae` of json-ld/yaml-ld). A later
version of any of them is a new theorem with its own name.

* Data Model §1.3 and Appendix A: an annotation's RDF is the JSON-LD 1.1
  deserialisation of its JSON-LD form with the `anno.jsonld` context
  (`wa2017_toRdf_eq_jsonld11_toRdf`, `wa2017_expand_eq_jsonld11_expand`).
  There is no Web-Annotation-specific RDF mapping to keep in step.
* The same annotation written as YAML-LD 1.0 gives the same dataset
  (`wa2017_yamlld10_toRdf`), by `yamlld10_toRdf_eq_jsonld11_toRdf`.
* The test procedure of `annotation-model/scripts/JSONtest.js`: a failure
  is hidden only when its level is listed in `skipFailures`
  (`runSchema_hidden_only_if_skipped`), so a MUST failure is always reported
  in the `*Musts.test` files, which list none; a document passes a `.test`
  file only when every reported subtest passes (`testVerdict_pass_iff`).
-/
import L4Factoidal.WebAnnotation.JsonTest
import L4Factoidal.WebAnnotation.Vocab
import L4Factoidal.YAMLLD.Theorems

namespace L4Factoidal.WebAnnotation

open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.JSONSchema

/-! ## Web Annotation 2017 and JSON-LD 1.1 -/

/-- Data Model 2017 §1.3: an annotation's RDF dataset is the JSON-LD 1.1
    API §8.2 deserialisation of the document. -/
theorem wa2017_toRdf_eq_jsonld11_toRdf (loader : Loader) (doc : Json) :
    toRdfWa loader doc = parseJsonLdRoot loader doc none none none none := rfl

/-- Vocabulary test 1 is JSON-LD 1.1 API §5.1 expansion, nothing else. -/
theorem wa2017_expand_eq_jsonld11_expand (loader : Loader) (doc : Json) :
    expandWa loader doc = expandRoot loader doc none none none := rfl

/-- A Web Annotation 2017 document read from JSON text gives the dataset
    that JSON-LD 1.1 gives for that text. -/
theorem wa2017_text_toRdf (loader : Loader) (t : String) (doc : Json)
    (ht : parseJson t = .ok doc) :
    parseJsonLd loader t none none none none = toRdfWa loader doc := by
  unfold parseJsonLd toRdfWa
  rw [ht]

/-- The same annotation written as YAML-LD 1.0 (same internal
    representation) gives the same dataset as its JSON-LD form. -/
theorem wa2017_yamlld10_toRdf (loader : Loader) (y t : String) (opts : YAMLLD.Options)
    (doc : Json) (hy : YAMLLD.load y opts = .ok doc) (ht : parseJson t = .ok doc) :
    YAMLLD.toRdfYamlLd loader y none none none none opts =
      YAMLLD.liftJsonLd (toRdfWa loader doc) := by
  rw [YAMLLD.yamlld10_toRdf_eq_jsonld11_toRdf loader y t opts none none none none doc hy ht,
    wa2017_text_toRdf loader t doc ht]

/-! ## The JSONtest.js procedure -/

/-- With no `expectedResult` member, the expected result is `valid`. -/
theorem determineResult_default (a : Json) (h : a.field? "expectedResult" = none)
    (valid : Bool) : determineResult a valid = valid := by
  simp [determineResult, expectsInvalid, strField?, h]

/-- An expected result never stops the run. -/
theorem determineAction_expected (a : Json) : determineAction a true = .continue_ := by
  simp [determineAction]

/-- `runSchema` reports nothing only for an unexpected result at a level
    that the `.test` file lists in `skipFailures`. -/
theorem runSchema_hidden_only_if_skipped (env : Env) (lvl idx : Nat) (file : String)
    (a content : Json) (h : (runSchema env lvl idx file a content).1 = []) :
    env.skipFailures.contains (levelOf a) = true := by
  unfold runSchema at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · simp at h
    · rename_i hrep
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hrep
      revert hrep
      cases determineResult a _ <;> simp_all

/-- A `.test` file passes on a document exactly when every reported
    subtest passes. -/
theorem testVerdict_pass_iff (subs : List Subtest) :
    testVerdict subs = .pass ↔ ∀ s ∈ subs, s.verdict = .pass := by
  unfold testVerdict
  constructor
  · intro h s hs
    by_cases hf : subs.any (·.verdict == .fail) = true
    · simp [hf] at h
    · by_cases hu : subs.any (·.verdict == .undetermined) = true
      · simp [hf, hu] at h
      · simp only [List.any_eq_true, not_exists, not_and] at hf hu
        cases hv : s.verdict
        · rfl
        · exact absurd (by rw [hv]; rfl) (hf s hs)
        · exact absurd (by rw [hv]; rfl) (hu s hs)
  · intro h
    have hf : subs.any (·.verdict == .fail) = false := by
      simp only [List.any_eq_false]
      intro s hs; rw [h s hs]; decide
    have hu : subs.any (·.verdict == .undetermined) = false := by
      simp only [List.any_eq_false]
      intro s hs; rw [h s hs]; decide
    simp [hf, hu]

end L4Factoidal.WebAnnotation
