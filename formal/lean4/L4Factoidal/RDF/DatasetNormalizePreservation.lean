/- Preservation for the actual operation normalizer, on its checked fast-path
subset. Typed literals already have canonical language tags. Empty named graph
declarations are removed by normalization; default-graph preservation has no
nonempty-name premise. No runtime definition is changed here. -/
import L4Factoidal.RDF.NormalizeSet
import L4Factoidal.RDF.DatasetDenotation

namespace L4Factoidal.RDF
open L4Factoidal.Syntax

/-- Canonical language tags are enforced by the Term type, including nested
triple terms. Normalization therefore changes no typed term. -/
theorem Term.lowerTags_eq_self (t : Term) : t.lowerTags = t := by
  calc
    t.lowerTags = t.lowerTags.joinKey := (Term.joinKey_eq_self _).symm
    _ = t.joinKey := Term.joinKey_lowerTags t
    _ = t := Term.joinKey_eq_self t

theorem Triple.lowerTags_eq_self (t : Triple) : t.lowerTags = t := by
  cases t
  simp [Triple.lowerTags, Term.lowerTags_eq_self]

theorem Graph.map_lowerTags_eq_self (g : Graph) : g.map Triple.lowerTags = g := by
  have h : Triple.lowerTags = id := funext Triple.lowerTags_eq_self
  rw [h, List.map_id]

/-- A certified set's default graph is preserved as a list, including order.
This does not claim preservation of empty named-graph declarations. -/
theorem normalizeDataset_default_of_isSet (ds : Dataset) (hs : ds.IsSet) :
    (normalizeDataset ds).default = ds.default := by
  rw [normalizeDataset_of_isSet ds hs]
  exact Graph.map_lowerTags_eq_self ds.default

/-- The actual runtime branch selected by the syntactic round-trip check. -/
theorem datasetForOps_safe_eq (mode : Mode) (ds : Dataset) (hs : ds.IsSet)
    (safe : roundTripSafe mode ds = true) :
    datasetForOps mode ds = .ok ds.normalizeSet := by
  simp [datasetForOps, safe, normalizeDataset_of_isSet ds hs]

/-- Exact reasoner input preservation on the normalizer's checked subset. -/
theorem datasetForOps_default_preserved (mode : Mode) (ds out : Dataset)
    (hs : ds.IsSet) (safe : roundTripSafe mode ds = true)
    (result : datasetForOps mode ds = .ok out) : out.default = ds.default := by
  rw [datasetForOps_safe_eq mode ds hs safe] at result
  have h := Except.ok.inj result
  subst out
  exact Graph.map_lowerTags_eq_self ds.default

/-- Foundation membership is preserved at the actual normalized default graph. -/
theorem datasetForOps_default_den (mode : Mode) (ds out : Dataset)
    (hs : ds.IsSet) (safe : roundTripSafe mode ds = true)
    (result : datasetForOps mode ds = .ok out) (t : Triple) :
    out.den.graph none t ↔ ds.den.graph none t := by
  change out.default.mem t = true ↔ ds.default.mem t = true
  rw [datasetForOps_default_preserved mode ds out hs safe result]

#print axioms Term.lowerTags_eq_self
#print axioms Triple.lowerTags_eq_self
#print axioms normalizeDataset_default_of_isSet
#print axioms datasetForOps_default_preserved
#print axioms datasetForOps_default_den
end L4Factoidal.RDF
