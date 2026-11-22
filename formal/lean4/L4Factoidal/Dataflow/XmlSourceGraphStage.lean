import L4Factoidal.Dataflow.Stage
import L4Factoidal.RDF.Graph

/-!
# Source-partitioned XML -> JSON-LD dataset ingestion

A JSON-LD reader may produce named graphs. The *simple-triples*
XML ingestion profile accepts only an RDF default graph; it refuses
JSON-LD documents with named graphs instead of silently losing them.

Each accepted source graph gets exactly one IRI name in the destination
dataset. The original Factoidal Dataflow.Stage composes the two pure
steps with a proof of their contracts. File access, XML processing and
XSLT remain host/IO stages with separate obligations.
-/
namespace L4Factoidal.Dataflow.XmlSourceGraphStage

open L4Factoidal.RDF
open L4Factoidal.Dataflow

/-- Refuse unexpectedly named JSON-LD graphs: converting them to a
    source named graph would otherwise erase their graph identity. -/
def defaultOnly (source : RDF.Dataset) : Except String RDF.Graph :=
  match source.named with
  | [] => .ok source.default
  | _ => .error "Expected JSON-LD simple triples, not a named dataset"

/-- This contract mentions the exact original RDF graph (not a bag
    of triples, and not a lossy concatenation). -/
def defaultOnlyStage : Stage String RDF.Dataset RDF.Graph where
  run := defaultOnly
  contract := fun source result =>
    source.named = [] ∧ result = source.default
  sound := by
    intro source result h
    cases hn : source.named with
    | nil =>
        simp only [defaultOnly, hn] at h
        cases h
        exact ⟨rfl, rfl⟩
    | cons ng tail =>
        simp [defaultOnly, hn] at h

/-- A source document always occupies its own named graph. -/
def sourceDataset (name : WfIri) (graph : RDF.Graph) : RDF.Dataset :=
  { default := [], named := [{name := .iri name, graph := graph}] }

/-- This stage does not merge duplicate RDF assertions into a multiset;
    RDF graph identity and set semantics remain the underlying model. -/
def assignNamedStage (name : WfIri) : Stage String RDF.Graph RDF.Dataset :=
  Stage.ofFun (sourceDataset name)
    (fun graph result => result = sourceDataset name graph)
    (by intro graph; rfl)

/-- Original Dataflow contract composition: JSON-LD default graph
    validation followed by one source-named RDF dataset. -/
def ingestSourceStage (name : WfIri) :
    Stage String RDF.Dataset RDF.Dataset :=
  defaultOnlyStage.comp (assignNamedStage name)

/-- The named graph's RDF statements are the exact accepted input graph. -/
theorem sourceDataset_lookup (name : WfIri) (graph : RDF.Graph) :
    (sourceDataset name graph).lookupNamed (.iri name) = some graph := by
  simp [sourceDataset, RDF.Dataset.lookupNamed]

theorem sourceDataset_default (name : WfIri) (graph : RDF.Graph) :
    (sourceDataset name graph).default = [] := rfl

theorem sourceDataset_one_name (name : WfIri) (graph : RDF.Graph) :
    (sourceDataset name graph).named.map (·.name) = [.iri name] := rfl

/-- A successful whole stage retains the exact graph under precisely
    the chosen source IRI. -/
theorem ingestSourceStage_exact (name : WfIri) (source out : RDF.Dataset)
    (h : (ingestSourceStage name).run source = .ok out) :
    source.named = [] ∧
    out = sourceDataset name source.default := by
  cases hn : source.named with
  | nil =>
      simp only [ingestSourceStage, Stage.comp, defaultOnlyStage,
        assignNamedStage, defaultOnly, hn, Stage.ofFun] at h
      cases h
      exact ⟨rfl, rfl⟩
  | cons ng rest =>
      simp [ingestSourceStage, Stage.comp, defaultOnlyStage,
        defaultOnly, hn] at h

#print axioms sourceDataset_lookup
#print axioms ingestSourceStage_exact

end L4Factoidal.Dataflow.XmlSourceGraphStage
