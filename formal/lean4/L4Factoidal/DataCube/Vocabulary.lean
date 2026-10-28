/-
L4Factoidal.DataCube.Vocabulary — the IRIs of the RDF Data Cube vocabulary that
the normalization algorithm and the integrity constraints read.

Specification: The RDF Data Cube Vocabulary, W3C Recommendation 16 January 2014,
https://www.w3.org/TR/2014/REC-vocab-data-cube-20140116/ (namespace
`http://purl.org/linked-data/cube#`). The names carry the version `QB2014`, so a
later edition of the vocabulary is a new namespace here, not a silent change.
Tracking: https://github.com/danbri/factoidal/issues/1165 (RDF Data Cube).
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.DataCube.QB2014

open L4Factoidal.RDF

/-- The Data Cube namespace, `http://purl.org/linked-data/cube#`. -/
def qbNs : String := "http://purl.org/linked-data/cube#"

/-! ## Classes -/

def qbObservation            : WfIri := ⟨"http://purl.org/linked-data/cube#Observation", rfl⟩
def qbDataSet                : WfIri := ⟨"http://purl.org/linked-data/cube#DataSet", rfl⟩
def qbSlice                  : WfIri := ⟨"http://purl.org/linked-data/cube#Slice", rfl⟩
def qbSliceKey               : WfIri := ⟨"http://purl.org/linked-data/cube#SliceKey", rfl⟩
def qbDataStructureDefinition : WfIri :=
  ⟨"http://purl.org/linked-data/cube#DataStructureDefinition", rfl⟩
def qbDimensionProperty      : WfIri := ⟨"http://purl.org/linked-data/cube#DimensionProperty", rfl⟩
def qbMeasureProperty        : WfIri := ⟨"http://purl.org/linked-data/cube#MeasureProperty", rfl⟩
def qbAttributeProperty      : WfIri := ⟨"http://purl.org/linked-data/cube#AttributeProperty", rfl⟩
def qbHierarchicalCodeList   : WfIri := ⟨"http://purl.org/linked-data/cube#HierarchicalCodeList", rfl⟩

/-! ## Properties -/

def qbObservationP       : WfIri := ⟨"http://purl.org/linked-data/cube#observation", rfl⟩
def qbDataSetP           : WfIri := ⟨"http://purl.org/linked-data/cube#dataSet", rfl⟩
def qbSliceP             : WfIri := ⟨"http://purl.org/linked-data/cube#slice", rfl⟩
def qbStructure          : WfIri := ⟨"http://purl.org/linked-data/cube#structure", rfl⟩
def qbComponent          : WfIri := ⟨"http://purl.org/linked-data/cube#component", rfl⟩
def qbComponentProperty  : WfIri := ⟨"http://purl.org/linked-data/cube#componentProperty", rfl⟩
def qbComponentAttachment : WfIri := ⟨"http://purl.org/linked-data/cube#componentAttachment", rfl⟩
def qbComponentRequired  : WfIri := ⟨"http://purl.org/linked-data/cube#componentRequired", rfl⟩
def qbDimension          : WfIri := ⟨"http://purl.org/linked-data/cube#dimension", rfl⟩
def qbMeasure            : WfIri := ⟨"http://purl.org/linked-data/cube#measure", rfl⟩
def qbAttribute          : WfIri := ⟨"http://purl.org/linked-data/cube#attribute", rfl⟩
def qbMeasureType        : WfIri := ⟨"http://purl.org/linked-data/cube#measureType", rfl⟩
def qbSliceKeyP          : WfIri := ⟨"http://purl.org/linked-data/cube#sliceKey", rfl⟩
def qbSliceStructure     : WfIri := ⟨"http://purl.org/linked-data/cube#sliceStructure", rfl⟩
def qbCodeList           : WfIri := ⟨"http://purl.org/linked-data/cube#codeList", rfl⟩
def qbHierarchyRoot      : WfIri := ⟨"http://purl.org/linked-data/cube#hierarchyRoot", rfl⟩
def qbParentChildProperty : WfIri := ⟨"http://purl.org/linked-data/cube#parentChildProperty", rfl⟩

/-! ## Other vocabularies the constraints name -/

def skosConcept       : WfIri := ⟨"http://www.w3.org/2004/02/skos/core#Concept", rfl⟩
def skosConceptScheme : WfIri := ⟨"http://www.w3.org/2004/02/skos/core#ConceptScheme", rfl⟩
def skosCollection    : WfIri := ⟨"http://www.w3.org/2004/02/skos/core#Collection", rfl⟩
def skosInScheme      : WfIri := ⟨"http://www.w3.org/2004/02/skos/core#inScheme", rfl⟩
def skosMember        : WfIri := ⟨"http://www.w3.org/2004/02/skos/core#member", rfl⟩
def owlInverseOf      : WfIri := ⟨"http://www.w3.org/2002/07/owl#inverseOf", rfl⟩

end L4Factoidal.DataCube.QB2014
