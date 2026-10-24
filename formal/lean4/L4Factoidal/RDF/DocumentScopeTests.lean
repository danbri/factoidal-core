/-
Tests of the shipped document scope (`renameDatasetBnodes`, used by the Wasm
operations `datasetOpen` and `parseToDatasetJson`) against
`Dataset.scopeDocument` (https://github.com/danbri/factoidal/issues/975,
phase C).
-/
import L4Factoidal.RDF.DocumentScope
import L4Factoidal.RDF.DatasetMerge

namespace L4Factoidal.RDF.DocumentScopeTests

open L4Factoidal.RDF

private def p : WfIri := ⟨"urn:p", by decide⟩
private def q : WfIri := ⟨"urn:q", by decide⟩
private def o : Term := .literal (Literal.string "x")

/-- `_:b0 urn:p <<( _:b0 urn:q "x" )>>`: one blank node, at the top level and
inside a triple term. -/
private def nested : Dataset :=
  { default := [⟨.bnode "b0", p, .tripleTerm (.bnode "b0") q o⟩],
    named := [{ name := .bnode "b0", graph := [⟨.bnode "b1", p, o⟩] }] }

/-! The document scope of the Wasm operations gives the scoped dataset: the
blank node inside the triple term gets the same label as the one outside it. -/

#guard renameDatasetBnodes (docScope 0) nested == nested.scopeDocument 0
#guard (renameDatasetBnodes (docScope 0) nested).bnodes.length == nested.bnodes.length

end L4Factoidal.RDF.DocumentScopeTests
