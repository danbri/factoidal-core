import L4Factoidal.RIF.Saturate

namespace L4Factoidal.RIF

/-- Direction-bearing literals cannot be silently converted to PlainLiteral. -/
theorem rdf_direction_unmapped (l : RDF.WfLiteral) (h : l.val.direction.isSome = true) :
    RdfMapping.gOfTerm (.literal l) = none := by
  simp [RdfMapping.gOfTerm, h]

/-- Consumers obtain no complete graph when any completeness condition fails. -/
theorem saturation_incomplete_no_graph (r : Saturate.Result) (h : r.complete = false) :
    r.completeGraph? = none := by simp [Saturate.Result.completeGraph?, h]

theorem saturation_complete_graph (r : Saturate.Result) (h : r.complete = true) :
    r.completeGraph? = some r.partialGraph := by simp [Saturate.Result.completeGraph?, h]

#print axioms rdf_direction_unmapped
#print axioms saturation_incomplete_no_graph
#print axioms saturation_complete_graph

end L4Factoidal.RIF
