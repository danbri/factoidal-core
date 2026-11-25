import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GraphEvaluate

/-!
# PVGraph — the public Lean GDSL dataflow API

RDF `Graph` is a distinct mathematical object in Factoidal.
GDSL's shared operator/port/link dataflow document is explicitly
called `PVGraph`. The earlier internal modules retain their
implementation names, but should not define public RDF terminology.

Every domain-specific GDSL application must build on this one PVGraph
dataflow representation. This is a pure/typed admission and evaluation
API, not a verified GPU implementation.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage

abbrev PVGraph := Graph.Document

namespace PVGraph

abbrev Admitted := GraphJson.AdmittedGraph

/-- Accept the actual serialized PVGraph and return a Lean proof-bearing
    admission certificate, or an explicit rejection. -/
def admit? (source : Lean.Json) : Except String Admitted :=
  GraphJson.decodeCertified? source

/-- Independently interpret actual serialized PVGraph and its input
    bindings via the common UInt32 operator semantics. -/
def evaluate? (source inputs : Lean.Json) : Except String Lean.Json :=
  GraphEvaluate.evaluate? source inputs

/-- The certified document satisfies the common whole-program checker. -/
theorem admitted_sound (a : Admitted) :
    GraphAdmission.Document.admitted a.graph = true := a.admitted

#print axioms admitted_sound

end PVGraph
end L4Factoidal.GpuDomainSpecificLanguage
