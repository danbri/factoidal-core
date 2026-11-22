import L4Factoidal.SPARQL.GsslFastPath

namespace L4Factoidal.SPARQL.GsslFastPathTests

open L4Factoidal.RDF L4Factoidal.SPARQL GsslFastPath

private def p : WfIri := ⟨"http://example.org/p", by decide⟩
private def q : WfIri := ⟨"http://example.org/q", by decide⟩
private def object : WfIri := ⟨"http://example.org/object", by decide⟩
private def alice : WfIri := ⟨"http://example.org/alice", by decide⟩
private def bob : WfIri := ⟨"http://example.org/bob", by decide⟩

private def accepted : Bgp :=
  [⟨.var "person", .iri p, .var "colleague"⟩,
   ⟨.var "colleague", .iri q, .iri object⟩]
private def unjoined : Bgp :=
  [⟨.var "person", .iri p, .var "colleague"⟩,
   ⟨.var "other", .iri q, .iri object⟩]
private def repeated : Bgp :=
  [⟨.var "x", .iri p, .var "x"⟩,
   ⟨.var "x", .iri q, .iri object⟩]
private def graph : Graph :=
  [{s := .iri alice, p := p, o := .iri bob},
   {s := .iri bob, p := q, o := .iri object}]

#guard supports accepted
#guard !supports unjoined
#guard !supports repeated
#guard !supports []
#guard (evalBgpIdx accepted graph).length == 1
#guard resolve accepted graph none == evalBgpIdx accepted graph
#guard resolve accepted graph (some []) == []
#guard resolve unjoined graph (some []) == evalBgpIdx unjoined graph

end L4Factoidal.SPARQL.GsslFastPathTests
