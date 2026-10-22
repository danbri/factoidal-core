import L4Factoidal.SPARQL.ResultsXml

namespace L4Factoidal.SPARQL

private def ns := "http://www.w3.org/2005/sparql-results#"
private def rejects (s : String) : Bool := match parseSrx s with | .error _ => true | .ok _ => false

private def acceptsTrue (s : String) : Bool :=
  match parseSrx s with | .ok (.boolean true) => true | _ => false

#guard acceptsTrue s!"<sparql xmlns='{ns}'><head/><boolean>true</boolean></sparql>"
#guard acceptsTrue s!"<r:sparql xmlns:r='{ns}'><r:head/><r:boolean>true</r:boolean></r:sparql>"
#guard rejects "<r:sparql xmlns:r='urn:wrong'><r:boolean>true</r:boolean></r:sparql>"
#guard rejects "<sparql><boolean>true</boolean></sparql>"
#guard rejects "<r:sparql><r:boolean>true</r:boolean></r:sparql>"
#guard rejects s!"<sparql xmlns='{ns}'><boolean xmlns='urn:wrong'>true</boolean></sparql>"
#guard rejects s!"<r:sparql xmlns:r='{ns}'><r:boolean xmlns:r='urn:wrong'>true</r:boolean></r:sparql>"
#guard rejects s!"<sparql xmlns='{ns}'><boolean xmlns=''>true</boolean></sparql>"
#guard acceptsTrue s!"<r:sparql xmlns:r='{ns}'><s:boolean xmlns:s='{ns}'>true</s:boolean></r:sparql>"

end L4Factoidal.SPARQL
