import L4Factoidal.MathML.FromXml

namespace L4Factoidal.MathML

private def mns := "http://www.w3.org/1998/Math/MathML"
private def readsTwo (s : String) : Bool :=
  match parseMathML s with | some (.int 2) => true | _ => false

#guard readsTwo s!"<math xmlns='{mns}'><cn>2</cn></math>"
#guard readsTwo s!"<m:math xmlns:m='{mns}'><m:cn>2</m:cn></m:math>"
#guard (parseMathML "<m:math xmlns:m='urn:wrong'><m:cn>2</m:cn></m:math>").isNone
#guard (parseMathML "<m:math><m:cn>2</m:cn></m:math>").isNone
#guard (parseMathML s!"<math xmlns='{mns}'><cn xmlns='urn:wrong'>2</cn></math>").isNone
#guard (parseMathML "<math><cn>2</cn></math>").isNone
-- A qualified foreign `type` is not the unqualified MathML attribute.
#guard readsTwo s!"<math xmlns='{mns}' xmlns:f='urn:foreign'><cn f:type='rational'>2</cn></math>"

end L4Factoidal.MathML
