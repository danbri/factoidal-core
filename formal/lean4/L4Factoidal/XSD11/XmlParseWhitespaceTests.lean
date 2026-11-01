import L4Factoidal.XSD11.Load

namespace L4Factoidal.XSD11.XmlParseWhitespaceTests
open L4Factoidal.XML L4Factoidal.XPath4

private def schema : Schema :=
  match parseXML "<xs:schema xmlns:xs='http://www.w3.org/2001/XMLSchema'><xs:element name='s' type='xs:string'/><xs:element name='token' type='xs:token'/><xs:element name='c'><xs:complexType><xs:simpleContent><xs:extension base='xs:string'><xs:attribute name='a'/></xs:extension></xs:simpleContent></xs:complexType></xs:element></xs:schema>" with
  | .ok d => buildSchema none xpathHooks [{ loc := "s.xsd", doc := d }] ["s.xsd"]
  | .error _ => default

private def parsed (src : String) (strip : Bool := true) : Except Err Doc := do
  let d ← match parseXML src with
    | .ok d => .ok d
    | .error _ => .error { code := "parse-error" }
  let o : ParseOpts := { baseUri := "", stripAll := strip, xsd := "lax" }
  parsedDocOfKids { schema := schemaHookOf schema } o (docKids o d) "urn:test"

private def result (src : String) : Doc := (parsed src).toOption.getD default

#guard schema.errors.isEmpty
private def publicText (f : LibFn) (src : String) : String :=
  let e : Env := { schema := schemaHookOf schema }
  match f { call := fun _ _ => .error { code := "unexpected-call" } } e [sStr src, [.map [(Atomic.ofStr "strip-space", sStr "all"),
      (Atomic.ofStr "xsd-validation", sStr "lax")]]] with
  | .ok [.node n] => e.nodeString n
  | .ok _ => "unexpected-result"
  | .error err => err.code
#guard publicText parseXmlFn "<s>    </s>" == "    "
#guard publicText parseFragmentFn "<c>    </c>" == "    "
-- Official parse-xml-436: xs:string whitespace survives strip-space:all.
#guard (result "<s>    </s>").stringValue 0 == "    "
#guard ((result "<s>    </s>").get 1).tval.map (fun as => as.map Atomic.str) == some ["    "]
-- Complex simple content gets the same exemption; whitespace facets still run.
#guard (result "<c a='v'>    </c>").stringValue 0 == "    "
#guard ((result "<token>  a   b  </token>").get 1).tval.map (fun as => as.map Atomic.str) == some ["a b"]
-- Unannotated lax content strips; simple descendants retain their own spaces.
#guard (result "<r>  <s>  </s>  <x/>  </r>").stringValue 0 == "  "
private def compact := result "<r>  <x a='v'/>  <y>z</y>  </r>"
#guard compact.nodes.size == 6
#guard (compact.get 1).children == #[2, 4]
#guard (compact.get 2).attrs == #[3]
#guard (compact.get 3).parent == some 2
#guard (compact.get 4).parent == some 1
#guard (compact.get 4).children == #[5]
#guard (compact.get 1).last == 5
#guard compact.stringValue 0 == "z"
#guard compact.uri == "urn:test"
-- xml:space inheritance is independent of the local simple-type exemption.
#guard (result "<r xml:space='preserve'>  <x xml:space='default'>  <y/>  </x>  </r>").stringValue 0 == "    "
#guard ((parsed "<r>  <x/>  </r>" false).toOption.getD default).stringValue 0 == "    "

private def metadata : Doc :=
  { compact with
    baseUri := "urn:base",
    idAttrs := [("r", "id")], idrefAttrs := [("r", "ref")],
    origin := some (42, #[10, 11, 12, 13, 14, 15], none) }
#guard (stripValidatedWs (schemaHookOf schema) metadata).baseUri == "urn:base"
#guard (stripValidatedWs (schemaHookOf schema) metadata).idAttrs == metadata.idAttrs
#guard (stripValidatedWs (schemaHookOf schema) metadata).idrefAttrs == metadata.idrefAttrs
#guard (stripValidatedWs (schemaHookOf schema) metadata).origin.map (fun (id, ns, _) => (id, ns)) == some (42, #[10, 11, 12, 13, 14, 15])

#print axioms parsedDocOfKids_no_strip
end L4Factoidal.XSD11.XmlParseWhitespaceTests
