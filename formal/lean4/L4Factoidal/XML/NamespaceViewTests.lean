import L4Factoidal.XML.NamespaceView

namespace L4Factoidal.XML

private def rejected (s : String) : Bool :=
  match parseNamespaceView s with | .error _ => true | _ => false

private def projected (s : String) : Option Node :=
  (parseNamespaceView s).toOption.map (·.forVocabulary "urn:target")

-- Default namespaces affect elements, not unprefixed attributes. Aliases for
-- XML attributes are resolved by namespace identity. Foreign attributes remain
-- qualified; they must not acquire the meaning of a bare vocabulary attribute.
#guard projected "<p:x xmlns:p='urn:target' xmlns:f='urn:foreign' a='1' f:a='2' xml:lang='en'/>" ==
  some (.element "x" [{name := "a", value := "1"},
    {name := "{urn:foreign}a", value := "2"}, {name := "xml:lang", value := "en"}] [])
#guard projected "<x xmlns='urn:target'><x xmlns='urn:foreign'/><x/><x xmlns=''/></x>" ==
  some (.element "x" [] [.element "{urn:foreign}x" [] [],
    .element "x" [] [], .element "{}x" [] []])
#guard rejected "<p:x/>"
#guard rejected "<x xmlns:xml='urn:wrong'/>"
#guard rejected "<x xmlns:p='urn:a' xmlns:q='urn:a' p:a='1' q:a='2'/>"
#guard rejected "<x xmlns:p='urn:a'><x xmlns:p=''/></x>"
#guard rejected "<p:1bad xmlns:p='urn:a'/>"
#guard rejected "<x xmlns:1bad='urn:a'/>"
#guard rejected "<?a:b data?><x/>"
#guard rejected "<x><?a:b data?></x>"
#guard rejected "<x/><?a:b data?>"
#guard rejected "<!DOCTYPE x [<!ENTITY a:b 'text'>]><x/>"
#guard (parseXML "<p:1bad xmlns:p='urn:a'/>").isOk
-- Namespaces 1.1 supports prefix undeclaration, without falling back to the
-- ancestor binding. Its sibling still inherits the original binding.
#guard projected "<?xml version='1.1'?><x xmlns='urn:target' xmlns:p='urn:a'><x xmlns:p=''/><p:y/></x>" ==
  some (.element "x" [] [.element "x" [] [], .element "{urn:a}y" [] []])
#guard rejected "<?xml version='1.1'?><x xmlns:p='urn:a'><p:y xmlns:p=''/></x>"

-- XML 1.0 §3.3.3: tokenized attributes collapse spaces after expansion.
#guard rejected "<!DOCTYPE x [<!ATTLIST x xmlns:a CDATA #IMPLIED xmlns:b NMTOKEN #IMPLIED>]><x xmlns:a='urn:a' xmlns:b=' urn:a ' a:k='1' b:k='2'/>"
#guard rejected "<!DOCTYPE x [<!NOTATION a:b SYSTEM 'n'>]><x/>"
#guard (parseXML "<!DOCTYPE x [<!NOTATION a:b SYSTEM 'n'>]><x/>").isOk
private def rootAttr (src name : String) : Option String :=
  (parseXML src).toOption.bind (fun d => findAttr name d.root.elementAttrs)
#guard rootAttr "<!DOCTYPE x [<!ATTLIST x a NMTOKENS #IMPLIED>]><x a=' a   b '/>" "a" == some "a b"
#guard rootAttr "<!DOCTYPE x [<!ATTLIST x a CDATA #IMPLIED>]><x a=' a   b '/>" "a" == some " a   b "
-- Character-reference tabs survive: only #x20 is collapsed at this stage.
#guard rootAttr "<!DOCTYPE x [<!ATTLIST x a NMTOKENS #IMPLIED>]><x a=' a&#9;b '/>" "a" == some "a\tb"
-- First declaration wins, including a first CDATA declaration.
#guard rootAttr "<!DOCTYPE x [<!ATTLIST x a CDATA #IMPLIED><!ATTLIST x a NMTOKEN #IMPLIED>]><x a=' a '/>" "a" == some " a "
end L4Factoidal.XML
