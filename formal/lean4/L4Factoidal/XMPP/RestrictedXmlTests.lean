/-
L4Factoidal.XMPP.RestrictedXmlTests — `#guard`s for `Wire.parseElement` against
RFC 6120 section 11.1: no DTD, no comment, no processing instruction.

The nested entities below take a parser that expands them exponential time, so
if the DTD check goes, this file stops building rather than passing slowly.
-/
import L4Factoidal.XMPP.Wire

namespace L4Factoidal.XMPP.RestrictedXmlTests

open L4Factoidal.XMPP.Wire (parseElement)

private def refused (s : String) : Bool := (parseElement s).isNone
private def accepted (s : String) : Bool := (parseElement s).isSome

/-- Ten levels of ten references to an empty entity, then a use of the last. -/
private def nestedEntities : String :=
  let level (i : Nat) : String :=
    let ref := s!"&l{i - 1};"
    s!"<!ENTITY l{i} '{String.join (List.replicate 10 ref)}'>"
  let decls := String.join ((List.range 9).map (fun i => level (i + 1)))
  s!"<!DOCTYPE a [<!ENTITY l0 ''>{decls}]><a>&l9;</a>"

-- A DTD is refused wherever the prolog allows one.
#guard refused nestedEntities
#guard refused "<!DOCTYPE a><a/>"
#guard refused "  \n<!DOCTYPE a><a/>"
#guard refused "<?xml version='1.0'?><!DOCTYPE a><a/>"
#guard refused "<!-- x --><!DOCTYPE a><a/>"
#guard refused "<?pi x?><!-- y --> <!DOCTYPE a><a/>"
#guard refused s!"<!-- {String.join (List.replicate 1000 "padding ")} -->{nestedEntities}"

-- Comments and processing instructions inside a stanza are refused, at any depth.
#guard refused "<message><!-- x --></message>"
#guard refused "<message><body>x</body><!-- </message><message from='a@b'> --></message>"
#guard refused "<message><a><b><!-- x --></b></a></message>"
#guard refused "<message><?evil x?></message>"
#guard refused "<message><a><?evil x?></a></message>"

-- What XMPP uses still parses.
#guard accepted "<message/>"
#guard accepted "<message to='a@b' type='chat'><body>hello</body></message>"
#guard accepted "<?xml version='1.0'?><message/>"
#guard accepted "<iq type='set' id='1'><bind xmlns='urn:ietf:params:xml:ns:xmpp-bind'/></iq>"

-- Text that only mentions these things is text.
#guard accepted "<message><body>&lt;!DOCTYPE a&gt; and &lt;!-- this --&gt;</body></message>"
#guard accepted "<message><body><![CDATA[<!DOCTYPE a><!-- this -->]]></body></message>"
#guard accepted "<message id='&lt;!DOCTYPE'/>"

-- The scan stops at the root, and copes with an unterminated prolog.
#guard !(L4Factoidal.XMPP.Wire.prologHasDoctype 100 "<a/><!DOCTYPE b>".toList)
#guard !(L4Factoidal.XMPP.Wire.prologHasDoctype 100 "<!-- never closed".toList)
#guard !(L4Factoidal.XMPP.Wire.prologHasDoctype 100 "".toList)
#guard !(L4Factoidal.XMPP.Wire.prologHasDoctype 0 "<!DOCTYPE a>".toList)

-- Running out of fuel refuses.
#guard L4Factoidal.XMPP.Wire.holdsRestricted 0 []
#guard L4Factoidal.XMPP.Wire.holdsRestricted 1 [.text "a"]
#guard !(L4Factoidal.XMPP.Wire.holdsRestricted 2 [.text "a"])

-- Many siblings and nesting up to the depth limit both fit the fuel that `parseElement` gives.
#guard accepted s!"<a>{String.join (List.replicate 2000 "<b/>")}</a>"
#guard accepted s!"{String.join (List.replicate 60 "<a>")}{String.join (List.replicate 60 "</a>")}"
#guard refused s!"{String.join (List.replicate 60 "<a>")}<!-- x -->{String.join (List.replicate 60 "</a>")}"

end L4Factoidal.XMPP.RestrictedXmlTests
