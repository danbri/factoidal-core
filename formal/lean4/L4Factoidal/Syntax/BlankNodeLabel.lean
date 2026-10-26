/-
L4Factoidal.Syntax.BlankNodeLabel — the check that a string is the body of an
RDF 1.1 N-Triples BLANK_NODE_LABEL.

  [141s] BLANK_NODE_LABEL ::= '_:' (PN_CHARS_U | [0-9]) ((PN_CHARS | '.')* PN_CHARS)?

`isBlankNodeLabel L` holds when `_:` followed by `L` is one BLANK_NODE_LABEL
token: a first character in PN_CHARS_U or 0-9 (`isBnodeStartChar`), then
characters in PN_CHARS or `.` (`isBnodeChar`), and not ending on `.`. Turtle,
TriG, N-Quads and SPARQL use the same production, so a label that passes can
be written in each of them. The SPARQL CONSTRUCT guards
(`SPARQL/ConstructLabelTests.lean`) check every output label with it
(https://github.com/danbri/factoidal/issues/742).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

/-- `_:` ++ `label` is an N-Triples BLANK_NODE_LABEL ([141s]). -/
def isBlankNodeLabel (label : String) : Bool :=
  match label.toList with
  | [] => false
  | c0 :: rest =>
      isBnodeStartChar c0 && rest.all isBnodeChar && rest.getLast? != some '.'

#guard isBlankNodeLabel "b1"
#guard isBlankNodeLabel "1a"
#guard isBlankNodeLabel "_x"
#guard isBlankNodeLabel "a-b.c"
#guard isBlankNodeLabel "tpl_0_b"
#guard isBlankNodeLabel "tpl_0g_bnode_13"
#guard isBlankNodeLabel "café·x"
-- Negative: the empty label, a bad first character, a final '.', and ':'
-- (W3C rdf11 N-Triples nt-syntax-bad-bnode-01 and -02, "Colon in bnode label
-- not allowed"), among them the label the CONSTRUCT generator made before
-- issue 742 was fixed.
#guard !isBlankNodeLabel ""
#guard !isBlankNodeLabel "-a"
#guard !isBlankNodeLabel ".a"
#guard !isBlankNodeLabel "a."
#guard !isBlankNodeLabel "a:b"
#guard !isBlankNodeLabel "tpl_0__:bnode_13"
#guard !isBlankNodeLabel "a b"
-- It agrees with the N-Triples lexer: a label it accepts is read back whole.
#guard (readBlankNodeLabel 0 ("_:a-b.c ".toList)).toOption.map (·.1) == some "a-b.c"
#guard (readBlankNodeLabel 0 ("_:tpl_0g_bnode_13 ".toList)).toOption.map (·.1) == some "tpl_0g_bnode_13"
-- and a label with ':' is not: the lexer stops at the colon.
#guard (readBlankNodeLabel 0 ("_:tpl_0__:bnode_13 ".toList)).toOption.map (·.1) == some "tpl_0__"

end L4Factoidal.Syntax
