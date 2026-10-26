/- Build-time checks for chunk-stable Turtle dotted-candidate scanning. -/
import L4Factoidal.Syntax.TurtleStatementScan

namespace L4Factoidal.Syntax

def scanChunks (chunks : List String) : StatementScan :=
  chunks.foldl StatementScan.feed StatementScan.init

def candidates (chunks : List String) : List String :=
  (scanChunks chunks).completed

/- IRIREF and comment dots are not candidates; the final statement dot is. -/
#guard candidates ["<http://example.org/a.b> <http://example.org/p> <http://example.org/o> .\n# c.d\n"] ==
  ["<http://example.org/a.b> <http://example.org/p> <http://example.org/o> ."]

/- The dot / whitespace boundary can cross byte-decoded string chunks. -/
#guard candidates ["<s> <p> <o> .", "\n<s2> <p> <o> .\n"] ==
  ["<s> <p> <o> .", "\n<s2> <p> <o> ."]

/- Short and long strings may contain dots and line breaks. -/
#guard candidates ["<s> <p> \"a. b\" .\n", "<s2> <p> \"\"\"a.\nb\"\"\" .\n"] ==
  ["<s> <p> \"a. b\" .", "\n<s2> <p> \"\"\"a.\nb\"\"\" ."]

/- A decimal's internal dot is left to the grammar; only its later terminal
dot becomes a candidate. -/
#guard candidates ["<s> <p> 1.0 .\n"] == ["<s> <p> 1.0 ."]

/- Standard no-dot SPARQL-style directives are candidates only at a
normal-mode line boundary, not because every newline is split. -/
#guard candidates ["PREFIX ex: <http://example.org/>\n", "ex:s ex:p ex:o .\n"] ==
  ["PREFIX ex: <http://example.org/>", "\nex:s ex:p ex:o ."]

/- https://github.com/danbri/factoidal/issues/1028: a prefixed name whose
prefix is a keyword (`prefix:Atto`, `base:x`, `version:v`) starts a triple,
not a directive, so its line end is not a boundary. -/
#guard candidates ["prefix:Atto\n  a qudt:Prefix ;\n  rdfs:label \"atto\" .\n"] ==
  ["prefix:Atto\n  a qudt:Prefix ;\n  rdfs:label \"atto\" ."]
#guard candidates ["BASE:x\n <p> <o> .\n"] == ["BASE:x\n <p> <o> ."]
#guard candidates ["version:v\n <p> <o> .\n"] == ["version:v\n <p> <o> ."]
#guard candidates ["prefixes:x\n <p> <o> .\n"] == ["prefixes:x\n <p> <o> ."]
-- the keywords as directives still give a boundary
#guard candidates ["BASE <http://example.org/>\n<s> <p> <o> .\n"] ==
  ["BASE <http://example.org/>", "\n<s> <p> <o> ."]
#guard candidates ["base<http://example.org/>\n<s> <p> <o> .\n"] ==
  ["base<http://example.org/>", "\n<s> <p> <o> ."]
#guard candidates ["VERSION \"1.2\"\n<s> <p> <o> .\n"] ==
  ["VERSION \"1.2\"", "\n<s> <p> <o> ."]
-- a keyword alone on its line is not yet a complete directive
#guard candidates ["PREFIX\n ex: <http://example.org/>\nex:s ex:p ex:o .\n"] ==
  ["PREFIX\n ex: <http://example.org/>", "\nex:s ex:p ex:o ."]

end L4Factoidal.Syntax
