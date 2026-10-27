/-
L4Factoidal.RDF.FormatOfContent — the format of a document read from its
content, for a caller that did not name one.

No W3C document specifies this inference, and the N-Quads rule calls the
fast N-Quads reader (`L4Factoidal.Syntax.NQuadsFast`), an implementation
module. So this function is an implementation, not part of the foundation
(foundation/README.md, https://github.com/danbri/factoidal/issues/975). It
was in `L4Factoidal.RDF.Format` (a foundation module, level 2) until the
N-Quads rule (https://github.com/danbri/factoidal/issues/1058) added the
import; the foundation gate stopped on that import.
-/

import L4Factoidal.RDF.Format
import L4Factoidal.JSON.Parser
import L4Factoidal.Syntax.NQuadsFast

namespace L4Factoidal.RDF

/-- The complete lines of the first characters of a document (`head`): up to
    and with the last line break, or all of `head` when it is the whole text. -/
def completeLines (head : List Char) (whole : Bool) : List Char :=
  if whole then head
  else (head.reverse.dropWhile (fun c => c != '\n' && c != '\r')).reverse

/-- Do the complete lines of the head of a document read as RDF 1.2 N-Quads
    (`parseNQuadsFastDocument`) with at least one quad in a named graph? -/
def headIsNQuads (head : List Char) (whole : Bool) : Bool :=
  match L4Factoidal.Syntax.parseNQuadsFastDocument (String.ofList (completeLines head whole)) .rdf12 with
  | .ok ds => ds.named.any (fun ng => !ng.graph.isEmpty)
  | .error _ => false

/-- The format of a document read from its content, for a caller that did not
    name one (https://github.com/danbri/factoidal/issues/882). No W3C document
    specifies this inference; the rules guess only where the text decides, and a
    caller with other text names the format
    (https://github.com/danbri/factoidal/issues/1058):

    1. JSON-LD when the first character is `{` or `[` and the whole text is
       JSON (RFC 8259). Turtle `[] <p> [] .`, `[ <p> <o> ] .` and TriG
       `{ <s> <p> <o> }` and `[] { … }` are not JSON, so the rules go on.
    2. RDF/XML when the text starts with `<?xml` or `<rdf:RDF`.
    3. N-Quads (RDF 1.2) when the complete lines of the first 4096 characters
       are N-Quads statements and at least one of them names a graph. N-Triples
       is also N-Quads; with no graph name the text goes on to rule 5, which
       reads it the same.
    4. TriG when the text has a `{` (a TriG reader also reads Turtle and
       N-Triples).
    5. Otherwise Turtle.

    A caller reports the inferred format with the result. -/
def formatOfContent (text : String) : RdfFormat :=
  let all := text.toList
  let first := all.take 4096
  let whole := first.length == all.length
  let head := first.dropWhile Char.isWhitespace
  let headStr := String.ofList head
  let notJson : RdfFormat :=
    if headStr.startsWith "<?xml" || headStr.startsWith "<rdf:RDF" then .rdfxml
    else if headIsNQuads first whole then .nquads
    else if text.any (· == '{') then .trig
    else .turtle
  match head with
  | '{' :: _ | '[' :: _ =>
      if (L4Factoidal.JSON.parseJson text).toOption.isSome then .jsonld else notJson
  | _ => notJson

/-! ## Build-time checks -/

#guard formatOfContent "  {\"@id\": \"http://e/a\"}" == .jsonld
#guard formatOfContent "<?xml version=\"1.0\"?><rdf:RDF/>" == .rdfxml
#guard formatOfContent "<http://e/g> { <http://e/a> <http://e/p> 1 . }" == .trig
#guard formatOfContent "<http://e/a> <http://e/p> 1 ." == .turtle
-- https://github.com/danbri/factoidal/issues/1058: Turtle and TriG that begin
-- with `[` or `{` are not JSON; N-Quads with a graph name is N-Quads.
#guard formatOfContent "[{\"@id\": \"http://e/a\"}]" == .jsonld
#guard formatOfContent "[]" == .jsonld
#guard formatOfContent " {}\n" == .jsonld
#guard formatOfContent "[] <http://b> [] ." == .turtle
#guard formatOfContent "[ <http://p> <http://o> ] ." == .turtle
#guard formatOfContent "{ <http://a> <http://b> <http://c> }" == .trig
#guard formatOfContent "[] { <http://a> <http://b> <http://c> }" == .trig
#guard formatOfContent "<http://a> <http://b> <http://c> <http://g> ." == .nquads
#guard formatOfContent "<http://a> <http://b> <http://c> .\n<http://a> <http://b> \"{\" <http://g> .\n" == .nquads
#guard formatOfContent "VERSION \"1.2\"\n<http://a> <http://b> <http://c> <http://g> .\n" == .nquads
#guard formatOfContent "<http://a> <http://b> <http://c> .\n" == .turtle
#guard formatOfContent "(<http://a>) <http://b> <http://c> ." == .turtle
#guard formatOfContent "<http://g> { <http://a> <http://b> <http://c> }" == .trig

end L4Factoidal.RDF
