import L4Factoidal.Wikidata.Source

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL

-- Text-only format and original-query comments in the pinned Wikimedia engine:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteEngine.java
private def linesWithEndings (text : String) : List (String × String) :=
  splitLines text.toList [] []
where
  line (chars : List Char) := String.ofList chars.reverse
  splitLines : List Char → List Char → List (String × String) → List (String × String)
    | '\r' :: '\n' :: rest, chars, acc => splitLines rest [] ((line chars, "\r\n") :: acc)
    | '\r' :: rest, chars, acc => splitLines rest [] ((line chars, "\r") :: acc)
    | '\n' :: rest, chars, acc => splitLines rest [] ((line chars, "\n") :: acc)
    | c :: rest, chars, acc => splitLines rest (c :: chars) acc
    | [], [], acc => acc.reverse
    | [], chars, acc => ((line chars, "") :: acc).reverse

/-- Preserve the leading blank lines and WDQS directives ahead of any
namespace declarations that the rewrite needs to add. -/
def splitLeadingComments (text : String) : String × String :=
  let lines := linesWithEndings text
  let leading := lines.takeWhile fun (line, ending) =>
    (ending == "\n" || ending == "\r\n") &&
      let body := line.toList.dropWhile (fun c => c == ' ' || c == '\t')
      body.isEmpty || body.head? == some '#'
  let joinLines := fun lines : List (String × String) => String.join (lines.map fun (line, ending) => line ++ ending)
  (joinLines leading, joinLines (lines.drop leading.length))

def appendOriginalQuery (output original : String) : String :=
  let comment := String.join ((linesWithEndings original).map fun (line, _) =>
    if line.isEmpty then "#\n" else "# " ++ line ++ "\n")
  output ++ "\n# Original query:\n" ++ comment

private def forbiddenPrefix (name iri : String) : Bool :=
  ["bd", "gas", "hint", "mwapi"].contains name ||
    ["http://www.bigdata.com/rdf#", "http://www.bigdata.com/rdf/gas#",
      "http://www.bigdata.com/queryHints#", "https://www.mediawiki.org/ontology#API/"].contains iri

-- WDQS defaults are emitted in upstream declaration order on the text-only path:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/WdqsPrefixes.java
/-- Finalise source-edited output. Only remove full prefix declaration lines
and blanked statements. A whitespace-only line inside a multiline literal
remains query content. -/
def formatTextRewrite (text : String) : String := Id.run do
  let (leading, body) := splitLeadingComments text
  let standaloneBody := standalone body
  let tokens := sourceTokens standaloneBody
  let .ok (state, queryTokens) := sourceState tokens [] | return text
  let used := queryTokens.filterMap fun t => match t.tok with
    | .pname name => some (splitPname name).1
    | _ => none
  let decls := tokens.takeWhile fun t => queryTokens.isEmpty || t.start < peekPos queryTokens
  let blanks := tokens.filter fun t => match t.token with
    | .str _ => true
    | _ => false
  let blankable := fun (line : String) => !line.isEmpty && line.toList.all (fun c => c == ' ' || c == '\t')
  let (_, _, _, kept) := (linesWithEndings standaloneBody).foldl (fun (offset, decls, blanks, kept) (line, ending) =>
    let stop := offset + line.length
    let decls := decls.dropWhile (fun t => t.start < offset)
    let blanks := blanks.dropWhile (fun t => t.stop <= offset)
    let dropPrefix := match decls with
      | keyword :: declaration :: iri :: _ =>
        keyword.start == offset && keyword.token == .prefixKw && iri.stop == stop &&
          (match declaration.token with
           | .pname name =>
             let name := (splitPname name).1
             !used.contains name || (lookupPrefix name state.prefixes).any (forbiddenPrefix name)
           | _ => false)
      | _ => false
    let dropBlank := !ending.isEmpty && blankable line &&
      !(blanks.head?.any fun t => t.start < offset && stop < t.stop)
    (stop + ending.length, decls, blanks,
      if dropPrefix || dropBlank then kept else (line ++ ending) :: kept))
    (0, decls, blanks, [])
  let output := leading ++ String.join kept.reverse
  return if output.endsWith "\n" then output else output ++ "\n"

end L4Factoidal.Wikidata
