import L4Factoidal.Wikidata.Source

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL

def hintNamespace : String := "http://www.bigdata.com/queryHints#"
def wikibaseNamespace : String := "http://wikiba.se/ontology#"

-- Wikimedia's QueryHintRewriter, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/QueryHintRewriter.java
private def hintSubject (state : PState) (token : Token) : Bool :=
  ["Query", "Prior", "Group", "GroupAndSubGroups", "SubQuery"].any fun name =>
    tokenIri state token == some (hintNamespace ++ name)

private def hintEnd (depth : Nat) : List LocatedToken → Option (Nat × List LocatedToken)
  | [] => none
  | token :: rest =>
    match token.token with
    | .dot => if depth == 0 then some (token.stop, rest) else hintEnd depth rest
    | .rbrace => if depth == 0 then some (token.start, token :: rest) else none
    | .lbrace | .invalid _ => none
    | .lparen | .lbracket => hintEnd (depth + 1) rest
    | .rparen | .rbracket => if depth == 0 then none else hintEnd (depth - 1) rest
    | _ => hintEnd depth rest

private def hintEdits (state : PState) (chars : Array Char) :
    Nat → Token → List LocatedToken → List Edit → List Edit
  | fuel + 1, previous, token :: rest, acc =>
    let atSubject := previous == .lbrace || previous == .dot ||
      previous == .rbrace || previous == .rparen
    if atSubject && hintSubject state token.token then
      match hintEnd 0 rest with
      | some (stop, tail) =>
        let removed := (chars.extract token.start stop).map fun c =>
          if c == '\n' || c == '\r' then c else ' '
        hintEdits state chars fuel .dot tail (⟨token.start, stop, String.ofList removed.toList⟩ :: acc)
      | none => hintEdits state chars fuel token.token rest acc
    else hintEdits state chars fuel token.token rest acc
  | _, _, _, acc => acc.reverse

def rewriteHints (text : String) (state : PState) (tokens : List LocatedToken) : List Edit :=
  hintEdits state text.toList.toArray tokens.length .eof tokens []

-- Wikimedia's WikibaseIsSomeValueRewriter, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/WikibaseIsSomeValueRewriter.java
private def someValueArg : Token → Option String
  | .var name => some s!"CONTAINS(STR(?{name}),\"wikidata.org/.well-known/genid\")"
  | .iri _ | .pname _ | .str _ | .bnode _ | .integer _ | .decimal _ | .double _
  | .trueKw | .falseKw => some "false"
  | _ => none

private def callArgs : Nat → List LocatedToken → List String →
    Option (List String × Nat × List LocatedToken)
  | fuel + 1, arg :: sep :: rest, acc => do
    let value ← someValueArg arg.token
    if sep.token == .rparen then some ((value :: acc).reverse, sep.stop, rest)
    else if sep.token == .comma then callArgs fuel rest (value :: acc)
    else none
  | _, _, _ => none

private def someValueEdits (state : PState) :
    Nat → List LocatedToken → List Edit → Except Nat (List Edit)
  | fuel + 1, name :: openParen :: args, acc =>
    if tokenIri state name.token == some (wikibaseNamespace ++ "isSomeValue") &&
        openParen.token == .lparen then
      if (args.head?.map (·.token)) == some .rparen then .error name.start
      else match callArgs fuel args [] with
      | some (values, stop, rest) =>
        let replacement := match values with
          | [single] => single
          | _ => "(" ++ String.intercalate " || " values ++ ")"
        someValueEdits state fuel rest (⟨name.start, stop, replacement⟩ :: acc)
      | none => someValueEdits state fuel (openParen :: args) acc
    else someValueEdits state fuel (openParen :: args) acc
  | _, _, acc => .ok acc.reverse

def rewriteSomeValue (state : PState) (tokens : List LocatedToken) :
    Except Nat (List Edit) :=
  someValueEdits state tokens.length tokens []

end L4Factoidal.Wikidata
