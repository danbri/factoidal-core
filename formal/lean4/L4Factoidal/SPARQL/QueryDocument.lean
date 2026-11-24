import L4Factoidal.SPARQL.QueryJson
import L4Factoidal.SPARQL.SourceComments
import L4Factoidal.SPARQL.QuerySourceAnchors
import L4Factoidal.Wikidata.NamedSubquery

namespace L4Factoidal.SPARQL
open L4Factoidal.JSON L4Factoidal.Syntax
open L4Factoidal.Wikidata

private def offset (position : Nat) : Json := .number (toString position)

def sourceCommentJson (comment : SourceComment) : Json :=
  .object [("text", .string comment.text), ("start", offset comment.start), ("end", offset comment.stop)]

private def span (start stop : Nat) : Json := .object [("start", offset start), ("end", offset stop)]

private def anchorJson (anchor : QuerySourceAnchor) : Json :=
  let encode := fun range : QuerySourceRange => span range.start range.stop
  let parts := [("subject", anchor.subject), ("predicate", anchor.predicate), ("object", anchor.object)]
  .object ([("kind", .string anchor.kind), ("span", encode anchor.range),
    ("origin", .string (if anchor.derived then "derived" else "exact"))] ++
    parts.filterMap fun (key, value) => value.map fun range => (key, encode range))

private def lexemeKind : Token → String
  | .pname _ => "prefixedName"
  | .iri _ => "iri"
  | .var _ => "variable"
  | .bnode _ => "blankNodeLabel"
  | .str _ => "string"
  | .invalid _ => "invalid"
  | .star => "star"
  | _ => "syntax"

private def lexemeJson (chars : Array Char) (state : PState) (bodyStart : Nat)
    (site : LocatedToken) : Json :=
  let text := String.ofList (chars.extract site.start site.stop).toList
  let resolution := if site.start < bodyStart then [] else
    (tokenIri state site.token).toList.map fun value => ("iri", Json.string value)
  .object ([("kind", .string (lexemeKind site.token)), ("text", .string text),
    ("span", span site.start site.stop)] ++ resolution)

private structure OpenBracket where
  start : Nat
  id : String
  anonymous : Bool

private def blankJson (id kind : String) (start stop : Nat) : Json :=
  .object [("id", .string id), ("kind", .string kind), ("span", span start stop)]

private def authoredBlankNodes : List LocatedToken → List OpenBracket → List Json → List Json
  | [], _, found => found.reverse
  | site :: rest, brackets, found =>
    match site.token, rest, brackets with
    | .lbracket, next :: _, _ =>
      let id := freshBnodeId [⟨next.token, next.start⟩]
      authoredBlankNodes rest (⟨site.start, id, next.token == .rbracket⟩ :: brackets) found
    | .rbracket, _, opening :: pending =>
      let kind := if opening.anonymous then "anonymous" else "propertyList"
      authoredBlankNodes rest pending (blankJson opening.id kind opening.start site.stop :: found)
    | .bnode id, _, _ =>
      authoredBlankNodes rest brackets (blankJson id "labelled" site.start site.stop :: found)
    | _, _, _ => authoredBlankNodes rest brackets found

private def prefixJson (declarations : List (String × String)) : Json :=
  let used := declarations.map Prod.fst |>.eraseDups
  .object (used.filterMap fun name =>
    (lookupPrefix name declarations).map fun iri => (name, .string iri))

def parseUnloweredQuery (text : String) (wdqs : Bool) (version : SparqlVersion)
    (base : Option String := none) : Except ParseError Query :=
  if wdqs then Wikidata.parseQuerySyntax text base version else
    match parseSparqlWith topFuel text base version with
    | .ok query => .ok query
    | .error error =>
      match parseSparqlWith (scaledFuel text) text base version with
      | .ok query => .ok query
      | .error _ => .error error

private def includeMarker (variables : List String) : Nat → Nat → String
  | 0, index => s!"__factoidal_include_{index}_"
  | fuel + 1, index =>
    let marker := s!"__factoidal_include_{index}_"
    if variables.any (marker.isPrefixOf ·) then includeMarker variables fuel (index + 1) else marker

private def decodeIncludes (marker : String) : Nat → Json → Json
  | 0, json => json
  | fuel + 1, json@(.object fields) =>
    match json.getString? "kind", json.field? "variables" with
    | some "values", some (.array (.string name :: variables)) =>
      if marker.isPrefixOf name then
        .object [("kind", .string "include"), ("name", .string ((name.drop marker.length).toString)),
          ("variables", .array variables)]
      else json
    | _, _ => .object (fields.map fun (key, value) => (key, decodeIncludes marker fuel value))
  | fuel + 1, .array values => .array (values.map (decodeIncludes marker fuel))
  | _, json => json

private def namedQuery (text prologue : String) (tokens : List LocatedToken)
    (plan : NamedSubquery.Plan) (version : SparqlVersion) (base : Option String) :
    Except (String × ParseError) (Json × List Json) := do
  let variables := tokens.filterMap fun token => match token.token with | .var v => some v | _ => none
  let marker := includeMarker variables (variables.length + 1) 0
  let encode := fun query =>
    let json := queryAstJson query
    decodeIncludes marker (2 * text.length + 64) json
  let mut prepared : List NamedSubquery.PreparedBlock := []
  let mut blocks := []
  for block in plan.blocks do
    let fragment := NamedSubquery.substitute block.body block.references prepared (markerPrefix := marker)
    let .ok query := parseUnloweredQuery (prologue ++ "\n" ++ fragment) true version base |
      throw ("named_subquery_parse_error", ⟨s!"Could not parse named subquery %{block.name}", block.start⟩)
    let variables := query.projectedVars.filter fun v => !marker.isPrefixOf v
    prepared := ⟨block.name, variables, "", "", []⟩ :: prepared
    blocks := .object [("name", .string block.name), ("ast", encode query),
      ("span", span block.start block.stop)] :: blocks
  let removes := plan.blocks.map fun block => (⟨block.start, block.stop, ""⟩ : Wikidata.Edit)
  let outer := NamedSubquery.substitute text plan.references prepared removes marker
  let query ← (parseUnloweredQuery outer true version base).mapError fun error =>
    ("named_subquery_outer_parse_error", ⟨error.msg, 0⟩)
  return (encode query, blocks.reverse)

private def directiveJson (comment : SourceComment) : Option Json := do
  let body := ((comment.text.drop 1).toString).trimAscii.toString
  let kind ← ["title", "defaultView", "view"].find? (fun name => (name ++ ":").isPrefixOf body)
  let value := ((body.drop (kind.length + 1)).toString).trimAscii.toString
  return .object [("kind", .string kind), ("value", .string value), ("span", span comment.start comment.stop)]

private def utf16Offset (chars : Array Char) (position : Nat) : Nat :=
  (chars.extract 0 position).foldl (fun units c => units + if c.toNat > 0xFFFF then 2 else 1) 0

private def diagnosticJson (chars : Array Char) (tokens : List LocatedToken) (code : String)
    (error : ParseError) : Json :=
  let start := min error.pos chars.size
  let stop := ((tokens.find? fun token => token.start ≤ start && start < token.stop).map (·.stop)).getD start
  .object [("code", .string code), ("message", .string error.msg), ("offset", offset start),
    ("span", span start stop), ("utf16Span", span (utf16Offset chars start) (utf16Offset chars stop))]

/-- Inspect both the resolved AST and the authored text. Positions refer to
Unicode code points in the input, including comments and whitespace. Parse
errors are data and still carry the original text and its source comments. -/
def parseQueryDocument (text : String) (wdqs := false) (version : SparqlVersion := .v11)
    (base : Option String := none) : Json := Id.run do
  let tokens := sourceTokens text wdqs version.is12
  let chars := text.toList.toArray
  let defaults := if wdqs then Wikidata.defaultPrefixes else []
  let initial : PState := { base := base, prefixes := defaults, v12 := version.is12 }
  let stream := tokens.map fun token => (⟨token.token, token.start⟩ : PosToken)
  let (prologue, body) := ((pPrologue (tokens.length + 1) initial stream).toOption).getD (initial, stream)
  let qlever := (tokens.zip (tokens.drop 1)).any fun (word, token) =>
    word.token == .withKw && (match token.token with
      | .invalid value => value.startsWith "%"
      | _ => false)
  let result : Except (String × ParseError) (Json × List Json) := do
    match parseUnloweredQuery text wdqs version base with
    | .ok query => pure (queryAstJson query, [])
    | .error error =>
      if !wdqs || !text.contains '%' then throw ("sparql_parse_error", error) else
      match NamedSubquery.plan text tokens (qlever := qlever) (inspect := true) with
      | .ok (some plan) =>
        let prologueText := String.ofList (chars.extract 0 (peekPos body)).toList
        namedQuery text prologueText tokens plan version base
      | .ok none => throw ("sparql_parse_error", error)
      | .error problem => throw (problem.code, ⟨problem.message, error.pos⟩)
  let (ast, named, diagnostics) := match result with
    | .ok (query, named) => (query, named, [])
    | .error (code, error) => (.null, [], [diagnosticJson chars tokens code error])
  let comments := sourceComments text version.is12
  return .object [("schema_version", .number "1"), ("parser_version", .string "factoidal-sparql-1"),
    ("ast", ast), ("namedSubqueries", .array named), ("diagnostics", .array diagnostics),
    ("prefixes", prefixJson prologue.prefixes),
    ("source", .object [("text", .string text), ("offsetEncoding", .string "unicode-code-points"),
      ("span", span 0 chars.size), ("tokens", .array (tokens.map (lexemeJson chars prologue (peekPos body)))),
      ("blankNodes", .array (authoredBlankNodes tokens [] [])),
      ("anchors", .array ((querySourceAnchors prologue tokens body).map anchorJson)),
      ("comments", .array (comments.map sourceCommentJson)),
      ("directives", .array (comments.filterMap directiveJson))])]

end L4Factoidal.SPARQL
