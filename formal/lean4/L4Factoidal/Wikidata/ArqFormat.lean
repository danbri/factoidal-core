import L4Factoidal.Wikidata.Output
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL L4Factoidal.RDF

-- The parsed-query path mirrors the layout of Jena ARQ 4.10.0:
-- https://github.com/apache/jena/tree/jena-4.10.0/jena-arq/src/main/java/org/apache/jena/sparql/serializer
-- Wikimedia sorts the serializer's prefix declarations:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteEngine.java

private abbrev Prefixes := List (String × String)

private def renderIri (prefixes : Prefixes) (iri : WfIri) : String :=
  (prefixes.findSome? fun (name, namespaceIri) =>
    if namespaceIri.isPrefixOf iri.val then
      let localName := String.ofList (iri.val.toList.drop namespaceIri.length)
      let pname := name ++ ":" ++ localName
      match sourceTokens pname with
      | [token] => if token.token == .pname pname && token.stop == pname.length then some pname else none
      | _ => none
    else none).getD ("<" ++ iri.val ++ ">")

private def renderLiteral (value : WfLiteral) : Option String := do
  guard (value.val.datatype == "http://www.w3.org/2001/XMLSchema#string")
  return "\"" ++ L4Factoidal.Syntax.escapeLiteral value.val.lexicalForm ++ "\""

private def renderTerm (prefixes : Prefixes) : PatternTerm → Option String
  | .var name => some ("?" ++ name)
  | .iri iri => some (renderIri prefixes iri)
  | .literal value => renderLiteral value
  | _ => none

private def renderTriple (prefixes : Prefixes) (triple : TriplePattern) : Option (String × String × String) := do
  let subject ← match triple.s with
    | .var name => some ("?" ++ name)
    | .iri iri => some (renderIri prefixes iri)
    | _ => none
  let predicate ← match triple.p with
    | .iri iri =>
      if iri.val == "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" then some "a"
      else renderTerm prefixes triple.p
    | _ => renderTerm prefixes triple.p
  return (subject, predicate, ← renderTerm prefixes triple.o)

private def spaces (count : Nat) := String.ofList (List.replicate count ' ')

private def renderTriples (prefixes : Prefixes) (triples : Bgp) : Option (List String) := do
  let terms ← triples.mapM (renderTriple prefixes)
  let subjectWidth := terms.foldl (fun width (s, _, _) => max width (s.length + 2)) 0
  let predicateWidth := terms.foldl (fun width (_, p, _) => max width (p.length + 2)) 0
  let (_, lines) := (terms.zip (terms.drop 1 |>.map (some ∘ Prod.fst) |>.concat none)).foldl
    (fun (previous, lines) ((subject, predicate, object), next) =>
      let left := if previous == some subject then spaces subjectWidth
        else subject ++ spaces (subjectWidth - subject.length)
      let endMark := if next == some subject then " ;" else if next.isSome then " ." else ""
      (some subject, (left ++ predicate ++ spaces (predicateWidth - predicate.length) ++ object ++ endMark) :: lines))
    (none, [])
  return lines.reverse

private def infixText (op left right : String) : String :=
  "( " ++ left ++ " " ++ op ++ " " ++ right ++ " )"

private def renderExpr (prefixes : Prefixes) (fuel : Nat) (expr : Expr) : Option String := do
  let fuel + 1 := fuel | none
  let render := renderExpr prefixes fuel
  let unary := fun name arg => do return name ++ "(" ++ (← render arg) ++ ")"
  let binary := fun name left right => do return name ++ "(" ++ (← render left) ++ ", " ++ (← render right) ++ ")"
  match expr with
  | .var name => some ("?" ++ name)
  | .iri iri => some (renderIri prefixes iri)
  | .lit lit => renderLiteral lit
  | .boolLit value => some (toString value)
  | .numericLit value => some (toString value)
  | .compare op left right =>
    let symbol := match op with
      | .eq => "=" | .ne => "!=" | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
    return infixText symbol (← render left) (← render right)
  | .and left right => return infixText "&&" (← render left) (← render right)
  | .bound name => some ("bound(?" ++ name ++ ")")
  | .cond check yes no => return "if(" ++ (← render check) ++ ", " ++ (← render yes) ++ ", " ++ (← render no) ++ ")"
  | .isIri e => unary "isURI" e
  | .lang e => unary "lang" e
  | .str e => unary "str" e
  | .strStarts e pre => binary "strstarts" e pre
  | .strAfter e suffix => binary "strafter" e suffix
  | .aggregate kind distinct e =>
    let name ← match kind with
      | .sum => some "SUM" | .sample => some "SAMPLE" | .avg => some "AVG"
      | .min => some "MIN" | .max => some "MAX" | .count => some "COUNT"
      | _ => none
    let value ← match kind, e with
      | .count, .boolLit true => some "*"
      | _, _ => render e
    return name ++ "(" ++ (if distinct then "DISTINCT " else "") ++ value ++ ")"
  | _ => none

private def groupText (indent : Nat) (lines : List String) : String :=
  match lines with
  | [] => spaces indent ++ "{ }"
  | [head] => spaces indent ++ "{ " ++ head ++
      (if head.contains '\n' then "\n" ++ spaces indent ++ "}" else " }")
  | head :: tail => spaces indent ++ "{ " ++ head ++ "\n" ++
      String.intercalate "\n" (tail.map (fun line => spaces (indent + 2) ++ line)) ++ "\n" ++ spaces indent ++ "}"

private def renderPattern (prefixes : Prefixes) (fuel indent : Nat) (pattern : QueryPattern) : Option (List String) := do
  let fuel + 1 := fuel | none
  match pattern with
  | .empty => some []
  | .bgp triples => renderTriples prefixes triples
  | .service endpoint silent (.bgp triples) =>
    let header := "SERVICE " ++ (if silent then "SILENT " else "") ++ renderIri prefixes endpoint
    return [header ++ "\n" ++ groupText (indent + 2) (← renderTriples prefixes triples)]
  | .join left (right@(.service _ _ _)) =>
    return (← renderPattern prefixes fuel indent left) ++ (← renderPattern prefixes fuel indent right)
  | .leftJoin left (.bgp triples) cond =>
    let triples ← renderTriples prefixes triples
    let body ← match cond with
      | .boolLit true => pure triples
      | .compare .eq (.lang (.var _)) (.lit _) => do
        let filter ← renderExpr prefixes fuel cond
        pure (triples ++ ["FILTER " ++ filter])
      | _ => none
    return (← renderPattern prefixes fuel indent left) ++ ["OPTIONAL\n" ++ groupText (indent + 2) body]
  | .bind expr name inner =>
    let bind := "BIND(" ++ (← renderExpr prefixes fuel expr) ++ " AS ?" ++ name ++ ")"
    return (← renderPattern prefixes fuel indent inner) ++ [bind]
  | .filter expr inner =>
    let condition ← renderExpr prefixes fuel expr
    let test := if condition.startsWith "(" then condition else "( " ++ condition ++ " )"
    return (← renderPattern prefixes fuel indent inner) ++ ["FILTER " ++ test]
  | _ => none

private def formatPrefix (name iri : String) : String :=
  "PREFIX  " ++ name ++ ":" ++ spaces (max 1 (5 - name.length)) ++ "<" ++ iri ++ ">\n"

/-- Format the parsed-query cases for which the ARQ layout has been ported.
Scopes and constructs outside this serializer's coverage use the source
output path. A base IRI and ambiguous IRI abbreviations also defer to it. -/
def formatParsedRewrite (text : String) (query : Query) : Option String := do
  guard (text.utf8ByteSize <= 8192)
  let .mk form [] pattern group [] modifier none none := query | none
  let tokens := sourceTokens text
  let (state, _) ← (sourceState tokens []).toOption
  let defaults := defaultPrefixes.filter fun (name, _) => (lookupPrefix name state.prefixes).isNone
  let prefixes := state.prefixes ++ defaults
  let render := renderExpr prefixes 128
  let select ← match form with
    | .ask => some "ASK"
    | .select projection => do
      let items ← match projection with
        | .all => some "*"
        | .vars items => do
          let names ← items.mapM fun item => match item with
            | .var name => some ("?" ++ name)
            | .expr expr name => do return "(" ++ (← render expr) ++ " AS ?" ++ name ++ ")"
          pure (String.intercalate " " names)
      let qualification := if modifier.distinct then " DISTINCT" else if modifier.reduced then " REDUCED" else ""
      pure ("SELECT" ++ qualification ++ "  " ++ items)
    | _ => none
  let grouping ← match group with
    | none => some ""
    | some conditions => do
      let keys ← conditions.mapM fun condition => match condition with
        | .var name => some ("?" ++ name)
        | _ => none
      pure ("GROUP BY " ++ String.intercalate " " keys ++ "\n")
  let ordering ← match modifier.orderBy with
    | none => some ""
    | some conditions => do
      -- The AST represents both explicit ASC() and default order as asc.
      guard (!(tokens.any fun token => token.token == .asc))
      let keys ← conditions.mapM fun condition => match condition with
        | .asc (.var name) => some ("?" ++ name)
        | .desc expr => do return "DESC(" ++ (← render expr) ++ ")"
        | _ => none
      pure ("ORDER BY " ++ String.intercalate " " keys ++ "\n")
  let offset := modifier.offset.elim "" (fun n => s!"OFFSET  {n}\n")
  let limit := modifier.limit.elim "" (fun n => s!"LIMIT   {n}\n")
  let lines ← renderPattern prefixes 128 4 pattern
  let body := select ++ "\nWHERE\n" ++ groupText 2 lines ++ "\n" ++ grouping ++ ordering ++ offset ++ limit
  let used := (sourceTokens body).filterMap fun t => match t.token with
    | .pname name => some (splitPname name).1
    | _ => none
  let declarations := ((prefixes.filter fun (name, _) => used.contains name)
    |>.mergeSort (fun a b => a.1 ≤ b.1)).map fun (name, iri) => formatPrefix name iri
  let (leading, _) := splitLeadingComments text
  let prologue := if declarations.isEmpty then "" else String.join declarations ++ "\n"
  return leading ++ prologue ++ body

end L4Factoidal.Wikidata
