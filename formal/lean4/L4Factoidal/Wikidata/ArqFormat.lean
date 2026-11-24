import L4Factoidal.Wikidata.Output
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL L4Factoidal.RDF

-- The parsed-query path mirrors the layout of Jena ARQ 4.10.0:
-- https://github.com/apache/jena/tree/jena-4.10.0/jena-arq/src/main/java/org/apache/jena/sparql/serializer
-- Wikimedia sorts the serializer's prefix declarations:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteEngine.java

private structure FormatContext where
  prefixes : List (String × String)
  blanks : Std.HashMap String String
  syntheticCountSelects : List Nat

private def renderIri (prefixes : FormatContext) (iri : WfIri) : String :=
  (prefixes.prefixes.findSome? fun (name, namespaceIri) =>
    if namespaceIri.isPrefixOf iri.val then
      let localName := String.ofList (iri.val.toList.drop namespaceIri.length)
      let pname := name ++ ":" ++ localName
      match sourceTokens pname with
      | [token] => if token.token == .pname pname && token.stop == pname.length then some pname else none
      | _ => none
    else none).getD ("<" ++ iri.val ++ ">")

private def xsd := "http://www.w3.org/2001/XMLSchema#"

private def renderLiteral (prefixes : FormatContext) (value : WfLiteral) : Option String := do
  let literal := value.val
  guard literal.direction.isNone
  let lexical := literal.lexicalForm
  let quoted := "\"" ++ L4Factoidal.Syntax.escapeLiteral lexical ++ "\""
  if let some language := literal.langTag then return quoted ++ "@" ++ language
  if literal.datatype == xsd ++ "string" then return quoted
  if literal.datatype == xsd ++ "boolean" && (lexical == "true" || lexical == "false") then
    return lexical
  let token := (sourceTokens lexical).head?.map (·.token)
  if (match token with
      | some (.integer s) => literal.datatype == xsd ++ "integer" && s == lexical
      | some (.decimal s) => literal.datatype == xsd ++ "decimal" && s == lexical
      | some (.double s) => literal.datatype == xsd ++ "double" && s == lexical
      | _ => false) then return lexical
  return quoted ++ "^^" ++ renderIri prefixes literal.datatype

private def renderTerm (prefixes : FormatContext) : PatternTerm → Option String
  | .var name => some ("?" ++ name)
  | .iri iri => some (renderIri prefixes iri)
  | .literal value => renderLiteral prefixes value
  | .bnode name => prefixes.blanks[name]?
  | _ => none

private def renderSubject (prefixes : FormatContext) : PatternSubject → Option String
    | .var name => some ("?" ++ name)
    | .iri iri => some (renderIri prefixes iri)
    | .bnode name => prefixes.blanks[name]?
    | _ => none

private def renderPredicate (context : FormatContext) (iri : WfIri) : String :=
  let rendered := renderIri context iri
  if rendered == "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>" then "a" else rendered

private def renderTriple (prefixes : FormatContext) (triple : TriplePattern) : Option (String × String × String) := do
  let subject ← renderSubject prefixes triple.s
  let predicate ← match triple.p with
    | .iri iri => some (renderPredicate prefixes iri)
    | _ => renderTerm prefixes triple.p
  return (subject, predicate, ← renderTerm prefixes triple.o)

private def spaces (count : Nat) := String.ofList (List.replicate count ' ')

private def renderTriples (prefixes : FormatContext) (triples : Bgp) : Option (List String) := do
  let terms ← triples.mapM (renderTriple prefixes)
  let subjectWidth := min 8 (terms.foldl (fun width (s, _, _) => max width s.length) 0) + 2
  let predicateWidth := min 20 (terms.foldl (fun width (_, p, _) => max width p.length) 0) + 2
  let (_, lines) := (terms.zip (terms.drop 1 |>.map (some ∘ Prod.fst) |>.concat none)).foldl
    (fun (previous, lines) ((subject, predicate, object), next) =>
      let left := if previous == some subject then spaces subjectWidth
        else if subject.length > 12 then subject ++ "\n" ++ spaces subjectWidth
        else subject ++ spaces (max 2 (subjectWidth - subject.length))
      let endMark := if next == some subject then " ;" else if next.isSome then " ." else ""
      let overhang := if previous != some subject && subject.length <= 12 then
        subject.length + 2 - subjectWidth else 0
      (some subject, (left ++ predicate ++ spaces (max 2 (predicateWidth - predicate.length - overhang)) ++
        object ++ endMark) :: lines))
    (none, [])
  return lines.reverse.flatMap (·.splitOn "\n")

private def infixText (op left right : String) : String :=
  "( " ++ left ++ " " ++ op ++ " " ++ right ++ " )"

private def renderExpr (prefixes : FormatContext) (fuel : Nat) (expr : Expr) : Option String := do
  let fuel + 1 := fuel | none
  let render := renderExpr prefixes fuel
  let unary := fun name arg => do return name ++ "(" ++ (← render arg) ++ ")"
  let binary := fun name left right => do return name ++ "(" ++ (← render left) ++ ", " ++ (← render right) ++ ")"
  let call := fun name args => do return name ++ "(" ++ String.intercalate ", " (← args.mapM render) ++ ")"
  match expr with
  | .var name => some ("?" ++ name)
  | .iri iri => some (renderIri prefixes iri)
  | .lit lit => renderLiteral prefixes lit
  | .boolLit value => some (toString value)
  | .numericLit value => some (toString value)
  | .decimalLit value | .doubleLit value => some value
  | .arith op left right =>
    let symbol := match op with | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
    return infixText symbol (← render left) (← render right)
  | .unaryMinus e => return "( - " ++ (← render e) ++ " )"
  | .unaryPlus e => return "( + " ++ (← render e) ++ " )"
  | .compare op left right =>
    let symbol := match op with
      | .eq => "=" | .ne => "!=" | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
    return infixText symbol (← render left) (← render right)
  | .and left right => return infixText "&&" (← render left) (← render right)
  | .or left right => return infixText "||" (← render left) (← render right)
  | .not e => return "( ! " ++ (← render e) ++ " )"
  | .bound name => some ("bound(?" ++ name ++ ")")
  | .cond check yes no => return "if(" ++ (← render check) ++ ", " ++ (← render yes) ++ ", " ++ (← render no) ++ ")"
  | .isIri e => unary "isURI" e
  | .isBlank e => unary "isBlank" e
  | .isLiteral e => unary "isLiteral" e
  | .isNumeric e => unary "isNumeric" e
  | .lang e => unary "lang" e
  | .datatype e => unary "datatype" e
  | .iriFn e => unary "URI" e
  | .str e => unary "str" e
  | .strLen e => unary "strlen" e
  | .uCase e => unary "ucase" e
  | .lCase e => unary "lcase" e
  | .encodeForUri e => unary "encode_for_uri" e
  | .substr e start len => call "substr" ([e, start] ++ len.toList)
  | .contains e sub => binary "contains" e sub
  | .strStarts e pre => binary "strstarts" e pre
  | .strAfter e suffix => binary "strafter" e suffix
  | .strEnds e suffix => binary "strends" e suffix
  | .strBefore e prefixText => binary "strbefore" e prefixText
  | .strDt e dt => binary "strdt" e dt
  | .strLang e tag => binary "strlang" e tag
  | .sameTerm e other => binary "sameTerm" e other
  | .concat es => call "concat" es
  | .coalesce es => call "coalesce" es
  | .replace e pat rep flags => call "replace" ([e, pat, rep] ++ flags.toList)
  | .regex e pat flags => call "regex" ([e, pat] ++ flags.toList)
  | .inList e es => return infixText "IN" (← render e) (← call "" es)
  | .notInList e es => return infixText "NOT IN" (← render e) (← call "" es)
  | .abs e => unary "abs" e
  | .round e => unary "round" e
  | .ceil e => unary "ceil" e
  | .floor e => unary "floor" e
  | .md5 e => unary "MD5" e
  | .sha1 e => unary "SHA1" e
  | .sha256 e => unary "SHA256" e
  | .sha384 e => unary "SHA384" e
  | .sha512 e => unary "SHA512" e
  | .now => some "now()"
  | .year e => unary "year" e
  | .month e => unary "month" e
  | .day e => unary "day" e
  | .hours e => unary "hours" e
  | .minutes e => unary "minutes" e
  | .seconds e => unary "seconds" e
  | .timezone e => unary "timezone" e
  | .tz e => unary "tz" e
  | .functionCall i args =>
    let name := if i.val == "http://www.w3.org/2005/xpath-functions#rand" && args.isEmpty
      then "rand" else renderIri prefixes i
    call name args
  | .aggregate (.groupConcat separator) distinct e =>
    let marker ← separator.elim (some "") fun s => do
      guard (!s.contains '\'' && !s.contains '\\' && !s.contains '\n' && !s.contains '\r')
      return " ; separator='" ++ s ++ "'"
    return "GROUP_CONCAT(" ++ (if distinct then "DISTINCT " else "") ++ (← render e) ++ marker ++ ")"
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

private def renderPath (prefixes : FormatContext) (fuel : Nat) (nested : Bool)
    (path : PropertyPath) : Option String := do
  let fuel + 1 := fuel | none
  let child := renderPath prefixes fuel true
  let binary := fun p sep q => do
    let text := (← child p) ++ sep ++ (← child q)
    return if nested then "(" ++ text ++ ")" else text
  let modifier := fun p suffix => do return "(" ++ (← renderPath prefixes fuel false p) ++ ")" ++ suffix
  match path with
  | .iri iri => some (renderPredicate prefixes iri)
  | .sequence left right => binary left "/" right
  | .alternative left right => binary left "|" right
  | .zeroOrMore p => modifier p "*"
  | .oneOrMore p => modifier p "+"
  | .zeroOrOne p => modifier p "?"
  | .inverse p => return "^" ++ (← child p)
  | .negatedSet paths => do
    let members ← paths.mapM child
    match members with
    | [] => none
    | [one] => some ("!" ++ one)
    | _ => some ("!(" ++ String.intercalate "|" members ++ ")")

private inductive TripleSpan where
  | basic (triples : Bgp)
  | path (subject : PatternSubject) (path : PropertyPath) (object : PatternTerm)

private def tripleSpans (fuel : Nat) (pattern : QueryPattern) (tail : List TripleSpan) :
    Option (List TripleSpan) := do
  let fuel + 1 := fuel | none
  match pattern with
  | .bgp triples => match tail with
    | .basic next :: rest => return .basic (triples ++ next) :: rest
    | _ => return .basic triples :: tail
  | .propertyPath subject path object =>
    return .path subject path object :: tail
  | .join left right =>
    tripleSpans fuel left (← tripleSpans fuel right tail)
  | .empty => pure tail
  | _ => none

/-- Render consecutive simple triples as one width-aligned run. A property
path separates runs even though it is part of the same source triple block. -/
private def renderTriplesBlock (context : FormatContext) (fuel : Nat)
    (pattern : QueryPattern) : Option (List String) := do
  let spans ← tripleSpans fuel pattern []
  let groups ← spans.mapM fun span => match span with
    | .basic triples => renderTriples context triples
    | .path s p o => do
      return [(← renderSubject context s) ++ " " ++ (← renderPath context fuel false p) ++
        " " ++ (← renderTerm context o)]
  return addDots groups
where
  addDots : List (List String) → List String
    | [] => []
    | [last] => last
    | block :: tail =>
      let dotted := match block.reverse with
        | [] => []
        | last :: rest => ((last ++ " .") :: rest).reverse
      dotted ++ addDots tail

private def renderData (prefixes : FormatContext) (indent : Nat) (pattern : QueryPattern) : Option String := do
  let .values names values := pattern | none
  let cell := fun value => match value with
    | none => some "UNDEF"
    | some (.iri iri) => some (renderIri prefixes iri)
    | some (.literal literal) => renderLiteral prefixes literal
    | _ => none
  let rows ← values.mapM fun row => do
    return String.join ((← row.mapM cell).map (" " ++ ·))
  let names := names.map ("?" ++ ·)
  match names with
  | [name] => return "VALUES " ++ name ++ " {" ++ String.join rows ++ " }"
  | _ => return "VALUES ( " ++ String.intercalate " " names ++ " ) {\n" ++
      String.join (rows.map fun row => spaces (indent + 2) ++ "(" ++ row ++ " )\n") ++ spaces indent ++ "}"

private def renderFilter (prefixes : FormatContext) (fuel : Nat) (expr : Expr) : Option String := do
  let content ← renderExpr prefixes fuel expr
  let plain := match expr with
    | .var _ | .lit _ | .iri _ | .boolLit _ | .numericLit _ | .decimalLit _ | .doubleLit _ => true
    | _ => false
  return "FILTER " ++ (if plain then "( " ++ content ++ " )" else content)

private def skipDot (ts : TStream) : TStream :=
  if peekTok ts == .dot then advTok ts else ts

private def withoutIndent (indent : Nat) (text : String) : String :=
  String.ofList (text.toList.drop indent)

private def selectText (prefixes : FormatContext) (fuel : Nat) (qualification : String)
    (selection : SelectClause) (syntheticCount : Bool) : Option String := do
  let items ← match selection with
    | .all => some "*"
    | .vars items => do
      let names ← items.mapM fun item => match item with
        | .var name => some ("?" ++ name)
        | .expr (.aggregate .count false (.boolLit true)) name =>
          some ((if syntheticCount then "(count(*)" else "(COUNT(*)") ++ " AS ?" ++ name ++ ")")
        | .expr expr name => do return "(" ++ (← renderExpr prefixes fuel expr) ++ " AS ?" ++ name ++ ")"
      pure (String.intercalate " " names)
  return "SELECT" ++ qualification ++ "  " ++ items

private def orderDirections (state : PState) (fuel : Nat) (tokens : TStream) : List Bool :=
  match fuel with
  | 0 => []
  | f + 1 =>
    match pOrderCondition f state tokens with
    | .error _ => []
    | .ok (_, rest) => (peekTok tokens == .asc) :: orderDirections state f rest

private def renderModifiers (prefixes : FormatContext) (state : PState) (fuel indent : Nat)
    (ts : TStream) : Option (List String × TStream) := do
  let ((modifier, group, having), afterModifiers) ← (pSolutionModifier fuel state ts).toOption
  let render := renderExpr prefixes fuel
  let groups ← (group.getD []).mapM fun condition => match condition with
    | .var name => some ("?" ++ name)
    | .expr expr name => do
      let body ← render expr
      return name.elim body (fun target => "(" ++ body ++ " AS ?" ++ target ++ ")")
  let having ← having.mapM render
  let ordering ← match modifier.orderBy with
    | none => some []
    | some conditions => do
      let order := ts.dropWhile (fun token => token.tok != .order)
      let flags := orderDirections state fuel (advTok (advTok order))
      guard (flags.length == conditions.length)
      (conditions.zip flags).mapM fun (condition, asc) => match condition with
        | .asc expr => do
          let body ← render expr
          return if asc then "ASC(" ++ body ++ ")" else body
        | .desc expr => do return "DESC(" ++ (← render expr) ++ ")"
  let clause := fun name (pieces : List String) =>
    if pieces.isEmpty then [] else [name ++ " " ++ String.intercalate " " pieces]
  let values ← if peekTok afterModifiers == .values then do
    let (pattern, rest) ← (pValuesClause fuel state (advTok afterModifiers)).toOption
    let body ← renderData prefixes indent pattern
    pure ([body], rest)
  else some ([], afterModifiers)
  return (clause "GROUP BY" groups ++ clause "HAVING" having ++ clause "ORDER BY" ordering ++
    modifier.offset.toList.map (fun n => s!"OFFSET  {n}") ++
    modifier.limit.toList.map (fun n => s!"LIMIT   {n}") ++ values.1, values.2)

-- The ordinary query AST flattens certain groups and moves FILTERs to their
-- group boundary. Read the already validated token stream with the standard
-- clause parsers to retain their source order for the ARQ serializer.
mutual
private def renderQuerySyntax (prefixes : FormatContext) (state : PState) (fuel indent : Nat)
    (ts : TStream) : Option (String × TStream) := do
  let fuel + 1 := fuel | none
  let (form, rest) ← match peekTok ts with
    | .ask => some ("ASK", advTok ts)
    | .select => do
      let rest := advTok ts
      let (qualification, rest) := match peekTok rest with
        | .distinct => (" DISTINCT", advTok rest)
        | .reduced => (" REDUCED", advTok rest)
        | _ => ("", rest)
      let (selection, rest) ← (pSelectVars fuel state rest).toOption
      pure (← selectText prefixes fuel qualification selection
        (prefixes.syntheticCountSelects.contains (peekPos ts)), rest)
    | _ => none
  let rest := if peekTok rest == .whereKw then advTok rest else rest
  let (body, rest) ← renderGroupSyntax prefixes state fuel (indent + 2) rest
  let (modifiers, rest) ← renderModifiers prefixes state fuel indent rest
  let head := spaces indent ++ form ++ "\n" ++ spaces indent ++ "WHERE\n" ++ body
  return (head ++ "\n" ++ String.join (modifiers.map (fun line => spaces indent ++ line ++ "\n")), rest)

private def renderGroupSyntax (prefixes : FormatContext) (state : PState) (fuel indent : Nat)
    (ts : TStream) : Option (String × TStream) := do
  let fuel + 1 := fuel | none
  let (_, rest) ← (expectTok .lbrace ts).toOption
  if peekTok rest == .select then
    let (body, rest) ← renderQuerySyntax prefixes state fuel (indent + 2) rest
    let (_, rest) ← (expectTok .rbrace rest).toOption
    return (spaces indent ++ "{ " ++ withoutIndent (indent + 2) body ++ spaces indent ++ "}", rest)
  else
    let (lines, rest) ← renderElements prefixes state fuel (indent + 2) rest []
    return (groupText indent lines, rest)

private def renderUnion (prefixes : FormatContext) (state : PState) (fuel indent : Nat)
    (ts : TStream) : Option (String × TStream) := do
  let fuel + 1 := fuel | none
  let (group, rest) ← renderGroupSyntax prefixes state fuel (indent + 2) ts
  if peekTok rest != .union then return (group, rest)
  let (more, rest) ← renderUnion prefixes state fuel indent (advTok rest)
  return (group ++ "\n" ++ spaces indent ++ "UNION\n" ++ more, rest)

private def renderElements (prefixes : FormatContext) (state : PState) (fuel indent : Nat)
    (ts : TStream) (acc : List String) : Option (List String × TStream) := do
  let fuel + 1 := fuel | none
  let token := peekTok ts
  if token == .rbrace then return (acc.reverse, advTok ts)
  let rest := advTok ts
  let (lines, rest) ← if startsTriples token then do
    let (pattern, tail) ← (pTriplesBlock fuel state (.empty, []) ts).toOption
    pure (← renderTriplesBlock prefixes fuel pattern, tail)
  else match token with
    | .lbrace => do
      let (group, tail) ← renderGroupSyntax prefixes state fuel indent ts
      if peekTok tail == .union then
        let (union, tail) ← renderUnion prefixes state fuel indent ts
        pure ([withoutIndent indent union], tail)
      else pure ([withoutIndent indent group], tail)
    | .optional | .minusKw => do
      let (body, tail) ← renderGroupSyntax prefixes state fuel (indent + 2) rest
      pure ([(if token == .optional then "OPTIONAL" else "MINUS") ++ "\n" ++ body], tail)
    | .service | .graph => do
      let silent := token == .service && peekTok rest == .silent
      let rest := if silent then advTok rest else rest
      let (name, rest) ← (pGraphName fuel state rest).toOption
      let name ← renderTerm prefixes name
      let (body, tail) ← renderGroupSyntax prefixes state fuel (indent + 2) rest
      let keyword := if token == .graph then "GRAPH " else if silent then "SERVICE SILENT " else "SERVICE "
      pure ([keyword ++ name ++ "\n" ++ body], tail)
    | .filterKw => do
      let paren := peekTok rest == .lparen
      let candidate := if paren then advTok rest else rest
      let negated := peekTok candidate == .notKw
      let candidate := if negated then advTok candidate else candidate
      if peekTok candidate == .exists then
        let header := if negated then "FILTER NOT EXISTS " else "FILTER EXISTS "
        let groupIndent := indent + header.length
        let (body, tail) ← renderGroupSyntax prefixes state fuel groupIndent (advTok candidate)
        let tail ← if paren then (expectTok .rparen tail).toOption.map Prod.snd else pure tail
        pure ([header ++ withoutIndent groupIndent body], tail)
      else
        let (expr, tail) ← (pFilterExpr fuel state rest).toOption
        pure ([← renderFilter prefixes fuel expr], tail)
    | .bind => do
      let (_, rest) ← (expectTok .lparen rest).toOption
      let (expr, rest) ← (pExpr fuel state rest).toOption
      let (_, rest) ← (expectTok .asKw rest).toOption
      let .var name := peekTok rest | none
      let (_, tail) ← (expectTok .rparen (advTok rest)).toOption
      pure (["BIND(" ++ (← renderExpr prefixes fuel expr) ++ " AS ?" ++ name ++ ")"], tail)
    | .values => do
      let (pattern, tail) ← (pValuesClause fuel state rest).toOption
      pure ([← renderData prefixes indent pattern], tail)
    | _ => none
  renderElements prefixes state fuel indent (skipDot rest) (List.reverse lines ++ acc)
end

private def collectBlankNames : TStream → Std.HashMap String String → Std.HashMap String String
  | [], names => names
  | token :: rest, names =>
    let name := match token.tok with
      | .bnode name => some name
      | .lbracket => some (bracketBnodeId (token :: rest))
      | _ => none
    let names := name.elim names fun name =>
      if names.contains name then names else names.insert name s!"_:b{names.size}"
    collectBlankNames rest names

private def formatPrefix (name iri : String) : String :=
  "PREFIX  " ++ name ++ ":" ++ spaces (max 1 (5 - name.length)) ++ "<" ++ iri ++ ">\n"

/-- Reproduce the pinned ARQ layout for supported syntax. The caller validates
both the input and the result. An unported case retains the source layout. -/
def formatParsedRewrite (text : String) (syntheticCountOrdinals : List Nat := []) : Option String := do
  guard (text.utf8ByteSize <= 8192)
  let tokens := sourceTokens text
  let (state, ts) ← (sourceState tokens []).toOption
  guard state.base.isNone
  let defaults := defaultPrefixes.filter fun (name, _) =>
    ["rdfs", "schema", "skos"].contains name && (lookupPrefix name state.prefixes).isNone
  let prefixes := state.prefixes ++ defaults
  -- ARQ's generated AggCount renders as lowercase count(*). Authored
  -- projections retain the normal uppercase aggregate formatting.
  let syntheticCounts := if syntheticCountOrdinals.isEmpty then [] else
    ((ts.filter (·.tok == .select)).zipIdx).filterMap fun (token, index) =>
      if syntheticCountOrdinals.contains index then some token.pos else none
  let (body, rest) ← renderQuerySyntax ⟨prefixes, collectBlankNames ts {}, syntheticCounts⟩ state 128 0 ts
  guard (tokensOnlyEof rest)
  let used := (sourceTokens body).filterMap fun token => match token.token with
    | .pname name => some (splitPname name).1
    | _ => none
  let declarations := ((prefixes.filter fun (name, _) => used.contains name)
    |>.mergeSort (fun a b => a.1 ≤ b.1)).map fun (name, iri) => formatPrefix name iri
  let (leading, _) := splitLeadingComments text
  let prologue := if declarations.isEmpty then "" else String.join declarations ++ "\n"
  return leading ++ prologue ++ body

end L4Factoidal.Wikidata
