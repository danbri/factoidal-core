import L4Factoidal.SPARQL.QueryJson
import L4Factoidal.Wikidata.Source

/-! Source provenance for the query document AST. The canonical parser decides
which queries are accepted. This pass follows token consumption through the
syntax of an accepted query and mirrors the graph-pattern assembly. An
erasure check against the canonical serializer guards that assembly. -/

namespace L4Factoidal.SPARQL
open L4Factoidal.JSON L4Factoidal.Syntax L4Factoidal.Wikidata RDF

private structure Extent where
  start : Nat
  stop : Nat

private def checkedExtent (length start stop : Nat) : Option Extent :=
  if start < stop ∧ stop ≤ length then some ⟨start, stop⟩ else none

/-- Invariant. Says: every accepted extent is nonempty and within the input.
Does not say: which syntactic occurrence supplied the bounds. -/
theorem checkedExtent_bounds {length start stop : Nat} {extent : Extent}
    (h : checkedExtent length start stop = some extent) :
    extent.start < extent.stop ∧ extent.stop ≤ length := by
  unfold checkedExtent at h
  split at h
  · simp only [Option.some.injEq] at h
    subst extent
    assumption
  · contradiction

#print axioms checkedExtent_bounds

private inductive Origin where
  | exact (extent : Extent)
  | derived (reason : String) (extents : List Extent)
  | synthetic (reason : String)
  | unmapped (reason : String)

private def extentJson (extent : Extent) : Json :=
  .object [("start", .number (toString extent.start)), ("end", .number (toString extent.stop))]

private def originJson : Origin → Json
  | .exact extent => .object [("origin", .string "exact"), ("span", extentJson extent)]
  | .derived reason extents => .object [("origin", .string "derived"), ("reason", .string reason),
      ("spans", .array (extents.map extentJson))]
  | .synthetic reason => .object [("origin", .string "synthetic"), ("reason", .string reason)]
  | .unmapped reason => .object [("origin", .string "unmapped"), ("reason", .string reason)]

private def withOrigin (origin : Origin) : Json → Json
  | .object fields =>
    .object (fields.filter (fun (key, _) => key != "source") ++ [("source", originJson origin)])
  | value => value

private def field (value : Json) (key : String) : Json := (value.field? key).getD .null
private def kind (value : Json) : String := (value.getString? "kind").getD ""

private def replaceField (key : String) (value : Json) : Json → Json
  | .object fields => .object (fields.map fun (name, current) =>
      (name, if name == key then value else current))
  | other => other

private def astNode (name : String) (fields : List (String × Json) := []) : Json :=
  .object (("kind", .string name) :: fields)

-- The previous token's end is keyed by the following token's start.
-- Parser tails keep the same positions after BASE resolution.
private structure Sites where
  length : Nat
  before : Std.HashMap Nat Nat
  lastStop : Nat
  parserFuel : Nat

private def makeSites (length : Nat) (tokens : List LocatedToken) : Sites :=
  let (preceding, lastStop) := tokens.foldl
    (fun (table, stop) token => (table.insert token.start stop, token.stop)) ({}, 0)
  ⟨length, preceding, lastStop, topFuel + length⟩

private def endBefore (sites : Sites) : TStream → Nat
  | [] => sites.lastStop
  | token :: _ => sites.before[token.pos]?.getD 0

private def cursorEq (a b : TStream) : Bool :=
  match a, b with
  | [], [] => true
  | x :: _, y :: _ => x.pos == y.pos
  | _, _ => false

private def extentBetween (sites : Sites) (start stop : TStream) : Option Extent :=
  match start with
  | [] => none
  | next :: _ => checkedExtent sites.length next.pos (endBefore sites stop)

private def exact (sites : Sites) (start stop : TStream) (value : Json) : Json :=
  match extentBetween sites start stop with
  | some extent => withOrigin (.exact extent) value
  | none => withOrigin (.unmapped "missing-token-range") value

private def derived (reason : String) (extents : List Extent) (value : Json) : Json :=
  if extents.isEmpty then withOrigin (.unmapped "missing-token-range") value
  else withOrigin (.derived reason extents) value

private def synthetic (reason : String) : Json → Json := withOrigin (.synthetic reason)

-- Explicit traversal frames keep wide result arrays and deep left-associated
-- pattern joins off the native stack during annotation completion and erasure.
private inductive RewriteFrame where
  | arrayItem (remaining : List Json) (written : List Json)
  | objectField (key : String) (remaining written : List (String × Json))
      (annotation : Option (String × Json))

private inductive RewriteVisit where
  | enter (value : Json)
  | leave (value : Json)

private def rewriteLoop (fallback : Option Json) :
    Nat → RewriteVisit → List RewriteFrame → Option Json
  | 0, _, _ => none
  | f + 1, .enter (.array (head :: rest)), stack =>
    rewriteLoop fallback f (.enter head) (.arrayItem rest [] :: stack)
  | f + 1, .enter value@(.object fields), stack =>
    let (fields, annotation) : List (String × Json) × Option (String × Json) := match fallback with
      | none => (fields.filter (fun entry => entry.1 != "source"), none)
      | some mark =>
        (fields, if (value.getString? "kind").isSome && (value.field? "source").isNone then
          some ("source", mark) else none)
    match fields with
    | [] => rewriteLoop fallback f (.leave (.object annotation.toList)) stack
    | (key, head) :: rest =>
      rewriteLoop fallback f (.enter head) (.objectField key rest [] annotation :: stack)
  | f + 1, .enter value, stack => rewriteLoop fallback f (.leave value) stack
  | _ + 1, .leave value, [] => some value
  | f + 1, .leave value, .arrayItem [] written :: stack =>
    rewriteLoop fallback f (.leave (.array (value :: written).reverse)) stack
  | f + 1, .leave value, .arrayItem (head :: rest) written :: stack =>
    rewriteLoop fallback f (.enter head) (.arrayItem rest (value :: written) :: stack)
  | f + 1, .leave value, .objectField key [] written annotation :: stack =>
    let fields := ((key, value) :: written).reverse ++ annotation.toList
    rewriteLoop fallback f (.leave (.object fields)) stack
  | f + 1, .leave value, .objectField key ((nextKey, head) :: rest) written annotation :: stack =>
    rewriteLoop fallback f (.enter head)
      (.objectField nextKey rest ((key, value) :: written) annotation :: stack)

private def eraseSources (value : Json) : Option Json :=
  rewriteLoop none (2 * value.size + 1) (.enter value) []

private def completeSources (reason : String) (value : Json) : Json :=
  let mark := originJson (.unmapped reason)
  -- Each input value is entered and left at most once. This traversal does
  -- not descend into the new annotations it appends at an object's exit.
  (rewriteLoop (some mark) (2 * value.size + 1) (.enter value) []).getD
    (withOrigin (.unmapped "provenance-traversal-limit") value)

private def wholeSource (length : Nat) (value : Json) : Json :=
  match checkedExtent length 0 length with
  | some extent => withOrigin (.exact extent) value
  | none => value

/-- Transformed WDQS ASTs have no token correspondence to the original text yet. -/
def transformedQuerySources (value : Json) (originalLength : Option Nat := none) : Json :=
  completeSources "named-subquery-transformation"
    (match originalLength with | some length => wholeSource length value | none => value)

private def takeDot (ts : TStream) : TStream :=
  if peekTok ts == .dot then advTok ts else ts

private def takeWhere (ts : TStream) : TStream :=
  if peekTok ts == .whereKw then advTok ts else ts

private def emptyPattern : Json := synthetic "identity-pattern" (astNode "empty")

private def binaryNode (tag : String) (left right : Json) : Json :=
  astNode tag [("left", left), ("right", right)]

private def joined (left right : Json) : Json :=
  if kind left == "empty" then right
  else if kind right == "empty" then left
  else synthetic "implicit-join" (binaryNode "join" left right)

private def nestedJoined (left right : Json) : Json :=
  if kind left == "empty" then right else synthetic "implicit-join" (binaryNode "join" left right)

private structure Placed where
  json : Json
  extent : Option Extent

private structure Triples where
  completed : Json := emptyPattern
  pending : List Placed := []
  completedExtent : Option Extent := none

private def extentCover (first last : Extent) : Extent :=
  ⟨min first.start last.start, max first.stop last.stop⟩

private def flush (parts : Triples) : Json :=
  match parts.pending with
  | [] => parts.completed
  | last :: _ =>
    let inOrder := parts.pending.reverse
    let pending := inOrder.map (·.json)
    let evidence := do
      let first ← inOrder.head?
      return extentCover (← first.extent) (← last.extent)
    let bgp := fun evidence triples =>
      derived "triple-pattern-group" evidence (astNode "bgp" [("triples", .array triples)])
    match kind parts.completed with
    | "empty" => bgp evidence.toList pending
    | "bgp" =>
      let existing := (parts.completed.getArray? "triples").getD []
      bgp (parts.completedExtent.toList ++ evidence.toList) (existing ++ pending)
    | _ =>
      inOrder.foldl (fun pattern item => joined pattern (bgp item.extent.toList [item.json])) parts.completed

private def addExtras (parts : Triples) (extra : Json) (extent : Option Extent := none) : Triples :=
  if kind extra == "empty" then parts else ⟨joined (flush parts) extra, [], extent⟩

private def exactPlaced (sites : Sites) (start stop : TStream) (value : Json) : Placed :=
  ⟨exact sites start stop value, extentBetween sites start stop⟩

private def authoredTriple (subject verb object : Placed) (isPath reusedSubject reusedVerb : Bool)
    (expansion : Option String) : Placed :=
  let tag := if isPath then "propertyPath" else "triple"
  let verbKey := if isPath then "path" else "predicate"
  let node := astNode tag [("subject", subject.json), (verbKey, verb.json), ("object", object.json)]
  let evidence := subject.extent.toList ++ verb.extent.toList ++ object.extent.toList
  let cover := do return extentCover (← subject.extent) (← object.extent)
  let origin := match expansion with
    | some reason => derived reason evidence node
    | none =>
      if reusedVerb then derived "object-list" evidence node
      else if reusedSubject then derived "predicate-list" evidence node
      else match cover with
        | some extent => withOrigin (.exact extent) node
        | none => withOrigin (.unmapped "missing-token-range") node
  ⟨origin, cover⟩

private def lastInfix (operand : TStream → Except ParseError (α × TStream)) (operator : Token → Bool)
    (target : TStream) : Nat → TStream → Option TStream → Option TStream
  | 0, _, _ => none
  | f + 1, ts, previous => do
    let (_, next) ← (operand ts).toOption
    if cursorEq next target then previous
    else if operator (peekTok next) then lastInfix operand operator target f (advTok next) (some next)
    else none

private def pathSuffix (tag : String) : Token :=
  match tag with
  | "zeroOrMore" => .star
  | "oneOrMore" => .plus
  | _ => .qmark

mutual
private def tracePath (sites : Sites) (st : PState) : Nat → Json → TStream → TStream → Json
  | 0, value, _, _ => value
  | f + 1, value, ts, stop => Id.run do
    let tag := kind value
    if peekTok ts == .lparen then
      if let .ok (_, close) := pPathAlternative sites.parserFuel st (advTok ts) then
        if peekTok close == .rparen && cursorEq (advTok close) stop then
          return tracePath sites st f value (advTok ts) close
    let traced := match tag with
      | "alternative" | "sequence" =>
        let (term, operator) := if tag == "alternative" then
          (pPathSequence sites.parserFuel st, Token.pipe)
          else (pPathEltOrInverse sites.parserFuel st, Token.slash)
        match lastInfix term (· == operator) stop 128 ts none with
        | none => value
        | some split =>
          value
            |> replaceField "left" (tracePath sites st f (field value "left") ts split)
            |> replaceField "right" (tracePath sites st f (field value "right") (advTok split) stop)
      | "inverse" =>
        if peekTok ts == .caret then
          replaceField "path" (tracePath sites st f (field value "path") (advTok ts) stop) value
        else value
      | "zeroOrMore" | "oneOrMore" | "zeroOrOne" =>
        match pPathPrimary sites.parserFuel st ts with
        | .ok (_, suffix) =>
          if peekTok suffix == pathSuffix tag && cursorEq (advTok suffix) stop then
            replaceField "path" (tracePath sites st f (field value "path") ts suffix) value
          else value
        | .error _ => value
      | "negatedSet" =>
        let members := advTok ts
        let members := if peekTok members == .lparen then advTok members else members
        match (field value "paths").asArray? with
        | some paths =>
          replaceField "paths" (.array (traceNegatedPaths sites st f paths members [])) value
        | none => value
      | _ => value
    return exact sites ts stop traced

private def traceNegatedPaths (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → List Json
  | 0, paths, _, done => done.reverse ++ paths
  | _, [], _, done => done.reverse
  | f + 1, path :: paths, ts, done =>
    match pPathOneInSet sites.parserFuel st ts with
    | .ok (_, next) =>
      let item := tracePath sites st f path ts next
      traceNegatedPaths sites st f paths (advTok next) (item :: done)
    | .error _ => done.reverse ++ path :: paths
end

private def unsupportedPattern (reason : String) (pattern : QueryPattern) : Json :=
  if let .empty := pattern then emptyPattern else completeSources reason (patternJson pattern)

private def collectionCells (close : Extent) (cells : List (String × Placed × Json)) : Json :=
  let nil := derived "collection-terminator" [close] (patternTermJson (.iri rdfNilIri))
  let (_, _, pattern) := cells.foldl (fun (nextTerm, nextExtent, rest) (id, item, extra) =>
    let evidence := item.extent.toList
    let linkage := evidence ++ nextExtent.toList
    let cell := derived "collection-cell" evidence (patternSubjectJson (.bnode id))
    let firstPred := derived "collection-first-predicate" evidence (patternTermJson (.iri rdfFirstIri))
    let restPred := derived "collection-rest-predicate" linkage (patternTermJson (.iri rdfRestIri))
    let first := derived "collection" evidence
      (astNode "triple" [("subject", cell), ("predicate", firstPred), ("object", item.json)])
    let restTriple := derived "collection" linkage
      (astNode "triple" [("subject", cell), ("predicate", restPred), ("object", nextTerm)])
    let bgp := derived "collection" linkage (astNode "bgp" [("triples", .array [first, restTriple])])
    (cell, item.extent, joined (joined bgp extra) rest)) (nil, some close, emptyPattern)
  pattern

mutual
private def traceObject (sites : Sites) (st : PState) :
    Nat → TStream → Except ParseError ((PatternTerm × Placed × Json) × TStream)
  | 0, ts => pErr "source provenance depth limit" ts
  | f + 1, ts => do
    let ((term, extras), stop) ← pObjectWithExtras sites.parserFuel st ts
    let (marked, pattern) ← traceTerm sites st f (patternTermJson term) extras ts stop
    return ((term, marked, pattern), stop)

private def traceTerm (sites : Sites) (st : PState) :
    Nat → Json → QueryPattern → TStream → TStream → Except ParseError (Placed × Json)
  | 0, value, extras, ts, stop =>
    .ok (exactPlaced sites ts stop value, unsupportedPattern "provenance-depth-limit" extras)
  | f + 1, value, extras, ts, stop => do
    let placed := exactPlaced sites ts stop value
    match peekTok ts with
    | .lbracket =>
      let inner := advTok ts
      if peekTok inner == .rbracket then return (placed, emptyPattern)
      let shared := { placed with
        json := derived "blank-node-property-list" placed.extent.toList value }
      let subject := PatternSubject.bnode (bracketBnodeId ts)
      let (parts, close) ← tracePredicates sites st f subject shared {} false
        (some "blank-node-property-list") inner
      if peekTok close == .rbracket && cursorEq (advTok close) stop then
        return (shared, flush parts)
      else pErr "source provenance blank-node range mismatch" close
    | .lparen =>
      let itemStart := advTok ts
      let (cells, close) ← traceCollection sites st f itemStart []
      if !cursorEq (advTok close) stop then pErr "source provenance collection range mismatch" close
      else
        let marked := { placed with json := derived "collection" placed.extent.toList value }
        match extentBetween sites close stop with
        | some closing => return (marked, collectionCells closing cells)
        | none => return (marked, unsupportedPattern "missing-token-range" extras)
    | .ttBareOpen =>
      return ({ placed with json := derived "reified-triple-term" placed.extent.toList value },
        unsupportedPattern "reified-triple-pattern" extras)
    | _ => return (placed, unsupportedPattern "triple-term-expansion" extras)

private def traceCollection (sites : Sites) (st : PState) :
    Nat → TStream → List (String × Placed × Json) →
      Except ParseError ((List (String × Placed × Json)) × TStream)
  | 0, ts, _ => pErr "source provenance collection limit" ts
  | f + 1, ts, cells =>
    if peekTok ts == .rparen then .ok (cells, ts)
    else do
      let ((_, placed, extra), next) ← traceObject sites st f ts
      traceCollection sites st f next ((freshBnodeId ts, placed, extra) :: cells)

private def tracePredicates (sites : Sites) (st : PState) :
    Nat → PatternSubject → Placed → Triples → Bool → Option String → TStream → Except ParseError (Triples × TStream)
  | 0, _, _, _, _, _, ts => pErr "source provenance predicate limit" ts
  | f + 1, subject, placed, parts, reused, expansion, ts => do
    let (verb, ts1) ← pVerb sites.parserFuel st ts
    let verbPlace := match verb with
      | .inl term => ⟨tracePath sites st 64 (patternTermJson term) ts ts1, extentBetween sites ts ts1⟩
      | .inr path => ⟨tracePath sites st 64 (pathJson path) ts ts1, extentBetween sites ts ts1⟩
    let (parts, ts2) ← traceObjects sites st f subject placed verb verbPlace parts reused false expansion ts1
    if peekTok ts2 == .semi then
      let next := advTok ts2
      if endsPredObjList (peekTok next) then return (parts, next)
      else tracePredicates sites st f subject placed parts true expansion next
    else return (parts, ts2)

private def traceObjects (sites : Sites) (st : PState) :
    Nat → PatternSubject → Placed → (PatternTerm ⊕ PropertyPath) → Placed → Triples → Bool →
      Bool → Option String → TStream → Except ParseError (Triples × TStream)
  | 0, _, _, _, _, _, _, _, _, ts => pErr "source provenance object limit" ts
  | f + 1, subject, placed, verb, verbPlace, parts, reusedSubject, reusedVerb, expansion, ts => do
    let triple := fun object isPath => authoredTriple placed verbPlace object isPath reusedSubject reusedVerb expansion
    match verb with
    | .inl predicate =>
      if isFulltextPredicate predicate then
        let (literal, next) ← pFulltextObject sites.parserFuel st ts
        let extent := extentBetween sites ts next
        let obj := ⟨derived "fulltext-arguments" extent.toList (patternTermJson (.literal literal)), extent⟩
        return ({ parts with pending := triple obj false :: parts.pending }, next)
      else
        let ((term, obj, extras), ts1) ← traceObject sites st f ts
        let parts := addExtras { parts with pending := triple obj false :: parts.pending } extras obj.extent
        let (annotations, ts2) ← pAnnotations sites.parserFuel st subject predicate term none ts1
        let parts := addExtras parts (unsupportedPattern "rdf-star-annotation" annotations)
        if peekTok ts2 == .comma then
          traceObjects sites st f subject placed verb verbPlace parts reusedSubject true expansion (advTok ts2)
        else return (parts, ts2)
    | .inr _ =>
      let ((_, obj, extras), ts1) ← traceObject sites st f ts
      let parts := addExtras ⟨joined (flush parts) (triple obj true).json, [], none⟩ extras obj.extent
      if peekTok ts1 == .comma then
        traceObjects sites st f subject placed verb verbPlace parts reusedSubject true expansion (advTok ts1)
      else return (parts, ts1)
end

private def traceTriples (sites : Sites) (st : PState) :
    Nat → Triples → TStream → Except ParseError (Json × TStream)
  | 0, _, ts => pErr "source provenance triples limit" ts
  | f + 1, parts, ts => do
    let ((subject, extras, optional), ts1) ← pSubjectWithExtras sites.parserFuel st ts
    let (placed, extras) ← traceTerm sites st f (patternSubjectJson subject) extras ts ts1
    let parts := addExtras parts extras placed.extent
    let (parts, ts2) ← match tracePredicates sites st f subject placed parts false none ts1 with
      | .ok result => .ok result
      | .error error => if optional then .ok (parts, ts1) else .error error
    let next := takeDot ts2
    if peekTok ts2 == .dot && startsTriples (peekTok next) then traceTriples sites st f parts next
    else return (flush parts, next)

private def leftCondition (filters : List (Placed × Placed)) : Json :=
  match filters.reverse with
  | [] => synthetic "optional-default-condition" (exprJson (.boolLit true))
  | (clause, expression) :: rest =>
    let initial : Placed := ⟨expression.json, clause.extent⟩
    let condition := rest.foldl (fun previous (nextClause, nextExpression) =>
      let evidence := previous.extent.toList ++ nextClause.extent.toList
      let both := do return extentCover (← previous.extent) (← nextClause.extent)
      ⟨derived "optional-filter-conjunction" evidence (binaryNode "and" previous.json nextExpression.json),
        both⟩) initial
    condition.json

private def wrapSourceFilters (filters : List (Placed × Placed)) (body : Json) : Json :=
  filters.foldl (fun pattern (clause, expression) =>
    replaceField "condition" expression.json (replaceField "pattern" pattern clause.json)) body

private def compareToken (op : String) : Token :=
  match op with
  | "=" => .eq | "!=" => .ne | "<" => .lt | ">" => .gt | "<=" => .le | _ => .ge

private def arithmeticToken (op : String) : Token :=
  match op with
  | "+" => .plus | "-" => .minusOp | "*" => .star | _ => .slash

private def binaryExpression (sites : Sites) (st : PState) (value : Json)
    (ts stop : TStream) : Option TStream :=
  let find (operand : TStream → Except ParseError (Expr × TStream)) (operator : Token → Bool) :=
    lastInfix operand operator stop 128 ts none
  let op := (value.getString? "operator").getD ""
  let split := match kind value with
    | "and" => find (pRelExpr sites.parserFuel st) (· == Token.and)
    | "or" => find (pAndExpr sites.parserFuel st) (· == Token.or)
    | "compare" => find (pAddExpr sites.parserFuel st) (· == compareToken op)
    | "arith" =>
      if op == "+" || op == "-" then
        find (pMulExpr sites.parserFuel st) (fun token => token == Token.plus || token == Token.minusOp)
      else find (pUnaryExpr sites.parserFuel st) (fun token => token == Token.star || token == Token.slash)
    | _ => none
  split.filter fun pivot =>
    if kind value == "arith" then peekTok pivot == arithmeticToken op else true

private def exprPrefix (tag : String) : Option Token :=
  match tag with
  | "unaryPlus" => some .plus
  | "unaryMinus" => some .minusOp
  | "not" => some .bang
  | _ => none

private def takeComma (ts : TStream) : TStream :=
  if peekTok ts == .comma then advTok ts else ts

private def selectStart (ts : TStream) : TStream :=
  let next := advTok ts
  if peekTok next == .distinct || peekTok next == .reduced then advTok next else next

private def arrayField (value : Json) (key : String) : List Json := (value.getArray? key).getD []

private def derivedCopy (reason : String) (value : Json) : Json :=
  let source := field value "source"
  let evidence := match source.field? "span" with
    | some span => [span]
    | none => arrayField source "spans"
  if evidence.isEmpty then withOrigin (.unmapped reason) value
  else replaceField "source" (.object [("origin", .string "derived"), ("reason", .string reason),
    ("spans", .array evidence)]) value

private def templateTriples : Nat → List Json → List (List Json) → List Json
  | 0, _, found => found.reverse.flatten
  | _ + 1, [], found => found.reverse.flatten
  | f + 1, value :: rest, found =>
    match kind value with
    | "bgp" => templateTriples f rest (arrayField value "triples" :: found)
    | "join" => templateTriples f (field value "left" :: field value "right" :: rest) found
    | _ => templateTriples f rest found

mutual
private def traceExpr (sites : Sites) (st : PState) : Nat → Json → TStream → TStream → Json
  | 0, value, ts, stop => exact sites ts stop value
  | f + 1, value, ts, stop => Id.run do
    if peekTok ts == .lparen then
      if let .ok (_, close) := pExpr sites.parserFuel st (advTok ts) then
        if peekTok close == .rparen && cursorEq (advTok close) stop then
          return traceExpr sites st f value (advTok ts) close
    let tag := kind value
    if tag == "and" || tag == "or" || tag == "compare" || tag == "arith" then
      match binaryExpression sites st value ts stop with
      | none => return exact sites ts stop value
      | some split =>
        let left := traceExpr sites st f (field value "left") ts split
        let right := traceExpr sites st f (field value "right") (advTok split) stop
        return exact sites ts stop (value |> replaceField "left" left |> replaceField "right" right)
    if let some prefixToken := exprPrefix tag then
      if peekTok ts == prefixToken then
        let arg := traceExpr sites st f (field value "arg") (advTok ts) stop
        return exact sites ts stop (replaceField "arg" arg value)
    if tag == "existsPat" || tag == "notExistsPat" then
      let groupStart := if tag == "notExistsPat" then advTok (advTok ts) else advTok ts
      if let .ok (pattern, next) := traceGroup sites st f groupStart then
        if cursorEq next stop then
          return exact sites ts stop (replaceField "pattern" pattern value)
    if tag == "inList" || tag == "notInList" then
      if let .ok (_, split) := pAddExpr sites.parserFuel st ts then
        let inToken := if tag == "notInList" then advTok split else split
        let paren := advTok inToken
        if peekTok inToken == .inKw && peekTok paren == .lparen then
          let arg := traceExpr sites st f (field value "arg") ts split
          let args := traceExprArgs sites st f (arrayField value "args") (advTok paren) []
          return exact sites ts stop (value |> replaceField "arg" arg |> replaceField "args" (.array args))
      return exact sites ts stop value
    let paren := advTok ts
    if peekTok paren == .lparen then
      let start := advTok paren
      let start := if tag == "aggregate" && peekTok start == .distinct then advTok start else start
      if tag == "aggregate" && kind (field value "arg") == "wildcard" && peekTok start == .star then
        return exact sites ts stop
          (replaceField "arg" (exact sites start (advTok start) (field value "arg")) value)
      if let some args := value.getArray? "args" then
        let traced := traceExprArgs sites st f args start []
        return exact sites ts stop (replaceField "args" (.array traced) value)
      if let .object fields := value then
        let children := fields.filter fun (_, child) => (child.getString? "kind").isSome
        let traced := traceExprFields sites st f children start value
        return exact sites ts stop traced
    return exact sites ts stop value

private def traceExprArgs (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → List Json
  | 0, args, _, done => done.reverse ++ args
  | _, [], _, done => done.reverse
  | f + 1, arg :: args, ts, done =>
    match pExpr sites.parserFuel st ts with
    | .ok (_, next) =>
      if cursorEq ts next then done.reverse ++ arg :: args
      else traceExprArgs sites st f args (takeComma next) (traceExpr sites st f arg ts next :: done)
    | .error _ => done.reverse ++ arg :: args

private def traceExprFields (sites : Sites) (st : PState) :
    Nat → List (String × Json) → TStream → Json → Json
  | 0, _, _, value | _, [], _, value => value
  | f + 1, (key, argument) :: rest, ts, value =>
    match pExpr sites.parserFuel st ts with
    | .ok (_, next) =>
      if cursorEq ts next then value
      else
        let marked := traceExpr sites st f argument ts next
        traceExprFields sites st f rest (takeComma next) (replaceField key marked value)
    | .error _ => value

private def traceGroup (sites : Sites) (st : PState) : Nat → TStream → Except ParseError (Json × TStream)
  | 0, ts => pErr "source provenance group limit" ts
  | f + 1, ts => do
    let ((pattern, filters), next) ← traceGroupParts sites st f ts
    return (wrapSourceFilters filters pattern, next)

private def traceGroupParts (sites : Sites) (st : PState) :
    Nat → TStream → Except ParseError ((Json × List (Placed × Placed)) × TStream)
  | 0, ts => pErr "source provenance group limit" ts
  | f + 1, ts => do
    let (_, start) ← expectTok .lbrace ts
    match peekTok start with
    | .select =>
      let (query, stop) ← pSelectQuery sites.parserFuel st none start
      let (marked, next) ← traceQuery sites { st with base := none } f (queryAstJson query) start
      if !cursorEq stop next then pErr "source provenance subquery range mismatch" next
      else
        let (_, close) ← expectTok .rbrace next
        return ((exact sites ts close (astNode "subSelect" [("query", marked)]), []), close)
    | .rbrace =>
      let close := advTok start
      return ((exact sites ts close (astNode "empty"), []), close)
    | _ =>
      let (parts, tail) ← traceGroupBody sites st f emptyPattern [] start
      let (_, close) ← expectTok .rbrace tail
      return (parts, close)

private def traceGroupBody (sites : Sites) (st : PState) :
    Nat → Json → List (Placed × Placed) → TStream → Except ParseError ((Json × List (Placed × Placed)) × TStream)
  | 0, _, _, ts => pErr "source provenance group body limit" ts
  | f + 1, pattern, filters, ts => do
    let token := peekTok ts
    if startsTriples token then
      let (triples, next) ← traceTriples sites st f {} ts
      traceGroupBody sites st f (joined pattern triples) filters next
    else match token with
    | .optional =>
      let ((right, conditions), next) ← traceGroupParts sites st f (advTok ts)
      let node := astNode "leftJoin" [("left", pattern), ("right", right), ("condition", leftCondition conditions)]
      traceGroupBody sites st f (exact sites ts next node) filters (takeDot next)
    | .minusKw | .lateral =>
      let (right, next) ← traceGroup sites st f (advTok ts)
      let tag := if token == .minusKw then "minus" else "lateral"
      let node := exact sites ts next (binaryNode tag pattern right)
      traceGroupBody sites st f node filters (takeDot next)
    | .graph =>
      let nameStart := advTok ts
      let (name, groupStart) ← pGraphName sites.parserFuel st nameStart
      let (body, next) ← traceGroup sites st f groupStart
      let graph := exact sites nameStart groupStart (patternTermJson name)
      let node := exact sites ts next (astNode "graph" [("graph", graph), ("pattern", body)])
      traceGroupBody sites st f (joined pattern node) filters (takeDot next)
    | .service =>
      let start := advTok ts
      let silent := peekTok start == .silent
      let endpointStart := if silent then advTok start else start
      let (endpoint, groupStart) ← pGraphName sites.parserFuel st endpointStart
      let tag := if let .var _ := endpoint then "serviceVar" else "service"
      let (body, next) ← traceGroup sites st f groupStart
      let endpoint := exact sites endpointStart groupStart (patternTermJson endpoint)
      let node := exact sites ts next (astNode tag
        [("endpoint", endpoint), ("silent", .bool silent), ("pattern", body)])
      traceGroupBody sites st f (joined pattern node) filters (takeDot next)
    | .filterKw =>
      let expressionStart := advTok ts
      let (expression, next) ← pFilterExpr sites.parserFuel st expressionStart
      let marked := traceExpr sites st f (exprJson expression) expressionStart next
      let clause := exactPlaced sites ts next
        (astNode "filter" [("condition", .null), ("pattern", .null)])
      let expression := ⟨marked, extentBetween sites expressionStart next⟩
      traceGroupBody sites st f pattern ((clause, expression) :: filters) (takeDot next)
    | .bind =>
      let (_, start) ← expectTok .lparen (advTok ts)
      let (expression, asToken) ← pExpr sites.parserFuel st start
      let (_, variableToken) ← expectTok .asKw asToken
      let .var name := peekTok variableToken | pErr "source provenance BIND variable" variableToken
      let (_, next) ← expectTok .rparen (advTok variableToken)
      let marked := traceExpr sites st f (exprJson expression) start asToken
      let node := exact sites ts next (astNode "bind"
        [("expression", marked), ("variable", .string name), ("pattern", pattern)])
      traceGroupBody sites st f node filters (takeDot next)
    | .values =>
      let (values, next) ← pValuesClause sites.parserFuel st (advTok ts)
      let node := exact sites ts next (patternJson values)
      traceGroupBody sites st f (joined pattern node) filters (takeDot next)
    | .lbrace =>
      let (nested, next) ← traceUnion sites st f ts
      traceGroupBody sites st f (nestedJoined pattern nested) filters (takeDot next)
    | _ => return ((pattern, filters), ts)

private def traceUnion (sites : Sites) (st : PState) : Nat → TStream → Except ParseError (Json × TStream)
  | 0, ts => pErr "source provenance UNION limit" ts
  | f + 1, ts => do
    let (left, next) ← traceGroup sites st f ts
    if peekTok next == .union then
      let (right, stop) ← traceUnion sites st f (advTok next)
      return (exact sites ts stop (binaryNode "union" left right), stop)
    else return (left, next)

private def traceProjection (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → Except ParseError ((List Json) × TStream)
  | 0, _, ts, _ => pErr "source provenance projection limit" ts
  | _ + 1, [], ts, done => .ok (done.reverse, ts)
  | f + 1, item :: items, ts, done => do
    match peekTok ts with
    | .var _ =>
      let next := advTok ts
      traceProjection sites st f items next (exact sites ts next item :: done)
    | .lparen =>
      let start := advTok ts
      let (_, asToken) ← pExpr sites.parserFuel st start
      let (_, variableToken) ← expectTok .asKw asToken
      let (_, next) ← expectTok .rparen (advTok variableToken)
      let expression := traceExpr sites st f (field item "expression") start asToken
      let projected := exact sites ts next (replaceField "expression" expression item)
      traceProjection sites st f items next (projected :: done)
    | _ => pErr "source provenance projection item" ts

private def traceGroupBy (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → Except ParseError ((List Json) × TStream)
  | 0, _, ts, _ => pErr "source provenance GROUP BY limit" ts
  | _ + 1, [], ts, done => .ok (done.reverse, ts)
  | f + 1, item :: items, ts, done => do
    let (group, next) ← pGroupCondition sites.parserFuel st ts
    let marked ← match group with
      | .var _ => pure (exact sites ts next item)
      | .expr _ _ => do
        let start := if peekTok ts == .lparen then advTok ts else ts
        let (_, stop) ← pExpr sites.parserFuel st start
        let expression := traceExpr sites st f (field item "expression") start stop
        pure (exact sites ts next (replaceField "expression" expression item))
    traceGroupBy sites st f items next (marked :: done)

private def traceHaving (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → Except ParseError ((List Json) × TStream)
  | 0, _, ts, _ => pErr "source provenance HAVING limit" ts
  | _ + 1, [], ts, done => .ok (done.reverse, ts)
  | f + 1, item :: items, ts, done => do
    let parse := if peekTok ts == .lparen then pFilterExpr else pPrimaryExpr
    let (_, next) ← parse sites.parserFuel st ts
    let marked := traceExpr sites st f item ts next
    traceHaving sites st f items next (marked :: done)

private def traceOrderBy (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → Except ParseError ((List Json) × TStream)
  | 0, _, ts, _ => pErr "source provenance ORDER BY limit" ts
  | _ + 1, [], ts, done => .ok (done.reverse, ts)
  | f + 1, item :: items, ts, done => do
    let (_, next) ← pOrderCondition sites.parserFuel st ts
    let explicit := peekTok ts == .asc || peekTok ts == .desc
    let candidate := if explicit then advTok ts else ts
    let start := if peekTok candidate == .lparen then advTok candidate else candidate
    -- Bare ORDER BY variables consume one token, even if another expression follows.
    let expressionEnd ← if !explicit && (match peekTok ts with | .var _ => true | _ => false) then
        pure next
      else do let (_, stop) ← pExpr sites.parserFuel st start
              pure stop
    let expression := traceExpr sites st f (field item "expression") start expressionEnd
    let node := replaceField "expression" expression item
    let marked := if explicit then exact sites ts next node
      else derived "default-ascending-order" (extentBetween sites ts next).toList node
    traceOrderBy sites st f items next (marked :: done)

private def traceQuery (sites : Sites) (st : PState) : Nat → Json → TStream → Except ParseError (Json × TStream)
  | 0, _, ts => pErr "source provenance query depth limit" ts
  | f + 1, value, ts => do
    let form := field value "form"
    let (form, afterForm, templateFromWhere) ← match peekTok ts with
      | .select =>
        let start := selectStart ts
        if peekTok start == .star then
          let next := advTok start
          let projection := exact sites start next (field form "projection")
          pure (exact sites ts next (replaceField "projection" projection form), next, false)
        else do
          let (projection, next) ← traceProjection sites st f (arrayField form "projection") start []
          pure (exact sites ts next (replaceField "projection" (.array projection) form), next, false)
      | .construct =>
        let start := advTok ts
        if peekTok start == .lbrace then do
          let (template, next) ← traceGroup sites st f start
          let template := .array (templateTriples sites.parserFuel [template] [])
          pure (exact sites ts next (replaceField "template" template form), next, false)
        else pure (exact sites ts start form, start, true)
      | .describe =>
        let start := advTok ts
        if peekTok start == .star then
          let next := advTok start
          pure (exact sites ts next form, next, false)
        else do
          let (targets, next) ← traceTargets sites st f (arrayField form "targets") start []
          pure (exact sites ts next (replaceField "targets" (.array targets) form), next, false)
      | .ask =>
        let next := advTok ts
        pure (exact sites ts next form, next, false)
      | _ => pErr "source provenance query form" ts
    let (dataset, afterDataset) ← traceDataset sites st f (arrayField value "dataset") afterForm []
    let groupStart := takeWhere afterDataset
    let (pattern, afterGroup) ← if peekTok groupStart == .lbrace then
        traceGroup sites st f groupStart
      else pure (emptyPattern, groupStart)
    let form := if templateFromWhere then
        let triples := templateTriples sites.parserFuel [pattern] []
        replaceField "template" (.array (triples.map (derivedCopy "construct-where-template"))) form
      else form
    let (groupBy, afterGroupBy) ← if peekTok afterGroup == .group then do
        let (items, next) ← traceGroupBy sites st f (arrayField value "groupBy")
          (advTok (advTok afterGroup)) []
        pure (Json.array items, next)
      else pure (Json.null, afterGroup)
    let (having, afterHaving) ← if peekTok afterGroupBy == .having then
        traceHaving sites st f (arrayField value "having") (advTok afterGroupBy) []
      else pure ([], afterGroupBy)
    let modifier := field value "modifier"
    let modifier ← if peekTok afterHaving == .order then do
        let (items, _) ← traceOrderBy sites st f (arrayField modifier "orderBy")
          (advTok (advTok afterHaving)) []
        pure (replaceField "orderBy" (.array items) modifier)
      else pure modifier
    let (_, afterModifier) ← pSolutionModifier sites.parserFuel st afterGroup
    let (values, stop) ← pTrailingValues sites.parserFuel st afterModifier
    let pattern := match values, field value "postValues" with
      | some vals, .null => joined pattern (exact sites afterModifier stop (patternJson vals))
      | _, _ => pattern
    let marked := value
      |> replaceField "form" form
      |> replaceField "dataset" (.array dataset)
      |> replaceField "pattern" pattern
      |> replaceField "groupBy" groupBy
      |> replaceField "having" (.array having)
      |> replaceField "modifier" modifier
    return (exact sites ts stop marked, stop)

private def traceDataset (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → Except ParseError ((List Json) × TStream)
  | 0, _, ts, _ => pErr "source provenance dataset limit" ts
  | _ + 1, [], ts, done => .ok (done.reverse, ts)
  | f + 1, item :: items, ts, done => do
    let (_, graph) ← expectTok .fromKw ts
    let name := if peekTok graph == .named then advTok graph else graph
    let (_, next) ← pGraphName sites.parserFuel st name
    traceDataset sites st f items next (exact sites ts next item :: done)

private def traceTargets (sites : Sites) (st : PState) :
    Nat → List Json → TStream → List Json → Except ParseError ((List Json) × TStream)
  | 0, _, ts, _ => pErr "source provenance DESCRIBE limit" ts
  | _ + 1, [], ts, done => .ok (done.reverse, ts)
  | f + 1, item :: items, ts, done => do
    let (_, next) ← pGraphName sites.parserFuel st ts
    traceTargets sites st f items next (exact sites ts next item :: done)
end

private def checkedTrace (canonical candidate : Json) : Option Json :=
  if eraseSources candidate = some canonical then some candidate else none

/-- Invariant. Says: a candidate accepted by the compatibility check erases to
the canonical AST. Does not say: every exact range names the correct occurrence. -/
theorem checkedTrace_erases {canonical candidate accepted : Json}
    (h : checkedTrace canonical candidate = some accepted) :
    eraseSources accepted = some canonical := by
  unfold checkedTrace at h
  split at h
  · simp only [Option.some.injEq] at h
    subst accepted
    assumption
  · contradiction

#print axioms checkedTrace_erases

/-- Attach original-source locations to a successfully parsed query. The
provenance fuel limits replay independently of the shipping parser. -/
def queryAstWithSources (length : Nat) (tokens : List LocatedToken)
    (state : PState) (body : TStream) (query : Query) : Json :=
  let canonical := queryAstJson query
  let sites := makeSites length tokens
  let fallback := fun reason => completeSources reason (wholeSource length canonical)
  match traceQuery sites state (min 1024 (tokens.length + 32)) canonical (resolveIriTokens state.base body) with
  | .ok (candidate, []) =>
    -- The full Unicode source slice includes prologue, comments and trivia.
    let candidate := match checkedExtent length 0 length with
      | some extent => replaceField "source" (originJson (.exact extent)) candidate
      | none => candidate
    match checkedTrace canonical candidate with
    | some checked => completeSources "untracked-ast-node" checked
    | none => fallback "provenance-ast-mismatch"
  | _ => fallback "provenance-trace-incomplete"

end L4Factoidal.SPARQL
