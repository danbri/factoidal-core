import L4Factoidal.Wikidata.Source

namespace L4Factoidal.SPARQL
open L4Factoidal.Wikidata

/-- A span of authored graph syntax, before semantic AST nodes are combined. -/
structure QuerySourceRange where
  start : Nat
  stop : Nat

structure QuerySourceAnchor where
  kind : String
  range : QuerySourceRange
  derived : Bool := false
  subject : Option QuerySourceRange := none
  predicate : Option QuerySourceRange := none
  object : Option QuerySourceRange := none

private def consumed (stops : Std.HashMap Nat Nat) (before after : TStream) : QuerySourceRange :=
  let last := (before.takeWhile fun token => after.isEmpty || token.pos < peekPos after).getLast?
  let start := peekPos before
  ⟨start, (last.map (fun token => stops.getD token.pos token.pos)).getD start⟩

private def spanSince (stops : Std.HashMap Nat Nat) (kind : String)
    (before after : TStream) : QuerySourceAnchor :=
  { kind := kind, range := consumed stops before after }

/-- Use the standard verb and object parsers to split a property list into
its source pieces. The grammar conversions stay in the standard parser. -/
private def tripleObjects (state : PState) (stops : Std.HashMap Nat Nat)
    (subject predicate : QuerySourceRange) (kind : String) (firstPredicate : Bool) :
    Nat → Bool → TStream → List QuerySourceAnchor → List QuerySourceAnchor × TStream
  | 0, _, stream, found => (found, stream)
  | fuel + 1, firstObject, stream, found =>
    match pObjectWithExtras topFuel state stream with
    | .error _ => (found, stream)
    | .ok (_, after) =>
      let object := consumed stops stream after
      let exact := firstPredicate && firstObject
      let start := if exact then subject.start else if firstObject then predicate.start else object.start
      let found := ⟨kind, ⟨start, object.stop⟩, !exact, some subject, some predicate, some object⟩ :: found
      if peekTok after == .comma then
        tripleObjects state stops subject predicate kind firstPredicate fuel false (advTok after) found
      else (found, after)

private def tripleProperties (state : PState) (stops : Std.HashMap Nat Nat)
    (subject : QuerySourceRange) :
    Nat → Bool → TStream → List QuerySourceAnchor → List QuerySourceAnchor
  | 0, _, _, found => found
  | fuel + 1, first, stream, found =>
    match pVerb topFuel state stream with
    | .error _ => found
    | .ok (verb, objects) =>
      let predicate := consumed stops stream objects
      let kind := match verb with | .inl _ => "triple" | .inr _ => "propertyPath"
      let (found, after) := tripleObjects state stops subject predicate kind first
        fuel true objects found
      if peekTok after == .semi && !endsPredObjList (peekTok (advTok after)) then
        tripleProperties state stops subject fuel false (advTok after) found
      else found

private def clauseTail (state : PState) (site : PosToken) (tail : TStream) :
    Option (String × TStream) := do
  match site.tok with
  | .optional | .minusKw | .union | .lateral =>
    let kind := match site.tok with
      | .optional => "optional" | .minusKw => "minus" | .union => "unionBranch" | _ => "lateral"
    let (_, rest) ← (pGroupGraphPattern topFuel state tail).toOption
    some (kind, rest)
  | .filterKw =>
    let (_, rest) ← (pFilterExpr topFuel state tail).toOption
    some ("filter", rest)
  | .bind =>
    let (_, rest) ← (expectTok .lparen tail).toOption
    let (_, rest) ← (pExpr topFuel state rest).toOption
    let (_, rest) ← (expectTok .asKw rest).toOption
    let (_, rest) ← (expectTok .rparen (advTok rest)).toOption
    some ("bind", rest)
  | .values =>
    let (_, rest) ← (pValuesClause topFuel state tail).toOption
    some ("values", rest)
  | _ => none

private def scanAnchors (state : PState) (stops : Std.HashMap Nat Nat) :
    Nat → Token → TStream → List QuerySourceAnchor → List QuerySourceAnchor
  | 0, _, _, found | _, _, [], found => found.reverse
  | fuel + 1, previous, stream@(site :: tail), found =>
    if let some (kind, after) := clauseTail state site tail then
      let anchor := spanSince stops kind stream after
      -- Inline data has braces too, but its rows are not graph patterns.
      if site.tok == .values then scanAnchors state stops fuel .rbrace after (anchor :: found)
      else scanAnchors state stops fuel site.tok tail (anchor :: found)
    else
      let found := if [.lbrace, .rbrace, .rparen, .dot].contains previous && startsTriples site.tok then
        match pSubjectWithExtras topFuel state stream with
        | .ok (_, properties) =>
          let subject := consumed stops stream properties
          tripleProperties state stops subject fuel true properties found
        | .error _ => found
      else found
      scanAnchors state stops fuel site.tok tail found

/-- Source anchors for triples and explicit grouping clauses. The AST can
have implicit joins, moved filters, and other nodes with no single span. -/
def querySourceAnchors (state : PState) (tokens : List LocatedToken) (body : TStream) :
    List QuerySourceAnchor :=
  let stops := tokens.foldl (fun (positions : Std.HashMap Nat Nat) t => positions.insert t.start t.stop) {}
  scanAnchors state stops (body.length + 1) .eof body []

end L4Factoidal.SPARQL
