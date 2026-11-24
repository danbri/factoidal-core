import L4Factoidal.Wikidata.Output

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL

/-! Extract Blazegraph named subqueries before SPARQL parsing, then hoist their
rewritten bodies and restore references in QLever syntax. The temporary VALUES
clauses expose the same variables to the ordinary rewrite pipeline.
-/

-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/NamedSubqueryOrchestrator.java
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/NamedSubqueryRewriter.java

namespace NamedSubquery

structure Problem where
  status : String
  code : String
  message : String

structure Reference where
  name : String
  start : Nat
  stop : Nat

structure Block where
  name : String
  body : String
  start : Nat
  stop : Nat
  references : List Reference

structure Plan where
  blocks : List Block
  references : List Reference

structure PreparedBlock where
  name : String
  vars : List String
  pattern : String
  modifiers : String
  prefixes : List String

private def slice (chars : Array Char) (start stop : Nat) : String :=
  String.ofList (chars.extract start stop).toList

private def readName (token : LocatedToken) : Option (String × Nat) :=
  match token.token with
  | .invalid name =>
    if name.length > 1 && name.startsWith "%" then some ((name.drop 1).toString, token.stop)
    else none
  | _ => none

private def references (chars : Array Char) (tokens : List LocatedToken) : List Reference :=
  let found := tokens.zip (tokens.drop 1)
  found.filterMap fun (word, percent) => do
    if (slice chars word.start word.stop).toUpper != "INCLUDE" then none else
      let (name, stop) ← readName percent
      some ⟨name, word.start, stop⟩

private def closeGroup (depth : Nat) : List LocatedToken → Option (LocatedToken × List LocatedToken)
  | [] => none
  | token :: rest =>
    match token.token with
    | .lbrace => closeGroup (depth + 1) rest
    | .rbrace => if depth == 0 then some (token, rest) else closeGroup (depth - 1) rest
    | _ => closeGroup depth rest

private def findBlocks (chars : Array Char) (qlever : Bool) : Nat → List LocatedToken →
    List Block → List Block
  | 0, _, blocks | _, [], blocks => blocks.reverse
  | fuel + 1, word :: rest, blocks =>
    let found : Option (Block × List LocatedToken) := do
      if word.token != .withKw then none else
        let (name, body, stop, tail) ← if qlever then do
          let nameToken :: asWord :: openBrace :: body := rest | none
          guard (asWord.token == .asKw && openBrace.token == .lbrace)
          let (name, _) ← readName nameToken
          let (closeBrace, tail) ← closeGroup 0 body
          let body := slice chars openBrace.start closeBrace.stop
          some (name, "SELECT * WHERE " ++ body, closeBrace.stop, tail)
        else do
          let openBrace :: body := rest | none
          guard (openBrace.token == .lbrace)
          let (closeBrace, after) ← closeGroup 0 body
          let asWord :: nameToken :: tail := after | none
          guard (asWord.token == .asKw)
          let (name, stop) ← readName nameToken
          some (name, (slice chars openBrace.stop closeBrace.start).trimAscii.toString, stop, tail)
        some (⟨name, body, word.start, stop, references body.toList.toArray (sourceTokens body true)⟩, tail)
    match found with
    | some (block, tail) => findBlocks chars qlever fuel tail (block :: blocks)
    | none => findBlocks chars qlever fuel rest blocks

private def wildcard (text : String) : Bool :=
  match (sourceTokens text).map LocatedToken.token with
  | .select :: .star :: _
  | .select :: .distinct :: .star :: _
  | .select :: .reduced :: .star :: _ => true
  | _ => false

private def orderBlocks (done : List Block) : Nat → List Block → Except Problem (List Block)
  | _, [] => .ok done.reverse
  | 0, remaining =>
    let names := String.intercalate ", " (remaining.map fun block => "%" ++ block.name)
    .error ⟨"blazegraph_error", "named_subquery_cyclic_reference",
      s!"The named subqueries {names} form an INCLUDE dependency cycle."⟩
  | fuel + 1, remaining =>
    match remaining.find? (fun block => block.references.all fun ref => done.any (·.name == ref.name)) with
    | none => orderBlocks done 0 remaining
    | some next => orderBlocks (next :: done) fuel (remaining.filter (·.name != next.name))

def plan (text : String) (tokens : List LocatedToken) (qlever := false) (inspect := false) :
    Except Problem (Option Plan) := do
  let chars := text.toList.toArray
  let blocks := findBlocks chars qlever tokens.length tokens []
  let outer := (references chars tokens).filter fun ref =>
    !blocks.any (fun block => block.start ≤ ref.start && ref.start < block.stop)
  if blocks.isEmpty && outer.isEmpty then return none
  let mut seen : List String := []
  for block in blocks do
    if seen.contains block.name then
      throw ⟨"ambiguous_conflicting", "named_subquery_duplicate_definition",
        s!"The named subquery %{block.name} is defined more than once."⟩
    seen := block.name :: seen
  let all := outer ++ blocks.flatMap (·.references)
  for ref in all do
    if !seen.contains ref.name then
      throw ⟨"blazegraph_error", "named_subquery_undefined_reference",
        s!"INCLUDE %{ref.name} refers to a named subquery this query never defines."⟩
  unless inspect do
    for ref in all do
      if blocks.any (fun block => block.name == ref.name && wildcard block.body) then
        throw ⟨"skipped_unsupported", "named_subquery_select_star_included",
          s!"The named subquery %{ref.name} uses SELECT * and cannot be safely referenced by INCLUDE; declare its projected variables explicitly."⟩
  let blocks ← orderBlocks [] blocks.length (blocks.mergeSort (fun a b => a.name ≤ b.name))
  return some ⟨blocks, outer⟩

private def placeholderPrefix := "__include_"

private def variables (names : List String) : String :=
  String.join (names.map fun name => " ?" ++ name)

def substitute (text : String) (refs : List Reference) (blocks : List PreparedBlock)
    (extra : List Edit := []) (markerPrefix : String := placeholderPrefix) : String :=
  let edits := refs.map fun ref =>
    let vars := ((blocks.find? (·.name == ref.name)).map (·.vars)).getD []
    let columns := variables vars
    let undefs := String.join (vars.map fun _ => " UNDEF")
    (⟨ref.start, ref.stop, s!"VALUES (?{markerPrefix}{ref.name}{columns}) \{ (UNDEF{undefs}) }"⟩ : Edit)
  applyEdits text ((edits ++ extra).mergeSort (fun a b => a.start ≤ b.start))

private def prefixLine (line : String) : Bool :=
  match (sourceTokens line).head?.map LocatedToken.token with
  | some .prefixKw | some .baseKw => true
  | _ => false

private def leadingLines (text : String) : List String :=
  (text.splitOn "\n").takeWhile (fun line => line.trimAscii.isEmpty || prefixLine line)

def prefixes (text : String) : List String :=
  (leadingLines text).filter prefixLine |>.map (fun line => (line.dropEndWhile (· == '\r')).toString)

private def possiblePlaceholder : List LocatedToken → Option String
  | ⟨.lparen, _, _⟩ :: ⟨.var name, _, _⟩ :: _ =>
    if placeholderPrefix.isPrefixOf name then some name else none
  | _ => none
private def restoreEdits (chars : Array Char) (blocks : List PreparedBlock) :
    List LocatedToken → List Edit → Except Problem (List Edit)
  | [], edits => .ok edits.reverse
  | keyword :: tail, edits =>
    if keyword.token != .values then restoreEdits chars blocks tail edits else do
      let some varName := possiblePlaceholder tail | restoreEdits chars blocks tail edits
      let _ :: body := tail.dropWhile (·.token != .lbrace) | restoreEdits chars blocks tail edits
      let some (closeBrace, rest) := closeGroup 0 body | restoreEdits chars blocks tail edits
      let name := (varName.drop placeholderPrefix.length).toString
      let some block := blocks.find? (·.name == name) |
        throw ⟨"validation_failed", "named_subquery_unresolved_include_placeholder",
          s!"Internal placeholder variable ?{varName} could not be resolved."⟩
      let nextToken := (rest.head?.map (·.start)).getD chars.size
      let gap := (chars.extract closeBrace.stop nextToken).toList.takeWhile Char.isWhitespace
      let afterSpace := closeBrace.stop + gap.length
      let stop := if let some dot := rest.head? then
        if dot.token == .dot && afterSpace == dot.start then dot.stop else afterSpace
        else afterSpace
      let modifiers := if block.modifiers.isEmpty then "" else " " ++ block.modifiers
      let ending := if chars[stop]? == some '\n' then "" else "\n"
      let edit : Edit := ⟨keyword.start, stop,
        s!"\{ SELECT{variables block.vars} WHERE \{ INCLUDE %{name} }{modifiers} }{ending}"⟩
      restoreEdits chars blocks tail (edit :: edits)

private def restore (text : String) (blocks : List PreparedBlock) : Except Problem String :=
  (restoreEdits text.toList.toArray blocks (sourceTokens text) []).map (applyEdits text)

/-- Projected variables reachable when the query is included. An authored
projection can mention a variable that its group never puts in scope. -/
def includedVariables (query : Query) : List String :=
  let aliases := match query.form with
    | .select (.vars items) => items.filterMap fun item => match item with
      | .expr _ name => some name
      | .var _ => none
    | _ => []
  let reachable := aliases ++ query.pattern.inScopeVars
  query.projectedVars.filter (reachable.contains ·)

def prepareBlock (name : String) (query : Query) (rewritten : String)
    (blocks : List PreparedBlock) : Except Problem PreparedBlock := do
  let .select select := query.form |
    throw ⟨"parse_error", "original_query_parse_error", "Named subquery must be a SELECT query."⟩
  let vars := includedVariables query
  let extra := prefixes (standalone rewritten)
  let restored ← restore rewritten blocks
  let stripped := (String.intercalate "\n" ((restored.splitOn "\n").drop (leadingLines restored).length)).trimAscii.toString
  if selectHasAggregates select then
    return ⟨name, vars, "{\n{ " ++ stripped ++ " }\n}", "", extra⟩
  let tokens := (sourceTokens stripped true).dropWhile (·.token != .lbrace)
  let openBrace :: tail := tokens |
    throw ⟨"validation_failed", "named_subquery_assembly_unbalanced_braces", "Missing named subquery graph pattern."⟩
  let some (closeBrace, _) := closeGroup 0 tail |
    throw ⟨"validation_failed", "named_subquery_assembly_unbalanced_braces", "Unclosed named subquery graph pattern."⟩
  let chars := stripped.toList.toArray
  let body := (slice chars openBrace.stop closeBrace.start).trimAscii.toString
  let modifiers := (slice chars closeBrace.stop chars.size).trimAscii.toString
  return ⟨name, vars, "{\n" ++ body ++ "\n}", modifiers, extra⟩

private def prefixKey (line : String) : List Token :=
  (sourceTokens line).map (·.token)

private def balanced : Nat → List LocatedToken → Bool
  | depth, [] => depth == 0
  | depth, token :: rest =>
    match token.token with
    | .lbrace => balanced (depth + 1) rest
    | .rbrace => depth != 0 && balanced (depth - 1) rest
    | _ => balanced depth rest

def assemble (rewritten : String) (blocks : List PreparedBlock) : Except Problem String := do
  let restored ← restore rewritten blocks
  let some select := (sourceTokens restored true).find? (·.token == .select) |
    throw ⟨"validation_failed", "named_subquery_missing_select", "No SELECT keyword for WITH clauses."⟩
  let existing := (prefixes restored).map prefixKey
  let missing := (blocks.flatMap (·.prefixes)).eraseDups.filter fun line =>
    !existing.contains (prefixKey line)
  let withs := String.join (blocks.map fun block => s!"WITH %{block.name} AS {block.pattern}\n")
  let text := String.join (missing.map (· ++ "\n")) ++
    applyEdits restored [⟨select.start, select.start, withs⟩]
  if !balanced 0 (sourceTokens text true) then
    throw ⟨"validation_failed", "named_subquery_assembly_unbalanced_braces", "Unbalanced named subquery braces."⟩
  return text

end NamedSubquery
end L4Factoidal.Wikidata
