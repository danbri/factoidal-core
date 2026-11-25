import L4Factoidal.Wikidata.Source

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL

private def variableName (token : LocatedToken) : Option String :=
  match token.token with
  | .var name => some name
  | _ => none

private def freshInput (used : Std.HashSet String) (name : String) : String :=
  let stem := name ++ "__wdqs_input"
  if !used.contains stem then stem else
    ((List.range (used.size + 1)).findSome? fun n =>
    let candidate := s!"{stem}_{n + 1}"
    if used.contains candidate then none else some candidate).getD stem

private def variableEdit (names : List (String × String)) (token : LocatedToken) : Option Edit := do
  let name ← variableName token
  let replacement ← names.lookup name
  return ⟨token.start, token.stop, "?" ++ replacement⟩

private def aggregateToken : Token → Bool
  | .count | .sum | .minKw | .maxKw | .avg | .groupConcat | .sample => true
  | _ => false

/-- The projection parser identifies the whole SELECT list. Within that list
a closing AS names the public column, and earlier public names are visible
in later scalar expressions. Aggregate arguments still read the input rows. -/
private def projectionEdits (names : List (String × String)) :
    Nat → Option Nat → Token → List (String × String) → List LocatedToken → List Edit → List Edit
  | depth, aggregate, previous, scalar, asToken :: target :: close :: rest, edits =>
    if depth == 1 && asToken.token == .asKw && close.token == .rparen then
      let scalar := scalar.filter fun pair => variableName target != some pair.1
      projectionEdits names 0 none .rparen scalar rest edits
    else
      let next := if asToken.token == .lparen then depth + 1
        else if asToken.token == .rparen then depth - 1 else depth
      let scopes := if aggregate.isSome then names else scalar
      let edits := (if depth == 0 then none else variableEdit scopes asToken).elim edits (· :: edits)
      let aggregate := if asToken.token == .lparen && aggregateToken previous then some next
        else if asToken.token == .rparen && aggregate == some depth then none else aggregate
      projectionEdits names next aggregate asToken.token scalar (target :: close :: rest) edits
  | _, _, _, _, _, edits => edits.reverse

private def affectedSubquery (names : List String) (depth : Nat)
    (subquery : Option Nat) (tokens : List LocatedToken) : Bool :=
  match tokens with
  | [] => false
  | token :: rest =>
    if subquery.isSome && (variableName token).any names.contains then true
    else match token.token with
    | .lbrace => affectedSubquery names (depth + 1) subquery rest
    | .rbrace =>
      affectedSubquery names (depth - 1) (if subquery == some depth then none else subquery) rest
    | .select => affectedSubquery names depth (subquery.or (some depth)) rest
    | _ => affectedSubquery names depth subquery rest

/-- Recover outer SELECT aliases by alpha-renaming their input bindings.
Reuse the real projection, WHERE and modifier parsers without asking the
SELECT-level validation to accept a legacy binding. Edits target lexer
ranges, so comments, IRIs and literals are never variable references.

A subquery that uses an affected name needs its own binding analysis.
ORDER BY outside aggregate arguments continues to use the public alias. -/
def repairProjectionAliases (state : PState) (body : TStream)
    (tokens : List LocatedToken) : Except String (List Edit × List (String × String)) := do
  unless peekTok body == .select do return ([], [])
  let rest := advTok body
  let rest := if peekTok rest == .distinct || peekTok rest == .reduced then advTok rest else rest
  let fuel := tokens.length + 1
  let (selection, afterSelection) ← (pSelectVars fuel state rest).mapError (·.msg)
  let .vars items := selection | return ([], [])
  let (_, whereClause) ← (pDatasetClauses fuel state afterSelection).mapError (·.msg)
  let whereStart := if peekTok whereClause == .whereKw then advTok whereClause else whereClause
  let (pattern, afterWhere) ← (pGroupGraphPattern fuel state whereStart).mapError (·.msg)
  let (modifiers, afterModifiers) ← (pSolutionModifier fuel state afterWhere).mapError (·.msg)
  let inputVars := pattern.inScopeVars ++ groupNamedVars (modifiers.2.1.getD []) ++
    (if peekTok afterModifiers == .values then
      (tokens.dropWhile (fun token => token.start < peekPos afterModifiers)).filterMap variableName
    else [])
  let aliases := items.filterMap fun item => match item with
    | .expr _ name => if inputVars.contains name then some name else none
    | .var _ => none
  if aliases.isEmpty then return ([], [])
  let projection := (tokens.dropWhile (fun token => token.start < peekPos rest)).takeWhile
    (fun token => token.start < peekPos afterSelection)
  let graph := (tokens.dropWhile (fun token => token.start < peekPos whereStart)).takeWhile
    (fun token => afterWhere.isEmpty || token.start < peekPos afterWhere)
  let suffix := if afterWhere.isEmpty then [] else tokens.dropWhile (fun t => t.start < peekPos afterWhere)
  let grouping := suffix.takeWhile (fun token => ![.order, .limit, .offset, .values].contains token.token)
  let ordering := (suffix.dropWhile (fun token => token.token != .order)).takeWhile
    (fun token => ![.limit, .offset, .values].contains token.token)
  let values := suffix.dropWhile (fun token => token.token != .values)
  if affectedSubquery aliases 0 none graph ||
      projection.any (fun token => token.token == .exists) ||
      grouping.any (fun token => token.token == .exists) then
    throw "Legacy SELECT alias crosses a nested query or EXISTS scope"
  if (ordering.any fun token => (variableName token).any aliases.contains) &&
      ordering.any (fun token => aggregateToken token.token || token.token == .exists) then
    throw "Legacy SELECT alias has an ambiguous reference in ORDER BY"
  let used := (tokens.filterMap variableName).foldl Std.HashSet.insert (∅ : Std.HashSet String)
  let (names, _) := aliases.foldl (fun (names, used) name =>
    let fresh := freshInput used name
    ((name, fresh) :: names, used.insert fresh)) ([], used)
  return (projectionEdits names 0 none .eof names projection [] ++
    (graph ++ grouping ++ values).filterMap (variableEdit names), names)

end L4Factoidal.Wikidata
