import Lean.Data.Json
import L4Factoidal.Wikidata.LabelService
import L4Factoidal.Wikidata.Legacy
import L4Factoidal.Wikidata.ArqFormat
import L4Factoidal.Wikidata.GeoDistance
import L4Factoidal.Wikidata.NamedSubquery

namespace L4Factoidal.Wikidata
open Lean L4Factoidal.SPARQL

structure RewriteStep where
  rule_id : String
  variant_id : String := "default"
  deriving ToJson

structure Diagnostic where
  code : String
  phase : String
  message : String
  offset : Option Nat := none
  deriving ToJson

structure RewriteResult where
  schema_version : Nat := 1
  rewrite_status : String
  rewritten_query : Option String := none
  rewrites : List RewriteStep := []
  warnings : List Diagnostic := []
  errors : List Diagnostic := []
  deriving ToJson

private def failure (status code phase message : String) (offset : Option Nat := none)
    (steps : List RewriteStep := []) : RewriteResult :=
  { rewrite_status := status, rewrites := steps, errors := [⟨code, phase, message, offset⟩] }

private structure ServiceSite where
  start : Nat
  endpoint : LocatedToken
  iri : String
  body : List LocatedToken

private def services (state : PState) (tokens : List LocatedToken) : List ServiceSite :=
  go tokens []
where
  go : List LocatedToken → List ServiceSite → List ServiceSite
  | [], acc => acc.reverse
  | site :: rest, acc =>
    if site.token != .service then go rest acc
    else
      let tail := match rest with
        | head :: remainder => if head.token == Token.silent then remainder else rest
        | [] => []
      match tail with
      | endpoint :: body =>
        match tokenIri state endpoint.token with
        | some iri => go rest (⟨site.start, endpoint, iri, body⟩ :: acc)
        | none => go rest acc
      | [] => go rest acc

private def bodyEnd : Nat → List LocatedToken → Option (Nat × List LocatedToken)
  | depth, token :: rest =>
    match token.token with
    | .lbrace => bodyEnd (depth + 1) rest
    | .rbrace => if depth == 1 then some (token.stop, rest) else bodyEnd (depth - 1) rest
    | _ => bodyEnd depth rest
  | _, [] => none

/-- Find the innermost subselect enclosing this service. Each stack entry
tracks a graph group, with tokens only for groups that start a subselect. -/
private def enclosingSelect (position : Nat) (stack : List (Option (List LocatedToken))) :
    List LocatedToken → Option (List LocatedToken)
  | [] => stack.findSome? id
  | token :: rest =>
    if token.start ≥ position then stack.findSome? id
    else match token.token with
    | .lbrace =>
      let select := if rest.head?.any (fun next => next.token == .select) then some rest else none
      enclosingSelect position (select :: stack) rest
    | .rbrace => enclosingSelect position (stack.drop 1) rest
    | _ => enclosingSelect position stack rest

private def outerRange (tokens : List LocatedToken) (site : ServiceSite) :
    Option (Nat × Nat × List LocatedToken) := do
  let before := tokens.takeWhile (fun token => token.start < site.start)
  let depth := before.foldl (fun n token =>
    if token.token == .lbrace then n + 1 else if token.token == .rbrace then n - 1 else n) 0
  if depth != 1 then none else
    let (stop, rest) ← bodyEnd 0 site.body
    match rest with
    | first :: tail =>
      if first.token == .dot then some (site.start, first.stop, tail)
      else some (site.start, stop, rest)
    | [] => none

private def laterBinders (state : PState) : Nat → TStream → List (Nat × List String) →
    Option (List (Nat × List String))
  | 0, _, _ => none
  | fuel + 1, tokens, acc => do
    let token := peekTok tokens
    if token == .rbrace then return acc.reverse
    let rest := advTok tokens
    let (bound, rest) ← if startsTriples token then do
      let (pattern, tail) ← (pTriplesBlock topFuel state (.empty, []) tokens).toOption
      pure (pattern.inScopeVars, tail)
    else match token with
      | .optional | .minusKw => do
        let (pattern, tail) ← (pGroupGraphPattern topFuel state rest).toOption
        pure (if token == .optional then pattern.inScopeVars else [], tail)
      | .lbrace => do
        let (pattern, tail) ← (pGroupOrUnion topFuel state tokens).toOption
        pure (pattern.inScopeVars, tail)
      | .filterKw => (pFilterExpr topFuel state rest).toOption.map (fun (_, tail) => ([], tail))
      | .values => (pValuesClause topFuel state rest).toOption.map (fun (p, tail) => (p.inScopeVars, tail))
      | .service | .graph => do
        let rest := if token == .service && peekTok rest == .silent then advTok rest else rest
        let (name, rest) ← (pGraphName topFuel state rest).toOption
        let (pattern, tail) ← (pGroupGraphPattern topFuel state rest).toOption
        let vars := match name with | .var name => name :: pattern.inScopeVars | _ => pattern.inScopeVars
        pure (if token == .graph then vars else [], tail)
      | .bind => do
        let (_, rest) ← (expectTok .lparen rest).toOption
        let (_, rest) ← (pExpr topFuel state rest).toOption
        let (_, rest) ← (expectTok .asKw rest).toOption
        let .var name := peekTok rest | none
        let (_, tail) ← (expectTok .rparen (advTok rest)).toOption
        pure ([name], tail)
      | _ => none
    let rest := if peekTok rest == .dot then advTok rest else rest
    laterBinders state fuel rest ((peekPos rest, bound) :: acc)

private def subgraphNamespace := "https://query.wikidata.org/subgraph/"

-- Wikimedia's WdsubgraphServiceRewriter, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/WdsubgraphServiceRewriter.java
private def subgraphEdit (site : ServiceSite) : Except Diagnostic (Option Edit) :=
  if !subgraphNamespace.isPrefixOf site.iri then .ok none
  else if site.iri == subgraphNamespace ++ "scholarly_articles" then
    .ok (some ⟨site.endpoint.start, site.endpoint.stop, "<https://query-scholarly-next.wikidata.org/sparql>"⟩)
  else .error ⟨"wdsubgraph_unknown_subgraph", "post-parse", site.iri, some site.endpoint.start⟩

-- Wikimedia's UnsupportedFeatureDetector, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/UnsupportedFeatureDetector.java
private def pendingFeature (iri : String) : Bool :=
  (iri != labelEndpoint && wikibaseNamespace.isPrefixOf iri) ||
  "http://www.bigdata.com/rdf#".isPrefixOf iri ||
  "http://www.bigdata.com/rdf/gas#".isPrefixOf iri ||
  "https://www.mediawiki.org/ontology#API/".isPrefixOf iri

private def pendingToken (state : PState) (tokens : List LocatedToken) : Option LocatedToken :=
  match tokens with
  | token :: rest =>
    let iri := (tokenIri state token.token).getD ""
    let isCall := (rest.head?.map (·.token)) == some .lparen
    if hintNamespace.isPrefixOf iri ||
        ("http://www.opengis.net/def/geosparql/function/".isPrefixOf iri &&
          !(iri == legacyGeofDistance && isCall)) || (isCall && pendingFeature iri) then some token
    else pendingToken state rest
  | [] => none

private def finish (original current : String) (steps : List RewriteStep) (parsedRule : Bool) : RewriteResult :=
  if steps.isEmpty then { rewrite_status := "unchanged", rewritten_query := some original }
  else
    let output := formatTextRewrite current
    match parseSparql output with
    | .ok _ =>
      let formatted := if parsedRule then formatParsedRewrite output else none
      let output := (formatted.filter fun text => (parseSparql text).isOk).getD output
      { rewrite_status := "rewritten", rewritten_query := some output
        rewrites := steps }
    | .error error =>
      failure "validation_failed" "rewritten_query_parse_error" "validate" error.msg (some error.pos) steps

/-- SPARQL 1.1 §18.2.1 forbids projecting into a name already in the
WHERE scope. The general Factoidal parser permits some grouped aliases;
the migration tool diagnoses them before emitting a replacement. -/
private def projectionAliasConflict (query : Query) : Option String :=
  match query.form with
  | .select (.vars items) => items.findSome? fun item => match item with
    | .expr _ name => if query.pattern.inScopeVars.contains name then some name else none
    | .var _ => none
  | _ => none

private def afterParse (original current language : String) (steps : List RewriteStep)
    (inputNames : List (String × String)) (query : Query) (namedBlock : Bool) :
    RewriteResult := Id.run do
  if let some name := projectionAliasConflict query then
    return failure "parse_error" "select_alias_already_in_scope" "parse"
      s!"SELECT expression reuses ?{name}, already in scope in WHERE" none steps
  if !query.dataset.isEmpty then
    return failure "skipped_unsupported" "unsupported_dataset_clause" "post-parse" "Top-level FROM or FROM NAMED" none steps
  let tokens := sourceTokens current
  let .ok (state, body) := sourceState tokens |
    return failure "parse_error" "original_query_parse_error" "parse" "Invalid prologue" none steps
  let bodyTokens := match body.head? with
    | some first => tokens.dropWhile (fun token => token.start < first.pos)
    | none => []
  if let some token := pendingToken state bodyTokens then
    return failure "skipped_unsupported" "unsupported_proprietary_feature" "post-parse"
      "This proprietary term or function needs another rewrite rule" (some token.start) steps
  let sites := services state bodyTokens
  if let some site := sites.find? (fun site => pendingFeature site.iri) then
    return failure "skipped_unsupported" "unsupported_proprietary_service" "post-parse" site.iri (some site.start) steps
  let subgraphs ← match sites.mapM subgraphEdit with
    | .ok edits => pure (edits.filterMap id)
    | .error error => return { rewrite_status := "skipped_unsupported", rewrites := steps, errors := [error] }
  let geoRule : RewriteStep := ⟨"rewrite-geof-distance", "default"⟩
  let (geoEdits, geoCount) ← match rewriteGeoDistance state body bodyTokens with
    | .ok plan => pure plan
    | .error pos => return (failure "blazegraph_error" "geof_distance_invalid_arity" "post-parse"
        "geof:distance() must be called with exactly 2 or 3 arguments." (some pos) (steps ++ [geoRule]))
  let labelSites := sites.filter (fun site => site.iri == labelEndpoint)
  -- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/NamedSubqueryLabelServiceRemover.java
  let (edits, postSteps) ← if namedBlock then do
    let removals ← labelSites.mapM fun site => do
      let some (stop, _) := bodyEnd 0 site.body |
        return (⟨site.start, site.start, ""⟩ : Edit)
      let before := (bodyTokens.takeWhile (fun token => token.start < site.start)).getLast?
      let after := (bodyTokens.dropWhile (fun token => token.start < stop)).head?
      let dot := (after.any fun token => startsTriples token.token) &&
        before.any (fun token => ![.lbrace, .rbrace, .rparen, .dot].contains token.token)
      return ⟨site.start, stop, if dot then "." else ""⟩
    pure (subgraphs ++ removals,
      List.replicate removals.length ⟨"rewrite-wikibase-label-service", "removed-in-subquery"⟩)
  else match labelSites with
    | [] => pure (subgraphs, [])
    | [site] =>
      let (scope, scopedTokens, names) ← match enclosingSelect site.start [] bodyTokens with
        | none => pure (query, bodyTokens, inputNames)
        | some subqueryTokens =>
          let stream := subqueryTokens.map fun token => (⟨token.token, token.start⟩ : PosToken)
          match pSelectQuery topFuel state state.base stream with
          | .ok (subquery, _) => pure (subquery, subqueryTokens, [])
          | .error error =>
            return (failure "parse_error" "original_query_parse_error" "parse"
              error.msg (some error.pos) steps)
      let some (start, stop, rest) := outerRange scopedTokens site |
        return failure "skipped_unsupported" "label_scope_not_supported" "post-parse" "Label service must be directly in a query WHERE group" (some site.start) steps
      let used := tokens.filterMap fun token => match token.token with
        | .var name => some name
        | _ => none
      let binders := (laterBinders state (rest.length + 1)
        (rest.map fun token => ⟨token.token, token.start⟩) []).getD []
      match rewriteOuterLabel scope language used (binders.flatMap Prod.snd) names with
      | .ok (text, variant, entities) =>
        let target := binders.foldl (fun position (next, bound) =>
          if bound.any entities.contains then next else position) stop
        let labelEdits := if target == stop then [⟨start, stop, text⟩] else
          -- A triples block directly followed by SERVICE needs a dot if the
          -- next element after removing SERVICE is also a triples block.
          let before := (scopedTokens.takeWhile (fun token => token.start < start)).getLast?.map (·.token)
          let needsDot := (rest.head?.map (·.token)).any startsTriples &&
            (before.any fun token => ![.lbrace, .rbrace, .rparen, .dot].contains token)
          [⟨start, stop, if needsDot then ".\n" else ""⟩, ⟨target, target, "\n" ++ text⟩]
        pure (subgraphs ++ labelEdits, [⟨"rewrite-wikibase-label-service", variant⟩])
      | .error message => return failure "skipped_unsupported" "label_scope_not_supported" "post-parse" message (some site.start) steps
    | _ => return (failure "skipped_unsupported" "label_scope_not_supported" "post-parse"
        "Multiple label services require scope analysis" none steps)
  let steps := if subgraphs.isEmpty then steps else steps ++ [⟨"rewrite-wdsubgraph-service", "default"⟩]
  let edits := edits ++ geoEdits
  let result := finish original (applyEdits current (edits.mergeSort (fun a b => a.start ≤ b.start)))
    (steps ++ List.replicate geoCount geoRule ++ postSteps) (!edits.isEmpty)
  let warnings := if !namedBlock then [] else labelSites.map fun _ =>
    (⟨"named_subquery_label_service_removed", "post-ARQ",
      "SERVICE wikibase:label is not supported inside a named subquery and was removed; any *Label variable it would have bound is now permanently unbound in this block.", none⟩ : Diagnostic)
  return { result with warnings := result.warnings ++ warnings }

private def parseAndRewrite (original current language : String) (steps : List RewriteStep)
    (namedBlock : Bool) :
    RewriteResult := Id.run do
  let parsed := parseQuerySyntax current
  match parsed with
  | .ok query =>
    if (projectionAliasConflict query).isNone then
      return afterParse original current language steps [] query namedBlock
  | .error error =>
    if error.msg != "SELECT expression aliases variable already in scope" then
      return failure "parse_error" "original_query_parse_error" "parse" error.msg (some error.pos) steps
  let tokens := sourceTokens current
  let .ok (state, body) := sourceState tokens |
    return failure "parse_error" "original_query_parse_error" "parse" "Invalid prologue" none steps
  let (edits, names) ← match repairProjectionAliases state body tokens with
    | .ok ([], _) => return (failure "parse_error" "select_alias_already_in_scope" "legacy-input"
        "Alias repair needs an outer SELECT with a distinct input binding" none steps)
    | .ok repair => pure repair
    | .error message => return failure "parse_error" "select_alias_already_in_scope" "legacy-input" message none steps
  let repaired := applyEdits current edits
  let steps := steps ++ [⟨"rewrite-legacy-select-alias", "rename-input"⟩]
  return match parseQuerySyntax repaired with
  | .ok query => afterParse original repaired language steps names query namedBlock
  | .error error => failure "parse_error" "legacy_alias_repair_parse_error" "legacy-input"
      error.msg (some error.pos) steps

-- Wikimedia's SparqlRewriteEngine, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteEngine.java
private def unextractedDefinition : List LocatedToken → Bool
  | first :: second :: rest =>
    (first.token == .withKw && second.token == .lbrace) ||
      unextractedDefinition (second :: rest)
  | _ => false

private def rewriteBody (text language : String) (namedBlock : Bool) : RewriteResult := Id.run do
  let tokens := sourceTokens text
  if unextractedDefinition tokens then
    return failure "skipped_unsupported" "unsupported_proprietary_feature" "pre-ARQ"
      "The query uses an unimplemented named subquery."
  let .ok (state, _) := sourceState tokens | return parseAndRewrite text text language [] namedBlock
  let hints := rewriteHints text state tokens
  let current := applyEdits text hints
  let steps := if hints.isEmpty then [] else [⟨"rewrite-query-hint", "default"⟩]
  let tokens := if hints.isEmpty then tokens else sourceTokens current
  let edits ← match rewriteSomeValue state tokens with
    | .ok edits => pure edits
    | .error pos => return (failure "blazegraph_error" "wikibase_is_some_value_missing_argument"
        "pre-parse" "wikibase:isSomeValue needs an argument" (some pos)
        (steps ++ [⟨"rewrite-wikibase-isSomeValue", "default"⟩]))
  let steps := if edits.isEmpty then steps else steps ++ [⟨"rewrite-wikibase-isSomeValue", "default"⟩]
  return parseAndRewrite text (applyEdits current edits) language steps namedBlock

private def namedStep : RewriteStep := ⟨"rewrite-named-subquery", "default"⟩

private def namedFailure (problem : NamedSubquery.Problem) (phase : String)
    (steps : List RewriteStep := []) : RewriteResult :=
  failure problem.status problem.code phase problem.message none steps

private def rewriteNamed (body language : String) (plan : NamedSubquery.Plan) : RewriteResult := Id.run do
  let prologue := String.join ((NamedSubquery.prefixes body).eraseDups.map (· ++ "\n"))
  let mut blocks : List NamedSubquery.PreparedBlock := []
  let mut steps : List RewriteStep := [namedStep]
  let mut warnings : List Diagnostic := []
  for block in plan.blocks do
    let substituted := prologue ++ NamedSubquery.substitute block.body block.references blocks
    let result := rewriteBody substituted language true
    let some output := result.rewritten_query | return result
    let .ok query := parseQuerySyntax substituted |
      return failure "parse_error" "original_query_parse_error" "parse" "Invalid named subquery"
    match NamedSubquery.prepareBlock block.name query output blocks with
    | .error problem => return namedFailure problem "post-ARQ" (steps ++ result.rewrites)
    | .ok prepared => blocks := blocks ++ [prepared]
    steps := steps ++ result.rewrites
    warnings := warnings ++ result.warnings
  let removals := plan.blocks.map fun block => (⟨block.start, block.stop, ""⟩ : Edit)
  let result := rewriteBody (NamedSubquery.substitute body plan.references blocks removals) language false
  steps := steps ++ result.rewrites
  warnings := warnings ++ result.warnings
  let some rewritten := result.rewritten_query | return { result with rewrites := steps, warnings := warnings }
  match NamedSubquery.assemble rewritten blocks with
  | .error problem => return { namedFailure problem "post-ARQ" steps with warnings := warnings }
  | .ok text =>
    return { rewrite_status := "rewritten", rewritten_query := some text, rewrites := steps, warnings := warnings }

/-- Run the rewrite pipeline without executing the query. SPARQL fragments
are validated before assembling QLever's WITH and INCLUDE clauses. -/
def rewriteQuery (text : String) (language : String := "") : RewriteResult := Id.run do
  if text.utf8ByteSize > 1000000 then
    return failure "skipped_unsupported" "query_exceeds_length_limit" "input" "Query exceeds 1 MB"
  let (leading, body) := splitLeadingComments text
  let plan := if body.contains '%' then NamedSubquery.plan body (sourceTokens body true) else .ok none
  match plan with
  | .error problem => return namedFailure problem "pre-ARQ" [namedStep]
  | .ok none =>
    let result := rewriteBody text language false
    return if result.rewrite_status == "rewritten" then
      { result with rewritten_query := result.rewritten_query.map (appendOriginalQuery · text) }
      else result
  | .ok (some plan) =>
    let result := rewriteNamed body language plan
    return { result with rewritten_query :=
      result.rewritten_query.map (fun output => appendOriginalQuery (leading ++ output) text) }

end L4Factoidal.Wikidata
