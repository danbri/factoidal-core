import Lean.Data.Json
import L4Factoidal.Wikidata.LabelService
import L4Factoidal.Wikidata.Legacy
import L4Factoidal.Wikidata.ArqFormat
import L4Factoidal.Wikidata.GeoDistance

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

private def services (state : PState) : List LocatedToken → List ServiceSite
  | site :: rest =>
    let tail : List LocatedToken := match rest with
      | head :: remainder => if head.token == Token.silent then remainder else rest
      | [] => []
    let remaining := services state rest
    if site.token != .service then remaining
    else match tail with
    | endpoint :: body =>
      match tokenIri state endpoint.token with
      | some iri => ⟨site.start, endpoint, iri, body⟩ :: remaining
      | none => remaining
    | [] => remaining
  | [] => []

private def bodyEnd : Nat → List LocatedToken → Option (Nat × List LocatedToken)
  | depth, token :: rest =>
    match token.token with
    | .lbrace => bodyEnd (depth + 1) rest
    | .rbrace => if depth == 1 then some (token.stop, rest) else bodyEnd (depth - 1) rest
    | _ => bodyEnd depth rest
  | _, [] => none

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
      { rewrite_status := "rewritten", rewritten_query := some (appendOriginalQuery output original)
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
    (inputNames : List (String × String)) (query : Query) :
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
  let (edits, postSteps) ← match labelSites with
    | [] => pure (subgraphs, [])
    | [site] =>
      let some (start, stop, rest) := outerRange bodyTokens site |
        return failure "skipped_unsupported" "label_scope_not_supported" "post-parse" "Label service must be in the outer WHERE group" (some site.start) steps
      let used := tokens.filterMap fun token => match token.token with
        | .var name => some name
        | _ => none
      let binders := (laterBinders state (rest.length + 1)
        (rest.map fun token => ⟨token.token, token.start⟩) []).getD []
      match rewriteOuterLabel query language used (binders.flatMap Prod.snd) inputNames with
      | .ok (text, variant, entities) =>
        let target := binders.foldl (fun position (next, bound) =>
          if bound.any entities.contains then next else position) stop
        let labelEdits := if target == stop then [⟨start, stop, text⟩] else
          -- A triples block directly followed by SERVICE needs a dot if the
          -- next element after removing SERVICE is also a triples block.
          let before := (bodyTokens.takeWhile (fun token => token.start < start)).getLast?.map (·.token)
          let needsDot := (rest.head?.map (·.token)).any startsTriples &&
            (before.any fun token => ![.lbrace, .rbrace, .rparen, .dot].contains token)
          [⟨start, stop, if needsDot then ".\n" else ""⟩, ⟨target, target, "\n" ++ text⟩]
        pure (subgraphs ++ labelEdits, [⟨"rewrite-wikibase-label-service", variant⟩])
      | .error message => return failure "skipped_unsupported" "label_scope_not_supported" "post-parse" message (some site.start) steps
    | _ => return (failure "skipped_unsupported" "label_scope_not_supported" "post-parse"
        "Multiple label services require scope analysis" none steps)
  let steps := if subgraphs.isEmpty then steps else steps ++ [⟨"rewrite-wdsubgraph-service", "default"⟩]
  let edits := edits ++ geoEdits
  return finish original (applyEdits current (edits.mergeSort (fun a b => a.start ≤ b.start)))
    (steps ++ List.replicate geoCount geoRule ++ postSteps) (!edits.isEmpty)

private def parseAndRewrite (original current language : String) (steps : List RewriteStep) :
    RewriteResult := Id.run do
  let parsed := parseQuerySyntax current
  match parsed with
  | .ok query =>
    if (projectionAliasConflict query).isNone then
      return afterParse original current language steps [] query
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
  | .ok query => afterParse original repaired language steps names query
  | .error error => failure "parse_error" "legacy_alias_repair_parse_error" "legacy-input"
      error.msg (some error.pos) steps

-- Wikimedia's SparqlRewriteEngine, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteEngine.java
/-- Run pre-parse rules, parse with WDQS defaults, apply post-parse rules, and
validate rewritten SPARQL with the standard parser. No query is executed. -/
def rewriteQuery (text : String) (language : String := "") : RewriteResult := Id.run do
  if text.utf8ByteSize > 1000000 then
    return failure "skipped_unsupported" "query_exceeds_length_limit" "input" "Query exceeds 1 MB"
  let tokens := sourceTokens text
  let .ok (state, _) := sourceState tokens | return parseAndRewrite text text language []
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
  return parseAndRewrite text (applyEdits current edits) language steps

end L4Factoidal.Wikidata
