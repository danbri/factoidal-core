import Lean.Data.Json
import L4Factoidal.Wikidata.LabelService

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

private def afterLabelVars : Nat → List LocatedToken → List String
  | depth, token :: rest =>
    match token.token with
    | .rbrace => if depth == 0 then [] else afterLabelVars (depth - 1) rest
    | .lbrace => afterLabelVars (depth + 1) rest
    | .var name => name :: afterLabelVars depth rest
    | _ => afterLabelVars depth rest
  | _, [] => []

private def outerRange (tokens : List LocatedToken) (site : ServiceSite) :
    Option (Nat × Nat × List String) := do
  let before := tokens.takeWhile (fun token => token.start < site.start)
  let depth := before.foldl (fun n token =>
    if token.token == .lbrace then n + 1 else if token.token == .rbrace then n - 1 else n) 0
  if depth != 1 then none else
    let (stop, rest) ← bodyEnd 0 site.body
    match rest with
    | first :: tail =>
      if first.token == .dot then some (site.start, first.stop, afterLabelVars 0 tail)
      else some (site.start, stop, afterLabelVars 0 rest)
    | [] => none

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
    if hintNamespace.isPrefixOf iri ||
        "http://www.opengis.net/def/geosparql/function/".isPrefixOf iri ||
        ((rest.head?.map (·.token)) == some .lparen && pendingFeature iri) then some token
    else pendingToken state rest
  | [] => none

private def finish (original current : String) (steps : List RewriteStep) : RewriteResult :=
  if steps.isEmpty then { rewrite_status := "unchanged", rewritten_query := some original }
  else
    let output := standalone current
    match parseSparql output with
    | .ok _ =>
      let comment := String.intercalate "\n" (((original.replace "\r\n" "\n").replace "\r" "\n").splitOn "\n" |>.map ("# " ++ ·))
      { rewrite_status := "rewritten", rewritten_query := some (output ++ "\n\n# Original query:\n" ++ comment)
        rewrites := steps }
    | .error error =>
      failure "validation_failed" "rewritten_query_parse_error" "validate" error.msg (some error.pos) steps

private def afterParse (original current language : String) (steps : List RewriteStep) :
    RewriteResult := Id.run do
  let query ← match parseQuery current with
    | .ok query => pure query
    | .error error => return failure "parse_error" "original_query_parse_error" "parse" error.msg (some error.pos) steps
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
  let labelSites := sites.filter (fun site => site.iri == labelEndpoint)
  let (edits, postSteps) ← match labelSites with
    | [] => pure (subgraphs, [])
    | [site] =>
      let some (start, stop, later) := outerRange bodyTokens site |
        return failure "skipped_unsupported" "label_scope_not_supported" "post-parse" "Label service must be in the outer WHERE group" (some site.start) steps
      let used := tokens.filterMap fun token => match token.token with
        | .var name => some name
        | _ => none
      match rewriteOuterLabel query language used later with
      | .ok (text, variant) => pure (subgraphs ++ [⟨start, stop, text⟩],
          [⟨"rewrite-wikibase-label-service", variant⟩])
      | .error message => return failure "skipped_unsupported" "label_scope_not_supported" "post-parse" message (some site.start) steps
    | _ => return (failure "skipped_unsupported" "label_scope_not_supported" "post-parse"
        "Multiple label services require scope analysis" none steps)
  let steps := if subgraphs.isEmpty then steps else steps ++ [⟨"rewrite-wdsubgraph-service", "default"⟩]
  return finish original (applyEdits current (edits.mergeSort (fun a b => a.start ≤ b.start))) (steps ++ postSteps)

-- Wikimedia's SparqlRewriteEngine, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteEngine.java
/-- Run pre-parse rules, parse with WDQS defaults, apply post-parse rules, and
validate rewritten SPARQL with the standard parser. No query is executed. -/
def rewriteQuery (text : String) (language : String := "") : RewriteResult := Id.run do
  if text.utf8ByteSize > 1000000 then
    return failure "skipped_unsupported" "query_exceeds_length_limit" "input" "Query exceeds 1 MB"
  let tokens := sourceTokens text
  let .ok (state, _) := sourceState tokens | return afterParse text text language []
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
  return afterParse text (applyEdits current edits) language steps

end L4Factoidal.Wikidata
