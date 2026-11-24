import L4Factoidal.Wikidata.PreParse
import L4Factoidal.Wikidata.Language
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL L4Factoidal.RDF

def labelEndpoint : String := wikibaseNamespace ++ "label"

private def labelIri := "http://www.w3.org/2000/01/rdf-schema#label"
private def descriptionIri := "http://schema.org/description"
private def aliasIri := "http://www.w3.org/2004/02/skos/core#altLabel"
private def languageIri := wikibaseNamespace ++ "language"
private def paramIri := "http://www.bigdata.com/rdf#serviceParam"

-- Binding analysis counterpart:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/BindingAnalysis.java
-- This conservative subset describes variables guaranteed by incoming patterns.
private def definitelyBound : QueryPattern → List String
  | .bgp triples => (QueryPattern.bgp triples).inScopeVars
  | .propertyPath s path o => (QueryPattern.propertyPath s path o).inScopeVars
  | .join left right => definitelyBound left ++ definitelyBound right
  | .union left right => (definitelyBound left).filter (definitelyBound right).contains
  | .minus left _ | .leftJoin left _ _ | .filter _ left | .bind _ _ left =>
    definitelyBound left
  | _ => []

private def outerLabel : QueryPattern → Option (QueryPattern × QueryPattern)
  | .filter _ pattern | .bind _ _ pattern => outerLabel pattern
  | .leftJoin incoming _ _ | .minus incoming _ => outerLabel incoming
  | .join incoming (.service endpoint false body) =>
    if endpoint.val == labelEndpoint then some (incoming, body) else outerLabel incoming
  | .join incoming _ => outerLabel incoming
  | .service endpoint false body =>
    if endpoint.val == labelEndpoint then some (.empty, body) else none
  | _ => none

private structure Output where
  entity : PatternSubject
  name : String
  predicate : String

private def outputFor (name : String) : Option Output :=
  let suffixes := [("AltLabel", aliasIri), ("Description", descriptionIri), ("Label", labelIri)]
  suffixes.findSome? fun (suffix, predicate) =>
    if name.endsWith suffix && name.length > suffix.length then
      some ⟨.var (String.ofList (name.toList.take (name.length - suffix.length))), name, predicate⟩
    else none

private def readBody : List TriplePattern → List String → List Output →
    Except String (List String × List Output)
  | [], languages, outputs => .ok (languages.reverse, outputs.reverse)
  | triple :: rest, languages, outputs =>
    match triple.s, triple.p, triple.o with
    | .iri subject, .iri predicate, .literal value =>
      if subject.val == paramIri && predicate.val == languageIri &&
          value.val.datatype == "http://www.w3.org/2001/XMLSchema#string" then
        readBody rest (value.val.lexicalForm :: languages) outputs
      else .error "Unsupported label-service parameter"
    | subject, .iri predicate, .var name =>
      if [labelIri, descriptionIri, aliasIri].contains predicate.val then
        readBody rest languages (⟨subject, name, predicate.val⟩ :: outputs)
      else .error "Unsupported label-service predicate"
    | _, _, _ => .error "Unsupported label-service pattern"

private def allocate (used : List String) (stem : String) : String :=
  ((List.range (used.length + 1)).findSome? fun n =>
    let name := if n == 0 then stem else s!"{stem}_{n}"
    if used.contains name then none else some name).getD stem

private def emit (incoming : QueryPattern) (languages : List String) (output : Output)
    (used : List String) : Except String (String × List String) := do
  if output.predicate == aliasIri then
    throw "Alias aggregation requires candidate-subquery analysis"
  if incoming.inScopeVars.contains output.name then
    throw "Prebound label output requires candidate-subquery analysis"
  let value := allocate used (output.name ++ "__wdqs_value")
  let (entity, subject, guard, names) ← match output.entity with
    | .var name =>
      if !(incoming.inScopeVars.contains name) then
        .error s!"Label entity ?{name} has no incoming binding"
      else
        let entityVar := "?" ++ name
        if (definitelyBound incoming).contains name then .ok (entityVar, entityVar, "", value :: used)
        else
          let guarded := allocate (value :: used) (name ++ "__wdqs_subject")
          .ok (entityVar, "?" ++ guarded,
            s!"BIND(IF(BOUND({entityVar}), {entityVar}, \"unbound\") AS ?{guarded})\n",
            guarded :: value :: used)
    | .iri iri => .ok ("<" ++ iri.val ++ ">", "<" ++ iri.val ++ ">", "", value :: used)
    | _ => .error "Unsupported label entity term"
  let isLabel := output.predicate == labelIri
  let priority := if isLabel then labelLanguages languages else descriptionLanguages languages
  let lookups := String.join (priority.map fun language =>
    let literal := "\"" ++ L4Factoidal.Syntax.escapeLiteral language ++ "\""
    s!"OPTIONAL \{ {subject} <{output.predicate}> ?{value} . FILTER(LANG(?{value}) = {literal}) }\n")
  let expression := if isLabel then
    s!"IF(BOUND(?{value}), ?{value}, IF(ISIRI({entity}) && STRSTARTS(STR({entity}), \"http://www.wikidata.org/entity/\"), STRAFTER(STR({entity}), \"entity/\"), STR({entity})))"
    else "?" ++ value
  return (guard ++ lookups ++ s!"BIND({expression} AS ?{output.name})\n", names)

-- Wikimedia's WikibaseLabelRewriter, pinned source:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/WikibaseLabelRewriter.java
/-- Plan a single outer, non-SILENT label service with scalar outputs.
The source range is selected by the lexer, and the service body and incoming
scope are checked against the real parser's AST. -/
def rewriteOuterLabel (query : Query) (language : String) (used later : List String) :
    Except String (String × String) := do
  let some (incoming, body) := outerLabel query.pattern |
    throw "Label service placement requires nested or order-independent scope analysis"
  let .bgp triples := body | throw "Expected label-service triples"
  let (values, manual) ← readBody triples [] []
  let languages := languagePriority language values
  if languages.isEmpty then throw "Missing wikibase:language"
  let outputs ← if manual.isEmpty then
    match query.form with
    | .select (.vars _) =>
      let candidates := query.projectedVars.filterMap outputFor
      for output in candidates do
        if let .var name := output.entity then
          if query.pattern.inScopeVars.contains name && !(incoming.inScopeVars.contains name) then
            throw s!"Label entity ?{name} is introduced after the service"
      pure (candidates.filter fun output =>
        match output.entity with
        | .var name => incoming.inScopeVars.contains name
        | _ => false)
    | _ => throw "Automatic label lookup requires an explicit SELECT projection"
    else pure manual
  let names := outputs.map (·.name)
  if names.any later.contains then
    throw "An output variable also occurs later in the outer group"
  if names.eraseDups.length != names.length then throw "Multiple mappings for a label output"
  let (pieces, _) ← outputs.foldlM (fun (pieces, names) output => do
    let (piece, names) ← emit incoming languages output names
    return (piece :: pieces, names)) ([], used)
  return (String.join pieces.reverse, if manual.isEmpty then "automatic" else "manual")

end L4Factoidal.Wikidata
