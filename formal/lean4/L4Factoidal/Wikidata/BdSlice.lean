import L4Factoidal.Wikidata.Source

namespace L4Factoidal.Wikidata.BdSlice
open L4Factoidal.SPARQL

-- Pinned rule and validation order:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/BdSliceRewriter.java

private def namespaceIri := "http://www.bigdata.com/rdf#"
def endpoint := namespaceIri ++ "slice"

structure Problem where
  status : String
  code : String
  message : String

private def invalidBody : Problem :=
  ⟨"skipped_unsupported", "bd_slice_unsupported_service_content",
    "The bd:slice service body is not a supported triple block."⟩

private def invalid (code message : String) : Problem :=
  ⟨"blazegraph_error", "bd_slice_" ++ code, message⟩

private structure Statement where
  subject : PatternSubject
  predicate : Option String
  object : PatternTerm
  vars : List String

private def statements : QueryPattern → Option (List Statement)
  | .empty => some []
  | .bgp triples => some (triples.map fun triple =>
      let pred := match triple.p with | .iri iri => some iri.val | _ => none
      ⟨triple.s, pred, triple.o, (QueryPattern.bgp [triple]).inScopeVars⟩)
  | pat@(.propertyPath subject _ object) =>
      some [⟨subject, none, object, pat.inScopeVars⟩]
  | .join left right => do return (← statements left) ++ (← statements right)
  | _ => none

private def isParameter (statement : Statement) : Bool :=
  match statement.subject with
  | .iri iri => iri.val == namespaceIri ++ "serviceParam"
  | _ => false

private def readParameters (parameters : List Statement) :
    Except Problem (List String × Option PatternTerm) := do
  let mut seen : List String := []
  let mut range : Option PatternTerm := none
  for parameter in parameters do
    let name ← match parameter.predicate with
      | some iri =>
        match ["offset", "limit", "range"].find? (fun name => iri == endpoint ++ "." ++ name) with
        | some name => pure name
        | none => throw (invalid "unrecognized_parameter" "The bd:slice service sets an unrecognized bd:serviceParam.")
      | none => throw (invalid "unrecognized_parameter" "The bd:slice service sets an unrecognized bd:serviceParam.")
    if seen.contains name then
      throw ⟨"ambiguous_conflicting", "bd_slice_duplicate_parameter",
        s!"The bd:slice service sets bd:slice.{name} more than once."⟩
    seen := name :: seen
    if name == "range" then range := some parameter.object
  return (seen, range)

private def keptSource (text : String) (state : PState) (body : List LocatedToken) (stop : Nat) :
    Option String := do
  let inner := (body.drop 1).takeWhile (fun token => token.start < stop - 1)
  -- Parameters are identified by their subject, so an entire same-subject
  -- group belongs to the parameters or to the single kept statement.
  let starts := inner.zip (inner.drop 1) |>.filterMap fun (a, b) =>
    if a.token == .dot then some b else none
  let start ← (inner.head?.toList ++ starts).find? fun token =>
    tokenIri state token.token != some (namespaceIri ++ "serviceParam")
  let statement := (inner.dropWhile (fun token => token.start < start.start)).takeWhile (·.token != .dot)
  let last ← statement.getLast?
  return String.ofList ((text.toList.drop start.start).take (last.stop - start.start))

def plan (text : String) (state : PState) (body : List LocatedToken) (stop : Nat) :
    Except Problem (String × String) := do
  let stream := (body.drop 1).map fun token => (⟨token.token, token.start⟩ : PosToken)
  let pattern ← if peekTok stream == .rbrace then pure .empty else do
    let .ok (pattern, rest) := pTriplesBlock topFuel state (.empty, []) stream | throw invalidBody
    if peekTok rest == .rbrace then pure pattern else throw invalidBody
  let some triples := statements pattern | throw invalidBody
  let (params, kept) := triples.partition isParameter
  let (seen, range) ← readParameters params
  let statement ← match kept with
    | [] => throw (invalid "missing_pattern" "The bd:slice service has no triple to keep.")
    | [statement] => pure statement
    | _ => throw (invalid "multiple_statement_patterns" "The bd:slice service must contain a single statement pattern.")
  let some raw := keptSource text state body stop | throw invalidBody
  let some range := range | return (raw ++ " .\n", "hint-removed")
  if seen.contains "offset" || seen.contains "limit" then
    throw (invalid "mixed_parameters" "bd:slice.range cannot be combined with bd:slice.offset/bd:slice.limit.")
  let .var name := range |
    throw (invalid "range_not_variable" "The bd:slice.range parameter is not a variable.")
  if statement.vars.contains name then
    throw (invalid "range_variable_collision" "The bd:slice.range variable is also bound by the kept pattern.")
  return ("{ SELECT (COUNT(*) AS ?" ++ name ++ ") WHERE { " ++ raw ++ " } }\n", "range-count")

end L4Factoidal.Wikidata.BdSlice
