import L4Factoidal.Wikidata.Source

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL

-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/GeofDistanceRewriter.java

def legacyGeofDistance : String := "http://www.opengis.net/def/geosparql/function/distance"
private def standardGeof : String := "http://www.opengis.net/def/function/geosparql/"

private def distanceArgs (state : PState) (tokens : TStream) : Option (Option Edit) := do
  let parse := pExpr topFuel state
  let (_, rest) ← (parse tokens).toOption
  let (_, rest) ← (expectTok .comma rest).toOption
  let (_, rest) ← (parse rest).toOption
  match peekTok rest with
  | .rparen => some none
  | .comma => do
    let (_, close) ← (parse (advTok rest)).toOption
    guard (peekTok close == .rparen)
    pure (some ⟨peekPos rest, peekPos close, ""⟩)
  | _ => none

private def distanceEdits (state : PState) :
    List LocatedToken → TStream → List Edit → List Edit → Except Nat (List Edit × List Edit)
  | loc :: next :: tail, _ :: openParen :: args, edits, other => do
    let call := openParen.tok == .lparen && tokenIri state loc.token == some legacyGeofDistance
    if call then
      let some dropArg := distanceArgs state args | throw loc.start
      let rewrite := ⟨loc.start, loc.stop, "geof:distance"⟩
      distanceEdits state (next :: tail) (openParen :: args)
        (dropArg.elim (rewrite :: edits) (fun drop => drop :: rewrite :: edits)) other
    else
      let other := match loc.token with
        | .pname name =>
          if (splitPname name).1 == "geof" then
            (tokenIri state loc.token).elim other (fun iri => ⟨loc.start, loc.stop, "<" ++ iri ++ ">"⟩ :: other)
          else other
        | _ => other
      distanceEdits state (next :: tail) (openParen :: args) edits other
  | _, _, edits, other => pure (edits.reverse, other.reverse)

private def disjointEdits : Nat → List Edit → List Edit → List Edit
  | _, [], acc => acc.reverse
  | stop, edit :: rest, acc =>
    if edit.start < stop then disjointEdits stop rest acc
    else disjointEdits edit.stop rest (edit :: acc)

/-- Replace legacy distance calls and drop the ignored third argument.
Resolve other uses of the geof prefix before setting it to the standard IRI. -/
def rewriteGeoDistance (state : PState) (body : TStream) (tokens : List LocatedToken) :
    Except Nat (List Edit × Nat) := do
  let (edits, oldPrefixUses) ← distanceEdits state tokens body [] []
  if edits.isEmpty then return ([], 0)
  let count := (edits.filter fun edit => edit.replacement == "geof:distance").length
  let position := peekPos body
  let declaration := ⟨position, position, "PREFIX geof: <" ++ standardGeof ++ ">\n"⟩
  let edits := (declaration :: edits ++ oldPrefixUses).mergeSort (fun a b => a.start ≤ b.start)
  return (disjointEdits 0 edits [], count)

end L4Factoidal.Wikidata
