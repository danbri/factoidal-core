/-
L4Factoidal.RIF.Saturate — RIF Core saturation of an RDF graph.

Port of the FUNCTION of `RIF.Core.Tests.fst`'s `saturate_with_program`
(parse RIF-XML rules, run the forward-chaining fixpoint over the
graph's facts, return the saturated graph) and
`materialise_import_graph` (close an imported graph under the
entailment regime its `Import` profile names, BEFORE the rules see
it). The consumers are the SPARQL 1.1 entailment-regime tests that
name `ent:RIF` (rif01 / rif03 / rif04 / rif06).

## The two directions of RIF-RDF Compatibility §3

* Triples → facts (`factsOfTriple`): a triple is a FRAME
  `s[p -> o]`; `rdf:type` is additionally MEMBERSHIP `s # o` and
  `rdfs:subClassOf` additionally SUBCLASS `s ## o`, because RIF rules
  quantify over RIF's own object model. The implementation now lives in
  `RIF/RdfMapping.lean`, shared with `Harness/RifRun.lean`; the names
  are re-exported here for existing callers.
* Facts → triples (`tripleOfGAtom`): the derived frames, memberships
  and subclass atoms come BACK as triples so a SPARQL query can match
  them. A `pos` atom (a RIF predicate that is not a frame) has no RDF
  form and yields no triple. A constant survives the round trip only
  when its lexical form passes the RDF well-formedness checks
  (`isIri`, `literalWf`); a failed conversion marks the result
  incomplete, so query callers cannot accept the partial graph.

Blank nodes ride in `rif:local` space. Rule-local constants are
qualified with a document tag (`Engine.qualifyRule`) BEFORE
saturation, so a rule's `_x` can never capture a data blank node.
-/
import L4Factoidal.RIF.RdfMapping
import L4Factoidal.RIF.Xml
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RIF.Saturate

open L4Factoidal.RDF
open L4Factoidal.RIF

export L4Factoidal.RIF.RdfMapping (rdfTypeStr rdfsSubClassStr gOfTerm gOfSubject factsOfTriple
  termOfG subjectOfG predOfG mkTriple tripleOfGAtom)

/-- The fuel the F* side spends (`RIF.Core.Tests.default_fuel`). -/
def defaultRounds : Nat := 100

/-- A partial closure is available for diagnostics, but query callers must
    obtain the graph through `completeGraph?`. -/
structure Result where
  partialGraph : Graph
  blocked : Bool
  capped : Bool
  unsupportedInput : Bool
  unsupportedOutput : Bool

def Result.complete (r : Result) : Bool :=
  !(r.blocked || r.capped || r.unsupportedInput || r.unsupportedOutput)

def Result.completeGraph? (r : Result) : Option Graph :=
  if r.complete then some r.partialGraph else none

def Result.diagnostic (r : Result) : String :=
  String.intercalate "; " (([
    (r.blocked, "RIF evaluation blocked by an unresolved operation"),
    (r.capped, "RIF saturation round limit reached"),
    (r.unsupportedInput, "RDF input cannot be represented in RIF (direction or triple term)"),
    (r.unsupportedOutput, "derived RIF fact cannot be represented as RDF")
  ].filter (·.1)).map (·.2))

/-- Saturate and preserve all incompleteness flags. Positional atoms have no
    RDF projection by design; failed frame/member/subclass conversions are
    reported. Rule-local constants are qualified before evaluating. -/
def saturateGraph (docTag : String) (rules : List Rule) (g : Graph)
    (rounds : Nat := defaultRounds) : Result :=
  let facts := g.flatMap factsOfTriple
  let qualified := rules.map (qualifyRule docTag)
  let (fs, blocked, capped) := closure qualified facts rounds
  let derived := fs.filterMap tripleOfGAtom
  { partialGraph := g ++ (derived.filter (fun t => !(g.contains t))).eraseDups
    blocked, capped
    unsupportedInput := !RdfMapping.graphMappingSupported g
    unsupportedOutput := fs.any (fun f => match f with
      | .pos .. => false
      | _ => (tripleOfGAtom f).isNone) }

/-- Parse RIF-XML and saturate — the F* `saturate_with_program`.
`none` iff the RIF-XML does not parse. The caller resolves and merges
`Import` graphs into `g` first (`Xml.parseRifProgram` exposes the
import list on the parsed document). -/
def saturateWithProgram (rifXml : String) (g : Graph)
    (rounds : Nat := defaultRounds) : Option Result :=
  match Xml.parseRifProgram rifXml with
  | none => none
  | some doc => some (saturateGraph "rules" doc.rules g rounds)

/-! ## Build-time checks -/

/-! A frame fact round-trips to its triple. -/
#guard
  (tripleOfGAtom (GAtom.frame (gIri "http://ex.org/s")
                              (gIri "http://ex.org/p")
                              (gIri "http://ex.org/o"))).isSome

/-! A `pos` atom has no RDF form. -/
#guard (tripleOfGAtom (GAtom.pos "f" iriSpace [])) == none

/-! Membership comes back as `rdf:type`. -/
#guard
  (match tripleOfGAtom (GAtom.member (gIri "http://ex.org/a")
                                     (gIri "http://ex.org/C")) with
   | some t => t.p.val == rdfTypeStr
   | none   => false)

end L4Factoidal.RIF.Saturate
