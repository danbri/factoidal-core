/-
L4Factoidal.RML.CollectionTests — build-time checks for RML-CC, gather
maps: lists and containers, the append and cartesian strategies, empty
collections, named collections merged across iterations, graphs, nesting
and referencing members.

The shape of each check is the rule it pins: how many triples a
collection has, whether two iterations share a head, what an empty
gather yields. A rule has a twin that differs by one property, so an
implementation that ignores the property fails.
-/
import L4Factoidal.RML.Run
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.Syntax

private def graphOf (ttl : String) : Graph :=
  match parseTurtle ttl none with
  | .ok g    => g
  | .error _ => []

private def prefixes : String :=
  "@prefix rml: <http://w3id.org/rml/> .\n@prefix ex: <http://example.com/> .\n" ++
  "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n"

private def files (entries : List (String × String)) : FileAccess :=
  { read := fun _ p => (entries.find? (fun e => e.1 == p)).map (fun e => e.2.toUTF8) }

/-- A mapping over `d.json` whose object map is `om`. -/
private def mapping (om : String) : String :=
  "ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$.*\" ] ; " ++
  "rml:subjectMap [ rml:template \"http://example.org/e/{$.id}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:with ; rml:objectMap [ " ++ om ++ " ] ] ."

private def run (ttl : String) (data : String) : EvalResult :=
  runMappingGraphFiles (graphOf (prefixes ++ ttl)) (some "http://example.com/")
    (files [("d.json", data)])

private def two : String :=
  "[{\"id\":\"a\",\"v1\":[\"1\",\"2\"],\"v2\":[\"x\",\"y\"]},{\"id\":\"b\",\"v1\":[\"3\"],\"v2\":[]}]"

private def count (r : EvalResult) (p : String) : Nat :=
  (r.quads.filter (fun q => q.p.val == p)).length

private def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

private def listOm (extra : String) (refs : String) (kind : String) : String :=
  extra ++ " rml:gather ( " ++ refs ++ " ) ; rml:gatherAs rdf:" ++ kind

private def ref (path : String) : String := "[ rml:reference \"" ++ path ++ "\" ]"

private def nested : String :=
  "rml:gather ( [ " ++ listOm "" (ref "$.v1.*") "Bag" ++ " ] [ " ++
  listOm "" (ref "$.v2.*") "Bag" ++ " ] ) ; rml:gatherAs rdf:List"

-- The fixtures parse: a mapping that does not would make every check below
-- vacuous.
#guard !(graphOf (prefixes ++ mapping (listOm "" (ref "$.v1.*") "List"))).isEmpty
#guard !(graphOf (prefixes ++ mapping nested)).isEmpty

-- A list of two values: the link, then a first and a rest per cell.
private def r1 := run (mapping (listOm "" (ref "$.v1.*") "List")) two
#guard !r1.rejected
#guard count r1 "http://example.com/with" == 2
#guard count r1 (rdfNs ++ "first") == 3
#guard count r1 (rdfNs ++ "rest") == 3
-- ...whose last cell ends in rdf:nil.
#guard (r1.quads.filter (fun q => q.p.val == rdfNs ++ "rest" &&
         q.o == Term.iri ⟨rdfNs ++ "nil", rfl⟩)).length == 2

-- A bag: one rdf:type and one numbered member per value.
private def r2 := run (mapping (listOm "" (ref "$.v1.*") "Bag")) two
#guard count r2 (rdfNs ++ "type") == 2
#guard count r2 (rdfNs ++ "_1") == 2
#guard count r2 (rdfNs ++ "_2") == 1
#guard count r2 (rdfNs ++ "first") == 0
-- Seq and Alt are typed as themselves.
#guard (run (mapping (listOm "" (ref "$.v1.*") "Seq")) two).quads.any
         (fun q => q.o == Term.iri ⟨rdfNs ++ "Seq", rfl⟩)
#guard (run (mapping (listOm "" (ref "$.v1.*") "Alt")) two).quads.any
         (fun q => q.o == Term.iri ⟨rdfNs ++ "Alt", rfl⟩)

-- Append: the members of all term maps go in ONE list. a: 1,2,x,y; b: 3.
#guard count (run (mapping (listOm "" (ref "$.v1.*" ++ " " ++ ref "$.v2.*") "List")) two)
         (rdfNs ++ "first") == 5
#guard count (run (mapping (listOm "" (ref "$.v1.*" ++ " " ++ ref "$.v2.*") "List")) two)
         "http://example.com/with" == 2
-- Cartesian product: a list per combination. a: 2*2 = 4 lists of two;
-- b: v2 is empty, so no combination, and no list.
private def r3 := run (mapping (listOm "rml:strategy rml:cartesianProduct ;"
  (ref "$.v1.*" ++ " " ++ ref "$.v2.*") "List")) two
#guard count r3 "http://example.com/with" == 4
#guard count r3 (rdfNs ++ "first") == 8

-- An empty gather yields nothing unless it is allowed.
private def emptyData : String := "[{\"id\":\"a\",\"v1\":[]}]"
#guard (run (mapping (listOm "" (ref "$.v1.*") "List")) emptyData).quads.isEmpty
#guard (run (mapping (listOm "rml:allowEmptyListAndContainer false ;" (ref "$.v1.*") "List"))
         emptyData).quads.isEmpty
-- ...in which case a list is rdf:nil and a container is a typed head.
#guard (run (mapping (listOm "rml:allowEmptyListAndContainer true ;" (ref "$.v1.*") "List"))
         emptyData).quads.length == 1
#guard (run (mapping (listOm "rml:allowEmptyListAndContainer true ;" (ref "$.v1.*") "List"))
         emptyData).quads.any (fun q => q.o == Term.iri ⟨rdfNs ++ "nil", rfl⟩)
#guard (run (mapping (listOm "rml:allowEmptyListAndContainer true ;" (ref "$.v1.*") "Bag"))
         emptyData).quads.length == 2

/-! ## Named collections are merged across iterations -/

private def same : String :=
  "[{\"id\":\"a\",\"v1\":[\"1\",\"2\"]},{\"id\":\"b\",\"v1\":[\"3\"]},{\"id\":\"a\",\"v1\":[\"5\",\"6\"]}]"

-- Unnamed: three iterations, three lists (2 + 1 + 2 members).
#guard count (run (mapping (listOm "" (ref "$.v1.*") "List")) same) (rdfNs ++ "first") == 5
#guard count (run (mapping (listOm "" (ref "$.v1.*") "List")) same) "http://example.com/with" == 3
-- Named by a template: iterations a and a are ONE list of four, and b is
-- another, so two links and five cells; the head of the first has the
-- first member.
private def r4 := run (mapping (listOm "rml:template \"c/{$.id}\" ;" (ref "$.v1.*") "List")) same
#guard count r4 "http://example.com/with" == 3
#guard count r4 (rdfNs ++ "first") == 5
#guard (r4.quads.filter (fun q => q.p.val == rdfNs ++ "first" &&
         q.s == Subject.iri ⟨"http://example.com/c/a", rfl⟩)).length == 1
-- A named bag numbers its members across iterations: a has _1 to _4.
private def r5 := run (mapping (listOm "rml:template \"c/{$.id}\" ;" (ref "$.v1.*") "Bag")) same
#guard count r5 (rdfNs ++ "_4") == 1
#guard count r5 (rdfNs ++ "type") == 2
-- The same bag unnamed keeps the three separate.
#guard count (run (mapping (listOm "" (ref "$.v1.*") "Bag")) same) (rdfNs ++ "type") == 3
#guard count (run (mapping (listOm "" (ref "$.v1.*") "Bag")) same) (rdfNs ++ "_4") == 0

/-! ## A gather map in the subject map; nested gather maps -/


#guard (run ("ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$.*\" ] ; " ++
  "rml:subjectMap [ " ++ listOm "" (ref "$.v1.*") "List" ++ " ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:by ; rml:object ex:Doe ] .") two).quads.length == 8
-- A collection placed with SEVERAL triples is still one collection: two
-- predicate-object maps give two triples from the subject, and the list
-- is not appended twice (named, so the merge would show it).
#guard count (run ("ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$.*\" ] ; " ++
  "rml:subjectMap [ " ++ listOm "rml:template \"http://example.org/c/{$.id}\" ;" (ref "$.v1.*") "List" ++ " ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:by ; rml:object ex:Doe ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:at ; rml:object ex:Home ] .") two) (rdfNs ++ "first") == 3
-- ...and with no predicate-object map the lists alone are generated.
#guard (run ("ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$.*\" ] ; " ++
  "rml:subjectMap [ " ++ listOm "" (ref "$.v1.*") "Bag" ++ " ] .") two).quads.length == 3 + 2

-- Nested: a list of two bags.
private def r6 := run (mapping nested) two
#guard !r6.rejected
-- a: both bags exist; b: its second bag is empty, so only one.
#guard count r6 (rdfNs ++ "type") == 3
#guard count r6 (rdfNs ++ "first") == 3

/-! ## Graphs: the cells go where the link goes, and a blank node belongs to one graph -/

private def graphData : String :=
  "[{\"id\":\"a\",\"graph\":\"1\",\"v1\":[\"1\"]},{\"id\":\"a\",\"graph\":\"2\",\"v1\":[\"2\"]}]"

private def graphMapping (om : String) : String :=
  "ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$.*\" ] ; " ++
  "rml:subjectMap [ rml:template \"http://example.org/e/{$.id}\" ] ; " ++
  "rml:predicateObjectMap [ rml:graphMap [ rml:template \"http://example.org/g/{$.graph}\" ] ; " ++
  "rml:predicate ex:with ; rml:objectMap [ " ++ om ++ " ] ] ."

private def r7 := run (graphMapping (listOm "" (ref "$.v1.*") "List")) graphData
#guard r7.quads.length == 6
#guard r7.quads.all (fun q => q.g.isSome)
-- Named by a blank-node template, the same label in two graphs is two blank
-- nodes (RMLTC-CC-0010-Listb), so two cells exist, not one.
private def r8 := run (graphMapping (listOm "rml:template \"l/{$.id}\" ; rml:termType rml:BlankNode ;"
  (ref "$.v1.*") "List")) graphData
#guard (r8.quads.filter (fun q => q.p.val == rdfNs ++ "first")).length == 2
#guard ((r8.quads.filter (fun q => q.p.val == rdfNs ++ "first")).map (·.s)).eraseDups.length == 2

/-! ## A referencing member (RMLTC-CC-0008-ROMb) -/

private def rom : EvalResult :=
  run ("ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$.*\" ] ; " ++
  "rml:subjectMap [ rml:template \"http://example.org/e/{$.id}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:with ; rml:objectMap [ rml:gather ( [ rml:parentTriplesMap ex:tm ] ) ; " ++
  "rml:gatherAs rdf:List ] ] .") two
-- Same logical source and no join: each subject's own list holds the
-- subject of the SAME iteration, not of every iteration.
#guard !rom.rejected
#guard count rom (rdfNs ++ "first") == 2
#guard count rom "http://example.com/with" == 2

/-! ## Validation -/

private def valid (ttl : String) : Bool := (validateMapping (graphOf (prefixes ++ ttl))).isEmpty

#guard valid (mapping (listOm "" (ref "$.v1.*") "List"))
-- A gather map needs rdf:List, rdf:Seq, rdf:Bag or rdf:Alt.
#guard !valid (mapping "rml:gather ( [ rml:reference \"$.v1.*\" ] ) ; rml:gatherAs ex:Thing")
#guard !valid (mapping "rml:gather ( [ rml:reference \"$.v1.*\" ] )")
-- A non-empty list of members.
#guard !valid (mapping "rml:gather ( ) ; rml:gatherAs rdf:List")
-- A known strategy.
#guard valid (mapping (listOm "rml:strategy rml:cartesianProduct ;" (ref "$.v1.*") "List"))
#guard !valid (mapping (listOm "rml:strategy ex:shuffle ;" (ref "$.v1.*") "List"))
-- The companion properties need rml:gather.
#guard !valid (mapping "rml:reference \"$.v1\" ; rml:gatherAs rdf:List")
-- allowEmptyListAndContainer is boolean.
#guard valid (mapping (listOm "rml:allowEmptyListAndContainer true ;" (ref "$.v1.*") "List"))
#guard !valid (mapping (listOm "rml:allowEmptyListAndContainer \"maybe\" ;" (ref "$.v1.*") "List"))
-- A member is checked as a term map.
#guard !valid (mapping (listOm "" "[ rml:reference \"$.v1[\" ]" "List"))

end L4Factoidal.RML
