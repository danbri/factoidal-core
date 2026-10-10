/-
L4Factoidal.RML.StarTests — build-time checks for RML-star: star maps in
subject and object position, asserted and non-asserted triples maps,
nesting, joins between logical sources, and the mapping errors.

A rule has a twin that differs by one property (an asserted map and its
non-asserted twin, a star map with a join and one without), so an
implementation that ignores the property fails.
-/
import L4Factoidal.RML.Run
import L4Factoidal.RML.Targets
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

private def source (path : String) : String :=
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"" ++ path ++ "\" ] ; " ++
  "rml:referenceFormulation rml:CSV ] ; "

private def run (ttl : String) (data : List (String × String)) : EvalResult :=
  runMappingGraphFiles (graphOf (prefixes ++ ttl)) (some "http://example.com/") (files data)

private def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
private def reifies : String := rdfNs ++ "reifies"

/-- How many DISTINCT triples with predicate `p` the run puts in the
    default graph: an output dataset is a set, and a triple generated twice
    is one triple. -/
private def count (r : EvalResult) (p : String) : Nat :=
  (((datasetOfQuads r.quads).default).filter (fun t => t.p.val == p)).length

/-- The reifiers of a run: the distinct subjects of its `rdf:reifies` quads. -/
private def reifiers (r : EvalResult) : List Subject :=
  ((r.quads.filter (fun q => q.p.val == reifies)).map (·.s)).eraseDups

private def entities : String := "entity,class,confidence\nAlice,Person,0.8\nBobby,Dog,0.6\n"

/-- `ex:inner` generates a type triple per row; `ex:outer` quotes it. -/
private def sameSource (innerClass : String) : String :=
  "ex:inner a " ++ innerClass ++ " ; " ++ source "d.csv" ++
  "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate rdf:type ; " ++
  "rml:objectMap [ rml:template \"http://example.com/{class}\" ] ] .\n" ++
  "ex:outer a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
  "rml:subjectMap [ rml:quotedTriplesMap ex:inner ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:confidence ; " ++
  "rml:objectMap [ rml:reference \"confidence\" ] ] ."

-- The fixtures parse: a mapping that does not would make every check below
-- vacuous.
#guard !(graphOf (prefixes ++ sameSource "rml:AssertedTriplesMap")).isEmpty

/-! ## A star map in subject position -/

private def a1 := run (sameSource "rml:AssertedTriplesMap") [("d.csv", entities)]
#guard !a1.rejected
-- an asserted inner map: its type triples are in the output...
#guard count a1 (rdfNs ++ "type") == 2
-- ...and quoted: one reifier and one rdf:reifies triple per row...
#guard count a1 reifies == 2
#guard (reifiers a1).length == 2
-- ...and each confidence triple has a reifier as its subject
#guard count a1 "http://example.com/confidence" == 2
#guard (a1.quads.filter (fun q => q.p.val == "http://example.com/confidence")).all
         (fun q => (reifiers a1).contains q.s)
-- the triple term is the inner triple, not another one
#guard a1.quads.any (fun q => q.p.val == reifies &&
         q.o == Term.tripleTerm (.iri ⟨"http://example.com/Alice", rfl⟩)
                  ⟨rdfNs ++ "type", rfl⟩ (.iri ⟨"http://example.com/Person", rfl⟩))

-- The non-asserted twin: the type triples are NOT in the output, the
-- quoted ones are.
private def a2 := run (sameSource "rml:NonAssertedTriplesMap") [("d.csv", entities)]
#guard !a2.rejected
#guard count a2 (rdfNs ++ "type") == 0
#guard count a2 reifies == 2
#guard count a2 "http://example.com/confidence" == 2

-- A quoted triple has one reifier however often it is quoted: two rows
-- with the same entity and class quote the same triple.
private def a3 := run (sameSource "rml:AssertedTriplesMap")
  [("d.csv", "entity,class,confidence\nAlice,Person,0.8\nAlice,Person,0.9\n")]
#guard (reifiers a3).length == 1
#guard count a3 "http://example.com/confidence" == 2

/-! ## A star map in object position -/

private def objectStar : String :=
  "ex:inner a rml:NonAssertedTriplesMap ; " ++ source "d.csv" ++
  "rml:subjectMap [ rml:template \"http://example.com/{class}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate rdf:type ; " ++
  "rml:objectMap [ rml:template \"http://example.com/{entity}\" ] ] .\n" ++
  "ex:outer a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
  "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:has ; " ++
  "rml:objectMap [ rml:quotedTriplesMap ex:inner ] ] ."

private def b1 := run objectStar [("d.csv", entities)]
#guard !b1.rejected
#guard count b1 "http://example.com/has" == 2
-- the object of each ex:has triple is a reifier
#guard (b1.quads.filter (fun q => q.p.val == "http://example.com/has")).all
         (fun q => match q.o with
           | .bnode b => (reifiers b1).contains (.bnode b)
           | _ => false)
#guard count b1 reifies == 2

/-! ## Nesting -/

private def nestedStar : String :=
  "ex:inner a rml:NonAssertedTriplesMap ; " ++ source "d.csv" ++
  "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate rdf:type ; " ++
  "rml:objectMap [ rml:template \"http://example.com/{class}\" ] ] .\n" ++
  "ex:middle a rml:NonAssertedTriplesMap ; " ++ source "d.csv" ++
  "rml:subjectMap [ rml:quotedTriplesMap ex:inner ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:confidence ; " ++
  "rml:objectMap [ rml:reference \"confidence\" ] ] .\n" ++
  "ex:outer a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
  "rml:subjectMap [ rml:quotedTriplesMap ex:middle ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:by ; " ++
  "rml:objectMap [ rml:template \"http://example.com/{entity}\" ] ] ."

private def n1 := run nestedStar [("d.csv", "entity,class,confidence\nAlice,Person,0.8\n")]
#guard !n1.rejected
-- two reifiers (inner and middle), one asserted triple (outer)
#guard count n1 reifies == 2
#guard count n1 "http://example.com/by" == 1
#guard count n1 "http://example.com/confidence" == 0
#guard count n1 (rdfNs ++ "type") == 0
-- the middle triple term has the inner reifier as its subject
#guard n1.quads.any (fun q => q.p.val == reifies &&
         match q.o with
         | .tripleTerm (.bnode _) p _ => p.val == "http://example.com/confidence"
         | _ => false)

/-! ## Joins between logical sources -/

private def joined (joinText : String) : String :=
  "ex:inner a rml:NonAssertedTriplesMap ; " ++ source "classes.csv" ++
  "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate rdf:type ; " ++
  "rml:objectMap [ rml:template \"http://example.com/{class}\" ] ] .\n" ++
  "ex:outer a rml:AssertedTriplesMap ; " ++ source "conf.csv" ++
  "rml:subjectMap [ rml:quotedTriplesMap ex:inner " ++ joinText ++ " ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:confidence ; " ++
  "rml:objectMap [ rml:reference \"confidence\" ] ] ."

private def joinOn : String :=
  "; rml:joinCondition [ rml:child \"entity\" ; rml:parent \"entity\" ]"

private def j1 := run (joined joinOn)
  [ ("classes.csv", "entity,class\nAlice,Person\nBobby,Dog\n")
  , ("conf.csv", "entity,confidence\nAlice,0.8\nBobby,0.6\n") ]
#guard !j1.rejected
#guard count j1 reifies == 2
#guard count j1 "http://example.com/confidence" == 2

-- A row of the child source that matches no parent row quotes nothing.
private def j2 := run (joined joinOn)
  [ ("classes.csv", "entity,class\nAlice,Person\n")
  , ("conf.csv", "entity,confidence\nAlice,0.8\nCarol,0.5\n") ]
#guard count j2 reifies == 1
#guard count j2 "http://example.com/confidence" == 1

-- The same sources without a join condition: different logical sources
-- need one, so the mapping is rejected.
#guard (run (joined "")
  [ ("classes.csv", "entity,class\nAlice,Person\n")
  , ("conf.csv", "entity,confidence\nAlice,0.8\n") ]).rejected

/-! ## Mapping errors -/

private def invalid (ttl : String) : Bool :=
  !(validateMapping (graphOf (prefixes ++ ttl))).isEmpty

private def valid (ttl : String) : Bool :=
  (validateMapping (graphOf (prefixes ++ ttl))).isEmpty

#guard valid (sameSource "rml:AssertedTriplesMap")
#guard valid (sameSource "rml:NonAssertedTriplesMap")
#guard valid objectStar
#guard valid nestedStar

-- RMLSTARTC009: a quoted triples map in a predicate-object map, outside an
-- object map.
#guard invalid
  ("ex:inner a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
   "rml:predicateObjectMap [ rml:quotedTriplesMap ex:inner ; " ++
   "rml:objectMap [ rml:template \"http://example.com/{class}\" ] ] .")

-- A star map as a predicate map or a graph map.
#guard invalid
  ("ex:inner a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
   "rml:predicateObjectMap [ rml:predicateMap [ rml:quotedTriplesMap ex:inner ] ; " ++
   "rml:objectMap [ rml:template \"http://example.com/{class}\" ] ] .")
#guard invalid
  ("ex:inner a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ; " ++
   "rml:graphMap [ rml:quotedTriplesMap ex:inner ] ] .")

-- A non-asserted map that nothing quotes.
#guard invalid
  ("ex:inner a rml:NonAssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
   "rml:predicateObjectMap [ rml:predicate ex:p ; " ++
   "rml:objectMap [ rml:reference \"class\" ] ] .")

-- A map that is both asserted and non-asserted (RMLSTARTC010's type).
#guard invalid
  ("ex:inner a rml:AssertedTriplesMap, rml:NonAssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:template \"http://example.com/{entity}\" ] ; " ++
   "rml:predicateObjectMap [ rml:predicate ex:p ; " ++
   "rml:objectMap [ rml:reference \"class\" ] ] .\n" ++
   "ex:outer a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:quotedTriplesMap ex:inner ] ; " ++
   "rml:predicateObjectMap [ rml:predicate ex:q ; " ++
   "rml:objectMap [ rml:reference \"confidence\" ] ] .")

-- A quoted triples map that is not a triples map.
#guard invalid
  ("ex:outer a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:quotedTriplesMap ex:nothing ] ; " ++
   "rml:predicateObjectMap [ rml:predicate ex:q ; " ++
   "rml:objectMap [ rml:reference \"confidence\" ] ] .")

-- Two maps that quote each other.
#guard invalid
  ("ex:a a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:quotedTriplesMap ex:b ] ; " ++
   "rml:predicateObjectMap [ rml:predicate ex:q ; " ++
   "rml:objectMap [ rml:reference \"confidence\" ] ] .\n" ++
   "ex:b a rml:AssertedTriplesMap ; " ++ source "d.csv" ++
   "rml:subjectMap [ rml:quotedTriplesMap ex:a ] ; " ++
   "rml:predicateObjectMap [ rml:predicate ex:q ; " ++
   "rml:objectMap [ rml:reference \"confidence\" ] ] .")

end L4Factoidal.RML
