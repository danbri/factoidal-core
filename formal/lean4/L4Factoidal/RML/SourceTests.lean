/-
L4Factoidal.RML.SourceTests — build-time checks for RML-IO behaviour that
runs a whole mapping: sources of each kind, null values, the canonical
lexical form of a datatype override, and the routing of quads to logical
targets.

Each routing guard has a twin that routes the other way, so an
implementation that sent every quad everywhere, or nowhere, fails.
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
  "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n" ++
  "@prefix formats: <http://www.w3.org/ns/formats/> .\n"

private def files (entries : List (String × String)) : FileAccess :=
  { read := fun _ p => (entries.find? (fun e => e.1 == p)).map (fun e => e.2.toUTF8) }

private def runWith (ttl : String) (entries : List (String × String)) : EvalResult :=
  runMappingGraphFiles (graphOf (prefixes ++ ttl)) (some "http://example.com/") (files entries)

private def friendsJson : String :=
  "[{\"id\":0,\"name\":\"A\",\"age\":33},{\"id\":1,\"name\":\"B\",\"age\":34}]"

/-- A JSON mapping with a hook for the subject map's extras, the name
    predicate map's extras and the age object map's extras, and optional
    graph maps. -/
private def jsonMapping (subjectExtra nameExtra ageExtra : String) : String :=
  "ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"f.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$[*]\" ] ; " ++
  "rml:subjectMap [ rml:template \"http://example.org/{$.id}\" " ++ subjectExtra ++ " ] ; " ++
  "rml:predicateObjectMap [ rml:predicateMap [ rml:constant ex:name " ++ nameExtra ++ " ] ; " ++
  "rml:objectMap [ rml:reference \"$.name\" ] ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:age ; " ++
  "rml:objectMap [ rml:reference \"$.age\" " ++ ageExtra ++ " ] ] ."

private def targetDecl : String :=
  "ex:t1 a rml:LogicalTarget ; rml:target [ a rml:FilePath ; rml:path \"d1.nq\" ] ; rml:serialization formats:N-Quads .\n" ++
  "ex:t2 a rml:LogicalTarget ; rml:target [ a rml:FilePath ; rml:path \"d2.nq\" ] ; rml:serialization formats:N-Quads .\n"

private def quadsTo (r : EvalResult) (t : Option String) : Nat := (quadsFor t r.quads).length

private def jsonRun (s n a : String) : EvalResult :=
  runWith (targetDecl ++ jsonMapping s n a) [("f.json", friendsJson)]

-- Without any target, every quad goes to the default target.
#guard !(jsonRun "" "" "").rejected
#guard quadsTo (jsonRun "" "" "") none == 4
-- A subject-map target takes every quad of the map (4), leaving none for
-- the default.
#guard quadsTo (jsonRun "; rml:logicalTarget ex:t1" "" "") (some "http://example.com/t1") == 4
#guard quadsTo (jsonRun "; rml:logicalTarget ex:t1" "" "") none == 0
-- A predicate-map target takes the quads of that predicate only (2 of 4),
-- and the rest stay with the default target.
#guard quadsTo (jsonRun "" "; rml:logicalTarget ex:t1" "") (some "http://example.com/t1") == 2
#guard quadsTo (jsonRun "" "; rml:logicalTarget ex:t1" "") none == 2
-- An object-map target likewise (the age object map).
#guard quadsTo (jsonRun "" "" "; rml:logicalTarget ex:t2") (some "http://example.com/t2") == 2
#guard quadsTo (jsonRun "" "" "; rml:logicalTarget ex:t2") none == 2
-- Two targets on one term map: the quads go to both.
#guard quadsTo (jsonRun "; rml:logicalTarget ex:t1 ; rml:logicalTarget ex:t2" "" "")
         (some "http://example.com/t1") == 4
#guard quadsTo (jsonRun "; rml:logicalTarget ex:t1 ; rml:logicalTarget ex:t2" "" "")
         (some "http://example.com/t2") == 4
-- Targets on different term maps of one quad add up: the name quads have
-- the subject's target and the predicate's.
#guard quadsTo (jsonRun "; rml:logicalTarget ex:t1" "; rml:logicalTarget ex:t2" "")
         (some "http://example.com/t2") == 2
#guard quadsTo (jsonRun "; rml:logicalTarget ex:t1" "; rml:logicalTarget ex:t2" "")
         (some "http://example.com/t1") == 4

/-- A graph map's target belongs to the quads in the graph that map
    generates (`RMLTTC0002o`): the name quads are also in the graph of the
    predicate-object level map. -/
private def graphRun : EvalResult :=
  runWith (targetDecl ++
    "ex:tm a rml:TriplesMap ; " ++
    "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"f.json\" ] ; " ++
    "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$[*]\" ] ; " ++
    "rml:subjectMap [ rml:template \"http://example.org/{$.id}\" ; " ++
    "rml:graphMap [ rml:constant ex:g1 ; rml:logicalTarget ex:t1 ] ] ; " ++
    "rml:predicateObjectMap [ rml:predicate ex:name ; rml:objectMap [ rml:reference \"$.name\" ] ; " ++
    "rml:graphMap [ rml:constant ex:g2 ; rml:logicalTarget ex:t2 ] ] ; " ++
    "rml:predicateObjectMap [ rml:predicate ex:age ; rml:objectMap [ rml:reference \"$.age\" ] ] .")
    [("f.json", friendsJson)]

-- 2 name quads in each of g1, g2; 2 age quads in g1: six quads, and each
-- target holds exactly the quads of its own graph.
#guard graphRun.quads.length == 6
#guard quadsTo graphRun (some "http://example.com/t1") == 4
#guard quadsTo graphRun (some "http://example.com/t2") == 2
#guard quadsTo graphRun none == 0

-- Targets are read from the graph: the id, the file, the serialisation.
#guard (logicalTargetsOf (graphOf (prefixes ++ targetDecl))).length == 2
#guard ((logicalTargetsOf (graphOf (prefixes ++ targetDecl))).map (·.path)) == ["d1.nq", "d2.nq"]
#guard ((logicalTargetsOf (graphOf (prefixes ++ targetDecl))).map (·.serialization)) ==
       [formatsNs ++ "N-Quads", formatsNs ++ "N-Quads"]
-- `rml:compression` and `rml:encoding` are read from the target node or
-- from the logical target beside `rml:serialization`.
#guard ((logicalTargetsOf (graphOf (prefixes ++
         "ex:t a rml:LogicalTarget ; rml:target [ a rml:FilePath ; rml:path \"d\" ; rml:compression rml:gzip ] ."))).map (·.compression))
       == ["http://w3id.org/rml/gzip"]
#guard ((logicalTargetsOf (graphOf (prefixes ++
         "ex:t a rml:LogicalTarget ; rml:encoding rml:UTF-16 ; rml:target [ a rml:FilePath ; rml:path \"d\" ] ."))).map (·.encoding))
       == ["http://w3id.org/rml/UTF-16"]

/-! ## The canonical lexical form of a datatype override (RMLTTC0002q) -/

private def dtRun (dt : String) : List Term :=
  (runWith (jsonMapping "" "" ("; rml:datatype " ++ dt)) [("f.json", friendsJson)]).quads.filterMap
    (fun q => if q.p.val == "http://example.com/age" then some q.o else none)

private def lexicals (ts : List Term) : List String :=
  ts.filterMap (fun t => match t with | .literal l => some l.val.lexicalForm | _ => none)

#guard lexicals (dtRun "xsd:double") == ["3.3E1", "3.4E1"]
#guard lexicals (dtRun "xsd:integer") == ["33", "34"]
#guard lexicals (dtRun "xsd:decimal") == ["33", "34"]
-- A string type is not rewritten.
#guard lexicals (dtRun "xsd:string") == ["33", "34"]
-- An override whose lexical form is outside the datatype is a rejection.
#guard (runWith (jsonMapping "" "" "; rml:datatype xsd:boolean") [("f.json", friendsJson)]).rejected

/-! ## CSV, nulls and XML sources through a whole mapping -/

private def csvMapping (src : String) : String :=
  "ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"f.csv\" " ++ src ++ " ] ; " ++
  "rml:referenceFormulation rml:CSV ] ; " ++
  "rml:subjectMap [ rml:template \"http://example.org/{id}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:name ; rml:objectMap [ rml:reference \"name\" ] ] ."

private def csvText : String := "id,name\n0,A\n1,\n"

-- With no `rml:null`, an empty cell is a value (RMLSTC0004a): 2 quads.
#guard (runWith (csvMapping "") [("f.csv", csvText)]).quads.length == 2
-- With `rml:null ""`, it is not (RMLSTC0004b): 1 quad.
#guard (runWith (csvMapping "; rml:null \"\"") [("f.csv", csvText)]).quads.length == 1
-- A row of the wrong width rejects the mapping (RMLSTC0010a).
#guard (runWith (csvMapping "") [("f.csv", "id,name\n0\n")]).rejected
-- A missing file rejects it (RMLTC0002e).
#guard (runWith (csvMapping "") []).rejected

private def xmlMapping (ns : String) : String :=
  "ex:tm a rml:TriplesMap ; " ++
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"f.xml\" ] ; " ++
  (if ns.isEmpty then "rml:referenceFormulation rml:XPath ; rml:iterator \"/people/person\" ]"
   else "rml:referenceFormulation [ a rml:XPathReferenceFormulation ; " ++
        "rml:namespace [ rml:namespacePrefix \"p\" ; rml:namespaceURL \"http://p\" ] ] ; " ++
        "rml:iterator \"/p:people/p:person\" ]") ++ " ; " ++
  "rml:subjectMap [ rml:template \"http://example.org/{@id}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:name ; rml:objectMap [ rml:reference \"" ++
  (if ns.isEmpty then "name" else "p:name") ++ "/text()\" ] ] ."

#guard (runWith (xmlMapping "")
  [("f.xml", "<people><person id=\"1\"><name>A</name></person><person id=\"2\"><name>B</name></person></people>")]).quads.length == 2
-- With a namespace declared, the prefixed XPath selects the namespaced elements...
#guard (runWith (xmlMapping "ns")
  [("f.xml", "<p:people xmlns:p=\"http://p\"><p:person id=\"1\"><p:name>A</p:name></p:person></p:people>")]).quads.length == 1
-- ...and the unprefixed form selects nothing from them.
#guard (runWith (xmlMapping "")
  [("f.xml", "<p:people xmlns:p=\"http://p\"><p:person id=\"1\"><p:name>A</p:name></p:person></p:people>")]).quads.length == 0

end L4Factoidal.RML
