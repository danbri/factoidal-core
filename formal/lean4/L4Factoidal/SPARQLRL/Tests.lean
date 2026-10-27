/-
L4Factoidal.SPARQLRL.Tests — build-time `#guard`s for the SPARQL-RL module
(https://github.com/danbri/factoidal/issues/1099). The W3C suite is run by
`lake exe l4shacl-rules` (`Harness/ShaclRulesRun.lean`); these cases cover what
that suite does not test: group aggregation evaluation, the dependency graph
and the strata of the draft's worked example, imports, generalized triples,
paths and the parser's rejections.
-/
import L4Factoidal.SPARQLRL.Eval
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Canonical

namespace L4Factoidal.SPARQLRL.Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQLRL

def pfx : String := "PREFIX : <http://example/>\nPREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n"

def ttl (body : String) : Graph :=
  match L4Factoidal.Syntax.parseTurtle (pfx ++ body) none .rdf12 with
  | .ok g => g
  | .error _ => []

def canon (g : Graph) : String := (Canonical.canonicalize { default := g, named := [] }).nquads

/-- The canonical N-Quads of the inference graph, or the error message. -/
def run (rules data : String) : String :=
  match inferText (pfx ++ rules) (ttl data) with
  | .ok g => canon g
  | .error e => "ERROR " ++ e

def expect (body : String) : String := canon (ttl body)

def rs (text : String) : RuleSet := ((parseRuleSet (pfx ++ text)).toOption).getD {}

/-! ## The draft's worked example (§ "Worked Example") -/

def workedRules : String := "
RULE { ?x :exposedTo ?v } WHERE { ?x :hasVulnerability ?v }
RULE { ?x :exposedTo ?v } WHERE { ?x :dependsOn ?y . ?y :exposedTo ?v }
RULE { ?x :status :criticallyExposed }
WHERE { ?x :exposedTo ?v . ?v :severity ?s . FILTER(?s >= 9.0) }
RULE { ?x :status :safeToDeploy }
WHERE { ?x rdf:type :Component . NOT { ?x :status :criticallyExposed } }
RULE { [] rdf:type :Notification ; :concerns ?x }
WHERE { ?x :status :criticallyExposed }
"

def workedData : String := "
:frontend rdf:type :Component ; :dependsOn :app .
:app rdf:type :Component ; :dependsOn :db ; :dependsOn :logger .
:db rdf:type :Component ; :hasVulnerability :vuln1 .
:logger rdf:type :Component .
:vuln1 :severity 9.1 .
"

-- six edges: R2→R1, R2→R2, R3→R1, R3→R2 open; R4→R3, R5→R3 closed
#guard (dependencyGraph (rs workedRules).rules).length == 6
#guard (dependencyGraph (rs workedRules).rules).contains ⟨3, 2, .closedDep⟩
#guard (dependencyGraph (rs workedRules).rules).contains ⟨4, 2, .closedDep⟩
#guard (dependencyGraph (rs workedRules).rules).contains ⟨1, 1, .openDep⟩
-- stratum 0: general R1 R2 R3; stratum 1: run-once R5, general R4
#guard stratify (rs workedRules).rules ==
  some [⟨[], [0, 1, 2]⟩, ⟨[4], [3]⟩]

#guard run workedRules workedData == expect "
:db :exposedTo :vuln1 . :app :exposedTo :vuln1 . :frontend :exposedTo :vuln1 .
:db :status :criticallyExposed . :app :status :criticallyExposed .
:frontend :status :criticallyExposed .
[] rdf:type :Notification ; :concerns :db .
[] rdf:type :Notification ; :concerns :app .
[] rdf:type :Notification ; :concerns :frontend .
:logger :status :safeToDeploy ."

/-! ## Group elements (no W3C eval test yet) -/

def groupRules : String := "
RULE { ?s :n ?N ; :sum ?S ; :min ?m ; :max ?M }
WHERE { GROUP BY ?s { ?s :v ?x } [ ?N := COUNT(*) ?S := SUM(?x) ?m := MIN(?x) ?M := MAX(?x) ] }
"

#guard run groupRules ":a :v 1, 2, 3 . :b :v 5 ." == expect "
:a :n 3 ; :sum 6 ; :min 1 ; :max 3 .
:b :n 1 ; :sum 5 ; :min 5 ; :max 5 ."

-- COUNT DISTINCT counts distinct values; COUNT counts solutions
#guard run "RULE { ?s :c ?N ; :d ?D } WHERE { GROUP BY ?s { ?s :v ?x . ?x :w ?y } [ ?N := COUNT(?y) ?D := COUNT(DISTINCT ?y) ] }"
  ":a :v :x1, :x2 . :x1 :w 7 . :x2 :w 7 ." == expect ":a :c 2 ; :d 1 ."

-- no keys: one group over all solutions
#guard run "RULE { :all :n ?N } WHERE { GROUP { ?s :v ?x } [ ?N := COUNT(*) ] }"
  ":a :v 1, 2 . :b :v 3 ." == expect ":all :n 3 ."

-- an aggregate error drops the group: SUM over a non-number
#guard run "RULE { ?s :sum ?S } WHERE { GROUP BY ?s { ?s :v ?x } [ ?S := SUM(?x) ] }"
  ":a :v 1, \"x\" . :b :v 2 ." == expect ":b :sum 2 ."

-- the group element extends the outer solution with the keys and the aggregates
#guard run "RULE { ?s :label ?l ; :n ?N } WHERE { ?s :name ?l GROUP BY ?s { ?s :v ?x } [ ?N := COUNT(*) ] }"
  ":a :name \"A\" ; :v 1, 2 ." == expect ":a :label \"A\" ; :n 2 ."

/-! ## Assignment: an error drops the solution -/

#guard run "RULE { ?x :inv ?z } WHERE { ?x :v ?o SET (?z := 1/?o) }" ":a :v 0 . :b :v 2 ."
  == expect ":b :inv 0.5 ."

/-! ## Paths `/` and `^` -/

#guard run "RULE { ?x :gp ?z } WHERE { ?x :parent/:parent ?z }" ":a :parent :b . :b :parent :c ."
  == expect ":a :gp :c ."
#guard run "RULE { ?x :sib ?y } WHERE { ?x :parent/^:parent ?y FILTER(?x != ?y) }"
  ":a :parent :p . :b :parent :p ." == expect ":a :sib :b . :b :sib :a ."

/-! ## Triple terms and reification in heads -/

-- a head triple term with a variable makes the rule run-once
#guard (rs "RULE { ?x :says <<( ?x :p ?y )>> } WHERE { ?x :q ?y }").rules.all Rule.runOnce
-- a constant triple term does not
#guard !(rs "RULE { ?x :says <<( :a :p :b )>> } WHERE { ?x :q ?y }").rules.any Rule.runOnce
#guard run "RULE { ?x :p ?y ~:r } WHERE { ?x :q ?y }" ":a :q :b ."
  == expect ":a :p :b . :r rdf:reifies <<( :a :p :b )>> ."

/-! ## Generalized triples: matched, not returned -/

#guard run "DATA { 1 :p :o } RULE { :x :found ?s } WHERE { ?s :p :o }" ""
  == expect ":x :found 1 ."

/-! ## Imports -/

def loader (u : String) : Option String :=
  if u == "http://example/lib.srl" then
    some "PREFIX : <http://example/>\nRULE { ?x :q ?y } WHERE { ?x :p ?y }\nIMPORTS <http://example/main.srl>"
  else none

#guard (match inferText (pfx ++ "IMPORTS <http://example/lib.srl>\nRULE { ?x :r ?y } WHERE { ?x :q ?y }")
          (ttl ":a :p :b .") (some "http://example/main.srl") (some loader) with
        | .ok g => canon g
        | .error e => e) == expect ":a :q :b . :a :r :b ."
-- without a loader, IMPORTS is an error
#guard (inferText (pfx ++ "IMPORTS <http://example/lib.srl>") []).toOption.isNone
-- the cycle lib -> main -> lib is read once; without `main` in the visited set,
-- lib's own import of main is a document the loader does not give: an error
#guard (inferText (pfx ++ "IMPORTS <http://example/lib.srl>") [] none (some loader)).toOption.isNone
-- an import that cannot be read is an error
#guard (inferText (pfx ++ "IMPORTS <http://example/none.srl>") [] none (some loader)).toOption.isNone

/-! ## Static checks -/

-- SPARQL functions that SPARQL-RL does not have
#guard !validSyntax (pfx ++ "RULE {} WHERE { ?s ?p ?o FILTER(BOUND(?o)) }")
#guard !validSyntax (pfx ++ "RULE {} WHERE { ?s ?p ?o FILTER(EXISTS { ?s ?p ?o }) }")
#guard !validSyntax (pfx ++ "RULE {} WHERE { ?s ?p ?o SET(?h := MD5(?o)) }")
-- `*` and `+` paths are SPARQL only
#guard !validSyntax (pfx ++ "RULE {} WHERE { ?s :p* ?o }")
-- a character the tokenizer does not know
#guard !validSyntax (pfx ++ "RULE {} WHERE { ?s ?p ?o } %")
-- BASE applies to the IRIs after it
#guard (rs "BASE <http://example/a/>\nDATA { <s> <p> <o> }").data ==
  [⟨.iri ⟨"http://example/a/s", rfl⟩, .iri ⟨"http://example/a/p", rfl⟩, .iri ⟨"http://example/a/o", rfl⟩⟩]
-- a group variable must be new
#guard !wellFormedText (pfx ++ "RULE { ?s :n ?x } WHERE { GROUP BY ?s { ?s :v ?x } [ ?x := COUNT(*) ] }")
-- the aggregated variable must be bound in the group pattern
#guard !wellFormedText (pfx ++ "RULE { ?s :n ?N } WHERE { GROUP BY ?s { ?s :v ?x } [ ?N := SUM(?z) ] }")
-- a run-once rule that feeds itself is not stratifiable
#guard !stratifiableText (pfx ++ "RULE { ?x :n ?N } WHERE { GROUP BY ?x { ?x :n ?y } [ ?N := COUNT(*) ] }")

end L4Factoidal.SPARQLRL.Tests
