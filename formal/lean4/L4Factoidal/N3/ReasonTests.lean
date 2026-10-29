/-
L4Factoidal.N3.ReasonTests — build-time checks of the N3 reasoner. The W3C
suite runs in `Harness/N3Run.lean` (`lake exe l4n3`, manifest-reasoner.ttl).
-/
import L4Factoidal.N3.Reason

namespace L4Factoidal.N3.ReasonTests

open L4Factoidal.RDF
open L4Factoidal.N3

private def ex : String :=
  "@prefix : <http://ex/> . @prefix math: <http://www.w3.org/2000/10/swap/math#> . " ++
  "@prefix log: <http://www.w3.org/2000/10/swap/log#> . " ++
  "@prefix string: <http://www.w3.org/2000/10/swap/string#> . " ++
  "@prefix list: <http://www.w3.org/2000/10/swap/list#> .\n"

private def g (s : String) : N3Graph :=
  match parseN3 (ex ++ s) (some "http://ex/") with
  | .ok d => d.triples
  | .error _ => []

/-- The conclusions of a document equal (as N3 graphs) the triples of `exp`. -/
private def concludes (doc exp : String) : Bool :=
  let (out, limit) := reason { think := true, conclusions := true } (g doc)
  !limit && n3Isomorphic out (g exp) == .equal

-- A Datalog rule.
#guard concludes ":socrates a :Man . { ?x a :Man } => { ?x a :Mortal } ." ":socrates a :Mortal ."
-- `<=` is the same rule written backwards.
#guard concludes ":socrates a :Man . { ?x a :Mortal } <= { ?x a :Man } ." ":socrates a :Mortal ."
-- Chaining to a fixpoint: the transitive closure of a chain of three.
#guard concludes (":a :next :b . :b :next :c . :c :next :d . " ++
    "{ ?x :next ?y } => { ?x :reach ?y } . { ?x :reach ?y . ?y :next ?z } => { ?x :reach ?z } .")
  (":a :reach :b, :c, :d . :b :reach :c, :d . :c :reach :d .")
-- A body blank node is a variable; a head blank node is fresh, once per head values.
#guard concludes (":a :p :o . :b :p :o . { _:x :p :o } => { :seen :it true } .") ":seen :it true ."
#guard concludes (":a :p :o . :b :p :o . { ?x :p :o } => { [] a :Thing } .") "[] a :Thing ."
#guard concludes (":a :p :o . :b :p :o . { ?x :p :o } => { ?x :has [ a :Thing ] } .")
  ":a :has [ a :Thing ] . :b :has [ a :Thing ] ."
-- Built-ins through the SPARQL expression evaluator; values compared by value.
#guard concludes "{ (2 3) math:sum ?x } => { :r :is ?x } ." ":r :is 5 ."
#guard concludes "{ (2.7 2) math:sum 4.7 } => { :ok a :Ok } ." ":ok a :Ok ."
#guard concludes "{ (2 3) math:sum 5.0 } => { :ok a :Ok } ." ":ok a :Ok ."
#guard concludes "{ (7 2) math:remainder ?r } => { :r :is ?r } ." ":r :is 1 ."
#guard concludes "{ (-2 4) math:remainder ?r } => { :r :is ?r } ." ":r :is 2 ."
#guard concludes "{ -2.6 math:rounded ?r } => { :r :is ?r } ." ":r :is -3 ."
#guard concludes "{ 3 math:greaterThan 2 } => { :ok a :Ok } ." ":ok a :Ok ."
#guard concludes "{ 2 math:greaterThan 3 } => { :ok a :Ok } ." ""
#guard concludes "{ (\"a\" \"b\") string:concatenation ?s } => { :r :is ?s } ." ":r :is \"ab\" ."
#guard concludes "{ \"abc\" string:startsWith \"ab\" } => { :ok a :Ok } ." ":ok a :Ok ."
-- A built-in whose input is still a variable waits for the other triples.
#guard concludes ":a :n 2 . { (?x 1) math:sum ?y . :a :n ?x } => { :r :is ?y } ." ":r :is 3 ."
-- Lists: `list:in` binds, and lists have rdf:first / rdf:rest.
#guard concludes "{ ?x list:in (:a :b) } => { ?x a :Member } ." ":a a :Member . :b a :Member ."
#guard concludes ":l :is (1 2) . { :l :is ?l . ?l <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest> ?r } => { :r :is ?r } ."
  ":r :is (2) ."
-- log:includes and log:notIncludes on graph terms.
#guard concludes "{ { :a :b :c . :d :e :f } log:includes { :a :b ?x } } => { :r :is ?x } ." ":r :is :c ."
#guard concludes "{ { :a :b :c } log:notIncludes { :a :b :d } } => { :ok a :Ok } ." ":ok a :Ok ."
#guard concludes "{ { :a :b :c } log:notIncludes { :a :b :c } } => { :ok a :Ok } ." ""
-- A rule that a rule concludes fires in the next round.
#guard concludes (":a a :P . { :go :go :go } => { { ?x a :P } => { ?x a :Q } } . :go :go :go .")
  "{ ?x a :P } => { ?x a :Q } . :a a :Q ."
-- An unbounded rule set stops at a bound and says so.
#guard (reason {} (g ":z a :N . { ?x a :N } => { [ :succ ?x ] a :N } .")).2 == true

end L4Factoidal.N3.ReasonTests
