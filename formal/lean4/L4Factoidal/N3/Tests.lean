/-
L4Factoidal.N3.Tests — build-time checks of the Notation3 reader, writer and
comparison. The W3C suite runs in `Harness/N3Run.lean` (`lake exe l4n3`).
-/
import L4Factoidal.N3.Compare
import L4Factoidal.N3.Rdf

namespace L4Factoidal.N3.Tests

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.N3

private def ex : String := "@prefix : <http://ex/> .\n"

private def reads (s : String) : Bool := (parseN3 (ex ++ s) (some "http://ex/")).toOption.isSome

private def triplesOf (s : String) : N3Graph :=
  match parseN3 (ex ++ s) (some "http://ex/") with
  | .ok d => d.triples
  | .error _ => []

private def iri (s : String) : N3Term :=
  if h : isIri ("http://ex/" ++ s) then .iri ⟨"http://ex/" ++ s, h⟩ else .var "bad"

/-- The two readers agree on a Turtle text (both refuse, or isomorphic graphs). -/
private def agree (s : String) : Bool :=
  match parseTurtle (ex ++ s) (some "http://ex/"), parseN3ToRdf (ex ++ s) (some "http://ex/") with
  | .error _, .error _ => true
  | .ok g, .ok h => Graph.isomorphicOutcome g h == .equal
  | _, _ => false

/-- Write and read again: isomorphic. -/
private def roundTrips (s : String) : Bool :=
  match parseN3 (ex ++ s) (some "http://ex/") with
  | .error _ => false
  | .ok d =>
      match parseN3 (writeN3 (prefixTableOf d.prefixes) d.triples) (some "http://ex/") with
      | .error _ => false
      | .ok d2 => relabel d.triples == relabel d2.triples

-- Grammar [12] verbs.
#guard triplesOf ":a => :b ." == [(iri "a", .iri logImplies, iri "b")]
#guard triplesOf ":a <= :b ." == [(iri "a", .iri logIsImpliedBy, iri "b")]
#guard triplesOf ":a = :b ." == [(iri "a", .iri owlSameAs, iri "b")]
#guard triplesOf ":a is :p of :b ." == [(iri "b", iri "p", iri "a")]
#guard triplesOf ":a <- :p :b ." == [(iri "b", iri "p", iri "a")]
#guard triplesOf ":a has :p :b ." == [(iri "a", iri "p", iri "b")]
#guard triplesOf ":a <p> :b ." == [(iri "a", iri "p", iri "b")]
#guard triplesOf ":a <=> :b ." == [(iri "a", iri "=", iri "b")]
-- [18] any term in any position.
#guard reads "\"x\" :p 1 ."
#guard reads "?x ?p ?o ."
#guard reads "( 1 2 ) :p { :a :b :c } ."
#guard reads "{ :a :b :c } ."
#guard reads ":a ."
-- [17] paths, left to right.
#guard (triplesOf ":a!:b :c :d .").length == 2
#guard (triplesOf ":a!:b^:c :d :e .").length == 3
-- [21] IRI property lists; `id:` is a prefixed name, not the keyword.
#guard triplesOf "[ id :a :p :b ] ." == [(iri "a", iri "p", iri "b")]
#guard !reads "[ id:a :p :b ] ."
-- [24] the last statement of a graph term needs no `.`; directives inside.
#guard reads "{ :a :b :c . :d :e :f } => { } ."
#guard reads "{ @prefix q: <http://q/> . q:a q:b q:c } :p :o ."
#guard reads "{ PREFIX q: <http://q/> q:a q:b q:c } :p :o ."
-- [1] a top-level statement needs its `.`.
#guard !reads ":a :b :c"
#guard !reads "{ :a :b :c } => { :d :e :f }"
-- Removed by the report (§ "Changes since the Team Submission").
#guard !reads "@forAll :x . :x :p :o ."
#guard !reads "@keywords a ."
#guard !reads ":a @a :C ."
-- A blank node inside a graph term is not the document's blank node.
#guard match triplesOf "_:b :p { _:b :q :r } ." with
  | [(.bnode b1, _, .graph [(.bnode b2, _, _)])] => b1 != b2
  | _ => false
-- Two graph terms do not share a blank node.
#guard match triplesOf "{ _:b :q :r } :p { _:b :q :r } ." with
  | [(.graph [(.bnode b1, _, _)], _, .graph [(.bnode b2, _, _)])] => b1 != b2
  | _ => false
-- Nesting is bounded.
#guard !reads (":a :b " ++ String.join (List.replicate 2100 "(") ++ String.join (List.replicate 2100 ")") ++ " .")
#guard reads (":a :b " ++ String.join (List.replicate 300 "(") ++ String.join (List.replicate 300 ")") ++ " .")
-- The empty prefix defaults to `<#>`.
#guard (parseN3 ":a :b :c ." (some "http://ex/doc")).toOption.map (·.triples.length) == some 1
#guard (parseN3 ":a :b :c ." none).toOption.isNone

-- The N3 reader and the Turtle reader agree on Turtle text.
#guard agree ":a :b :c ."
#guard agree ":a :b :c, :d ; :e ( 1 2.0 3e1 true \"x\"@en \"y\"^^:t ) ."
#guard agree "[ :p [ :q :r ] ] ."
#guard agree "_:x :p _:y . _:y :q ( _:x [] ) ."
#guard agree ":a a :C ; ; :p :o ; ."
#guard agree "PREFIX q: <http://q/> q:a q:b q:c ."
#guard agree "@base <http://other/> . <a> <b> <c> ."
#guard agree ":a :b \"\"\"long\nstring\"\"\" ."
#guard agree ":a :b :c"
#guard agree ":a :b ."
#guard agree "<a b> :p :o ."

-- The writer's text reads back.
#guard roundTrips "{ ?x a :Human } => { ?x a :Mortal } ."
#guard roundTrips "_:b :p { _:b :q ( 1 _:c { } ) } . _:c :r \"x\"@en ."
#guard roundTrips ":a!:b^:c :d [ :e :f ] ."
#guard roundTrips "\"lit\" :p 1.5, -2, 3E4, false ."

-- `{}` and `true` compare equal.
#guard n3Isomorphic (triplesOf ":a :b {} .") (triplesOf ":a :b true .") == .equal
#guard n3Isomorphic (triplesOf ":a :b { :c :d :e . :f :g :h } .")
                    (triplesOf ":a :b { :f :g :h . :c :d :e } .") == .equal
#guard n3Isomorphic (triplesOf "_:x :p _:y .") (triplesOf "_:u :p _:v .") == .equal
#guard n3Isomorphic (triplesOf "_:x :p _:x .") (triplesOf "_:u :p _:v .") == .notEqual
-- Symmetric blank nodes need the search.
#guard n3Isomorphic (triplesOf "_:a :p :o . _:b :p :o . _:c :p :o .")
                    (triplesOf "_:x :p :o . _:y :p :o . _:z :p :o .") == .equal
#guard n3Isomorphic (triplesOf "_:a :p _:b . _:b :p _:a . _:c :p _:d . _:d :p _:c .")
                    (triplesOf "_:w :p _:x . _:x :p _:y . _:y :p _:z . _:z :p _:w .") == .notEqual
#guard n3Isomorphic (triplesOf "_:a :p _:b . _:b :p _:c . _:c :p _:a .")
                    (triplesOf "_:x :p _:z . _:z :p _:y . _:y :p _:x .") == .equal

end L4Factoidal.N3.Tests
