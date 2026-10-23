/-
L4Factoidal.RDF.StreamSetTests — executable checks of `RDF/StreamSet.lean`,
evaluated during `lake build`.

RDF 1.1 Concepts section 3: an RDF graph is a set of RDF triples. The streamed
output of `l4factoidal parse FILE --out nquads` for N-Triples and Turtle must
be the canonical N-Quads text of the whole-file parse (`Source.parseDocument`,
which gives a set), at every chunk size: a triple that the document states
two times, one chunk or many chunks apart, is written once, at the place of its
first occurrence, and two triples whose language tags differ only in case are
one triple (`Triple.eqb`). No executable imports this module.
-/
import L4Factoidal.RDF.StreamSet

namespace L4Factoidal.RDF.StreamSetTests

open L4Factoidal.RDF
open L4Factoidal.Syntax

private def a : String := "<http://e/a> <http://e/p> \"v\" .\n"
private def b : String := "<http://e/b> <http://e/p> \"v\" .\n"
private def aLower : String := "<http://e/a> <http://e/p> \"x\"@en .\n"
private def aUpper : String := "<http://e/a> <http://e/p> \"x\"@EN .\n"

private def ttlPrefix : String := "@prefix e: <http://e/> . "

/-- The canonical text of the whole-file parse. -/
private def whole (fmt : RdfFormat) (text : String) : Option String :=
  ((Source.parseDocument {} fmt .rdf11 none text).toOption).map Dataset.toCanonicalNQuads

private def sizes : List Nat := [1, 2, 3, 5, 7, 16, 64, 100000]

/-- The streamed text is the whole-file text at every chunk size. -/
private def agrees (fmt : RdfFormat) (text : String) : Bool :=
  match whole fmt text with
  | none => false
  | some w => sizes.all fun n => (streamedNQuads fmt .rdf11 "" n text).toOption == some w

/-- The streamed text at every chunk size is `expected`. -/
private def streams (fmt : RdfFormat) (text expected : String) : Bool :=
  sizes.all fun n => (streamedNQuads fmt .rdf11 "" n text).toOption == some expected

-- A document with no repeated triple is written as it is (the streamed loop works).
#guard streams .nt (a ++ b) (a ++ b)
#guard streams .turtle (ttlPrefix ++ "e:a e:p \"v\" . e:b e:p \"v\" .") (a ++ b)
#guard agrees .turtle (ttlPrefix ++ "e:a e:p \"v\", \"w\" .")

-- N-Triples: the same triple on two lines is one line; a, b, a is a, b.
#guard streams .nt (a ++ a) a
#guard streams .nt (a ++ b ++ a) (a ++ b)
#guard agrees .nt (a ++ b ++ a ++ b ++ a)
-- Language tags compare without case: one triple, written in lower case.
#guard streams .nt (aLower ++ aUpper) aLower
#guard streams .nt (aUpper ++ aLower) aLower
-- A different datatype or a different language tag is a different triple.
#guard agrees .nt (a ++ "<http://e/a> <http://e/p> \"v\"@en .\n" ++ a)

-- Turtle: two statements, an object list with the object two times, a
-- statement that repeats a triple of an earlier statement.
#guard streams .turtle (ttlPrefix ++ "e:a e:p \"v\" . e:a e:p \"v\" .") a
#guard streams .turtle (ttlPrefix ++ "e:a e:p \"v\", \"v\" .") a
#guard streams .turtle (ttlPrefix ++ "e:a e:p \"v\" . e:b e:p \"v\" . e:a e:p \"v\" .") (a ++ b)
#guard agrees .turtle (ttlPrefix ++ "e:a e:p \"v\", \"w\", \"v\" ; e:q e:b . e:a e:p \"w\" .")

-- No two lines of the output are equal.
private def noRepeatedLine (fmt : RdfFormat) (text : String) : Bool :=
  sizes.all fun n =>
    match streamedNQuads fmt .rdf11 "" n text with
    | .error _ => false
    | .ok out =>
      let ls := (out.splitOn "\n").filter (· ≠ "")
      ls.eraseDups.length == ls.length
#guard noRepeatedLine .nt (a ++ b ++ a ++ aLower ++ b ++ aUpper)
#guard noRepeatedLine .turtle (ttlPrefix ++ "e:a e:p \"v\", \"v\" . e:a e:p \"v\" . e:b e:p \"v\" .")

end L4Factoidal.RDF.StreamSetTests
