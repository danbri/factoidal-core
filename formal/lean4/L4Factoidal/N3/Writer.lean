/-
L4Factoidal.N3.Writer — Notation3 text for an N3 graph.

The writer gives one statement per triple, `subject predicate object .`, with
the Turtle writer's text for IRIs (prefixed when a row of the prefix table
names the namespace and the local part reads back, `tsAbbreviateIri`) and
literals (`tsLiteralToTurtleBy`, with the bare forms of numbers and booleans).
Quick variables are `?name`, lists `( ... )`, graph terms `{ s p o . ... }`,
`rdf:type` is `a` and `log:implies` is `=>`. The reader reads the text back
to an isomorphic graph (`N3/Tests.lean`, and every positive syntax test of
`Harness/N3Run.lean`, which writes and reads again).

A blank node is written with its label. A label the reader made for a
`_:x` inside a graph term contains `.` (`N3State.userBnode`), which a
BLANK_NODE_LABEL allows inside the label; reading it back inside the same
graph term gives it a label that is again unique to that graph term.

No `sorry`, no `axiom`, no `partial def`.
-/
import L4Factoidal.N3.Syntax
import L4Factoidal.Syntax.TurtleSerialize

namespace L4Factoidal.N3

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- The text of a term. `abbr` writes an IRI. -/
def N3Term.toText (abbr : String → String) : N3Term → String
  | .iri i => abbr i.val
  | .bnode b => "_:" ++ b
  | .lit l => tsLiteralToTurtleBy abbr true l
  | .var v => "?" ++ v
  | .triple s p o => tsTermToTurtleBy abbr true (.tripleTerm s p o)
  | .list xs => "(" ++ String.join (xs.attach.map fun ⟨x, _⟩ => " " ++ x.toText abbr) ++ " )"
  | .graph ts =>
      if ts.isEmpty then "{}"
      else "{ " ++ joinWith " . " (ts.attach.map fun ⟨(s, p, o), _h⟩ =>
        s.toText abbr ++ " " ++ predText abbr p (p.toText abbr) ++ " " ++ o.toText abbr) ++ " }"
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem ‹_›; omega
  · exact sizeOf_lt_triple_s _h
  · exact sizeOf_lt_triple_p _h
  · exact sizeOf_lt_triple_o _h
where
  /-- `a` for `rdf:type`, `=>` for `log:implies`, else the term's text. -/
  predText (_abbr : String → String) (p : N3Term) (dflt : String) : String :=
    match p with
    | .iri i => if i == rdfTypeN3 then "a" else if i == logImplies then "=>" else dflt
    | _ => dflt

/-- The prefix table of the Turtle writer (namespace, `label:`) for a reader's
prefix map (label, namespace; most recent first): each label once, the most
recent binding. -/
def prefixTableOf (prefixes : List (String × String)) : PrefixTable :=
  let step : List String × PrefixTable → String × String → List String × PrefixTable :=
    fun (seen, acc) (pfx, ns) =>
      if seen.contains pfx then (seen, acc) else (pfx :: seen, (ns, pfx ++ ":") :: acc)
  (prefixes.foldl step ([], [])).2.reverse

/-- An N3 document: the `@prefix` lines of the table, then one statement per
triple. -/
def writeN3 (table : PrefixTable) (g : N3Graph) : String :=
  let abbr := tsAbbreviateIri table
  let line : N3Triple → String := fun (s, p, o) =>
    s.toText abbr ++ " " ++ N3Term.toText.predText abbr p (p.toText abbr) ++ " " ++
      o.toText abbr ++ " .\n"
  String.join (renderPrefixHeader table) ++ String.join (g.map line)

end L4Factoidal.N3
