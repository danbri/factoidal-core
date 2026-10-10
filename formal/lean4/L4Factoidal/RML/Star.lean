/-
L4Factoidal.RML.Star — quoted triples as RDF 1.2 reifiers.

Spec: RML-star, "Generating quoted triples with RML-star" and "Generating
deeply nested quoted triples"; RDF 1.2 Concepts, "Triple Terms and
Reifiers"; RDF 1.2 Turtle, "Reified Triples".

## What a quoted triple becomes

RML-star talks about RDF-star: a quoted triple `<< s p o >>` is a node of
the graph that can be a subject or an object. RDF 1.2 has no such node.
It has a TRIPLE TERM `<<( s p o )>>`, which can only be an object, and a
REIFIER: a node `r` with `r rdf:reifies <<( s p o )>>`. RDF 1.2 Turtle
defines the reified triple `<< s p o >>` as sugar for the reifier, so a
quoted triple in either position is the reifier, and the triple term is
the object of its `rdf:reifies` triple.

## One reifier per quoted triple

RML-star names the quoted triple by its content: the triple a triples map
generates is the same triple wherever it is quoted. The reifier of a
quoted triple is therefore a blank node whose label is derived from the
triple term (`reifierOf`), so two uses of the same quoted triple share a
reifier without any state, and a label that never collides with the label
of a different triple term.

RDF 1.2 Turtle gives each `<< s p o >>` without a name a FRESH reifier, so
a document that quotes one triple twice has two reifiers. `mergeReifiers`
puts such a graph in the form the evaluator produces, for a comparison:
reifiers of the same triple term become one blank node.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- `rdf:reifies`. -/
def reifiesIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies", rfl⟩

/-- Keep ASCII letters and digits; write every other character as `_`,
    its code point in hexadecimal, and `_`. The map is injective, because
    a code `_xx_` never starts inside the text it replaces. -/
def labelSafe (s : String) : String :=
  s.foldl (fun acc c =>
    if c.toNat < 128 && c.isAlphanum then acc.push c
    else acc ++ "_" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "_") ""

/-- The blank-node label of the reifier of a triple term: a function of the
    triple term's canonical N-Triples form, and nothing else. -/
def reifierLabel (tt : Term) : String := "qt_" ++ labelSafe (L4Factoidal.Syntax.Term.toCanonicalNTriples tt)

/-- The reifier of a quoted triple. -/
def reifierOf (tt : Term) : Term := .bnode (reifierLabel tt)

/-- The `rdf:reifies` triple of a reifier. -/
def reifiesTriple (tt : Term) : Triple := { s := .bnode (reifierLabel tt), p := reifiesIri, o := tt }

/-! ## Merging reifiers -/

private def renameSubject (m : List (String × String)) : Subject → Subject
  | .bnode b => .bnode ((m.find? (·.1 == b)).map (·.2) |>.getD b)
  | s => s

private def renameTerm (m : List (String × String)) : Term → Term
  | .bnode b => .bnode ((m.find? (·.1 == b)).map (·.2) |>.getD b)
  | .tripleTerm s p o => .tripleTerm (renameSubject m s) p (renameTerm m o)
  | t => t

/-- The blank-node reifiers of a graph with the triple term each reifies. -/
def reifierPairs (g : Graph) : List (String × Term) :=
  g.filterMap (fun t =>
    match t.s, t.o with
    | .bnode b, .tripleTerm s p o =>
        if t.p == reifiesIri then some (b, .tripleTerm s p o) else none
    | _, _ => none)

private def mergeStep (g : Graph) : Graph :=
  let pairs := reifierPairs g
  let rename : List (String × String) := pairs.filterMap (fun (b, tt) =>
    match pairs.find? (fun (_, tt2) => tt2 == tt) with
    | some (b0, _) => if b0 != b then some (b, b0) else none
    | none => none)
  if rename.isEmpty then g
  else (g.map (fun t =>
    ({ s := renameSubject rename t.s, p := t.p, o := renameTerm rename t.o } : Triple))).eraseDups

/-- Merge the blank-node reifiers that reify the same triple term. The
    merge repeats until nothing changes, because merging the reifiers of a
    nested quoted triple makes the triple terms that contain them equal. -/
def mergeReifiers (g : Graph) : Graph :=
  (List.range (g.length + 1)).foldl (fun acc _ => mergeStep acc) g

/-! ## Build-time checks -/

private def exIri (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"urn:invalid", rfl⟩

private def ex (n : String) : WfIri := exIri ("http://example/" ++ n)
private def tt1 : Term := .tripleTerm (.iri (ex "s")) (ex "p") (.iri (ex "o"))
private def tt2 : Term := .tripleTerm (.iri (ex "s")) (ex "p") (.iri (ex "z"))

-- the same triple term has the same reifier, a different one does not
#guard reifierOf tt1 == reifierOf tt1
#guard reifierOf tt1 != reifierOf tt2
-- the label is made of letters, digits and underscores only
#guard (reifierLabel tt1).all (fun c => c.isAlphanum || c == '_')
-- the label code is injective on strings that differ only in a character it escapes
#guard labelSafe "a:b" != labelSafe "a_b"
#guard labelSafe "a_b" != labelSafe "a_3a_b"

-- two fresh reifiers of the same triple become one
private def twoReifiers : Graph :=
  [ { s := .bnode "r1", p := reifiesIri, o := tt1 }
  , { s := .bnode "r1", p := ex "q", o := .iri (ex "a") }
  , { s := .bnode "r2", p := reifiesIri, o := tt1 }
  , { s := .bnode "r2", p := ex "q", o := .iri (ex "b") } ]

#guard (mergeReifiers twoReifiers).length == 3
#guard (reifierPairs (mergeReifiers twoReifiers)).length == 1
-- two reifiers of different triples stay two
#guard (mergeReifiers
  [ { s := .bnode "r1", p := reifiesIri, o := tt1 }
  , { s := .bnode "r2", p := reifiesIri, o := tt2 } ]).length == 2
-- a graph with no reifier is unchanged
#guard (mergeReifiers [ { s := .iri (ex "s"), p := ex "p", o := .iri (ex "o") } ]).length == 1

-- nested: r1 and r2 reify the same inner triple; the outer triples differ
-- only by those two names, so merging the inner pair merges the outer pair
private def nestedGraph : Graph :=
  [ { s := .bnode "i1", p := reifiesIri, o := tt1 }
  , { s := .bnode "i2", p := reifiesIri, o := tt1 }
  , { s := .bnode "o1", p := reifiesIri, o := .tripleTerm (.bnode "i1") (ex "r") (.iri (ex "z")) }
  , { s := .bnode "o2", p := reifiesIri, o := .tripleTerm (.bnode "i2") (ex "r") (.iri (ex "z")) } ]

#guard (reifierPairs (mergeReifiers nestedGraph)).length == 2
#guard (mergeReifiers nestedGraph).length == 2

end L4Factoidal.RML
