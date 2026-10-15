/-
L4Factoidal.Syntax.NestedTermTests — build-time `#guard`s for triple terms nested deep
(https://github.com/danbri/factoidal/issues/867).

Five functions run as loops since issue 867: `readObject12` (`readObject12Down`, the term
reader of the N-Triples and N-Quads 1.2 readers), `Term.joinKey` (`Term.joinKeyLoop`), the
hash of a term (`Term.hashDown`, the instance `instHashableTermLoop`), `Term.toNTriples`
(`Term.toNTriplesLoop`) and `Term.lowerTags` (`Term.lowerTagsLoop`). Each equality with its
specification is a theorem (`readObject12_eq_loop`, `Term.joinKey_eq_fast`, `Term.hashFast_eq`,
`Term.toNTriples_eq_fast`, `Term.lowerTags_eq_fast`).
A guard that compares a specification with its `@[csimp]` loop compares the loop with itself,
because the compiler runs the loop for both (skills/lean4-proof-patterns, section 9b), so the
guards below pin results that the specifications gave BEFORE the change: the tables hold the
messages and offsets of the readers, the texts of the writers, the hash and the join key of
terms, recorded from the library at commit 724fdd79 by a program that called the functions
directly. A table row that does not hold fails the build. The guards on deep terms compare
with texts and values that are built another way (a repeated string, a repeated `mixHash`). The
hash is the exception to the rule above: the derived instance `instHashableTerm` is still in the
library, a different function from the loop, and a guard compares them.
-/

import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.RDF.DatasetNormalize

namespace L4Factoidal.Syntax.NestedTermTests

open L4Factoidal.RDF L4Factoidal.Syntax

/-! ### Helpers -/

def showTerm (t : Term) : String :=
  match Term.toNTriples .rdf12 t with
  | .ok s => s
  | .error e => s!"<<{e}>>"

def showObj : Except ParseError (Term × Nat × List Char) → String
  | .error e => s!"error({e.msg},{e.pos})"
  | .ok (t, p, r) => s!"ok({showTerm t}|{p}|{String.ofList r})"

def showE (e : ParseError) : String := s!"error({e.msg},{e.pos})"

def showNT (mode : Mode) (d : String) : String :=
  match parseNTriples d mode with
  | .error e => showE e
  | .ok g =>
      match Graph.toNTriples g .rdf12 with
      | .ok s => s!"ok({g.length};{s.quote})"
      | .error m => s!"ok({g.length};writer-error {m})"

def showNQ (mode : Mode) (d : String) : String :=
  match parseNQuads d mode with
  | .error e => showE e
  | .ok ds =>
      match Dataset.toNQuads ds .rdf12 with
      | .ok s => s!"ok({s.quote})"
      | .error m => s!"ok(writer-error {m})"

def showNQF (mode : Mode) (d : String) : String :=
  match parseNQuadsFast d mode with
  | .error e => showE e
  | .ok ds =>
      match Dataset.toNQuads ds .rdf12 with
      | .ok s => s!"ok({s.quote})"
      | .error m => s!"ok(writer-error {m})"

def showTT (mode : Mode) (t : Term) : String :=
  match Term.toNTriples mode t with
  | .ok s => s!"ok({s.quote})"
  | .error m => s!"error({m})"

/-- The term that `readObject12` reads from `d`, with a fuel that no table row exhausts. -/
def termOf (d : String) : Option Term :=
  match readObject12 200 0 d.toList with
  | .ok (t, _, _) => some t
  | .error _ => none

/-! ### The object reader: 38 texts at 8 fuels

`readObject12 f 7 text`, for `f` = 0, 1, 2, 3, 4, 5, 8 and 100: the term and the text left
after it, or the message and the offset of the error. The fuel counts the levels of nesting
that the reader may open, so the rows at 0 to 5 include the error "triple-term nesting too
deep" at the offset where the next object would begin. -/

def objectTable : List (String × List String) := [
  ("<http://a/o> .", ["error(triple-term nesting too deep,7)",
    "ok(<http://a/o>|19| .)",
    "ok(<http://a/o>|19| .)",
    "ok(<http://a/o>|19| .)",
    "ok(<http://a/o>|19| .)",
    "ok(<http://a/o>|19| .)",
    "ok(<http://a/o>|19| .)",
    "ok(<http://a/o>|19| .)"]),
  ("_:b .", ["error(triple-term nesting too deep,7)",
    "ok(_:b|10| .)",
    "ok(_:b|10| .)",
    "ok(_:b|10| .)",
    "ok(_:b|10| .)",
    "ok(_:b|10| .)",
    "ok(_:b|10| .)",
    "ok(_:b|10| .)"]),
  ("\"x\" .", ["error(triple-term nesting too deep,7)",
    "ok(\"x\"|10| .)",
    "ok(\"x\"|10| .)",
    "ok(\"x\"|10| .)",
    "ok(\"x\"|10| .)",
    "ok(\"x\"|10| .)",
    "ok(\"x\"|10| .)",
    "ok(\"x\"|10| .)"]),
  ("\"x\"@EN .", ["error(triple-term nesting too deep,7)",
    "ok(\"x\"@EN|13| .)",
    "ok(\"x\"@EN|13| .)",
    "ok(\"x\"@EN|13| .)",
    "ok(\"x\"@EN|13| .)",
    "ok(\"x\"@EN|13| .)",
    "ok(\"x\"@EN|13| .)",
    "ok(\"x\"@EN|13| .)"]),
  ("\"x\"@en--ltr .", ["error(triple-term nesting too deep,7)",
    "ok(\"x\"@en--ltr|18| .)",
    "ok(\"x\"@en--ltr|18| .)",
    "ok(\"x\"@en--ltr|18| .)",
    "ok(\"x\"@en--ltr|18| .)",
    "ok(\"x\"@en--ltr|18| .)",
    "ok(\"x\"@en--ltr|18| .)",
    "ok(\"x\"@en--ltr|18| .)"]),
  ("\"x\"^^<http://a/dt> .", ["error(triple-term nesting too deep,7)",
    "ok(\"x\"^^<http://a/dt>|25| .)",
    "ok(\"x\"^^<http://a/dt>|25| .)",
    "ok(\"x\"^^<http://a/dt>|25| .)",
    "ok(\"x\"^^<http://a/dt>|25| .)",
    "ok(\"x\"^^<http://a/dt>|25| .)",
    "ok(\"x\"^^<http://a/dt>|25| .)",
    "ok(\"x\"^^<http://a/dt>|25| .)"]),
  ("<<( <http://a/s> <http://a/p> <http://a/o> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "ok(<<( <http://a/s> <http://a/p> <http://a/o> )>>|53| .)",
    "ok(<<( <http://a/s> <http://a/p> <http://a/o> )>>|53| .)",
    "ok(<<( <http://a/s> <http://a/p> <http://a/o> )>>|53| .)",
    "ok(<<( <http://a/s> <http://a/p> <http://a/o> )>>|53| .)",
    "ok(<<( <http://a/s> <http://a/p> <http://a/o> )>>|53| .)",
    "ok(<<( <http://a/s> <http://a/p> <http://a/o> )>>|53| .)"]),
  ("<<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \"q\\\"r\\n\" )>> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,58)",
    "ok(<<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \"q\\\"r\\n\" )>> )>>|74| .)",
    "ok(<<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \"q\\\"r\\n\" )>> )>>|74| .)",
    "ok(<<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \"q\\\"r\\n\" )>> )>>|74| .)",
    "ok(<<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \"q\\\"r\\n\" )>> )>>|74| .)",
    "ok(<<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \"q\\\"r\\n\" )>> )>>|74| .)"]),
  ("<<(<http://a/s><http://a/p>\"x\")>>.", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,34)",
    "ok(<<( <http://a/s> <http://a/p> \"x\" )>>|40|.)",
    "ok(<<( <http://a/s> <http://a/p> \"x\" )>>|40|.)",
    "ok(<<( <http://a/s> <http://a/p> \"x\" )>>|40|.)",
    "ok(<<( <http://a/s> <http://a/p> \"x\" )>>|40|.)",
    "ok(<<( <http://a/s> <http://a/p> \"x\" )>>|40|.)",
    "ok(<<( <http://a/s> <http://a/p> \"x\" )>>|40|.)"]),
  ("<<(  <http://a/s>\t<http://a/p>  <<(\t<http://a/s> <http://a/p> \"x\"@en--rtl  )>>   )>>  .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,39)",
    "error(triple-term nesting too deep,69)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"@en--rtl )>> )>>|91|  .)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"@en--rtl )>> )>>|91|  .)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"@en--rtl )>> )>>|91|  .)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"@en--rtl )>> )>>|91|  .)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"@en--rtl )>> )>>|91|  .)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"^^<http://a/dt> )>> )>> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(triple-term nesting too deep,97)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"^^<http://a/dt> )>> )>> )>>|127| .)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"^^<http://a/dt> )>> )>> )>>|127| .)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"^^<http://a/dt> )>> )>> )>>|127| .)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"^^<http://a/dt> )>> )>> )>>|127| .)"]),
  ("<<( <http://a/s> <http://a/p> <http://a/o> ) .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)"]),
  ("<<( <http://a/s> <http://a/p> <http://a/o> )> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)"]),
  ("<<( <http://a/s> <http://a/p> <http://a/o> )>", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)",
    "error(expected ')>>',50)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> )> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> ", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)"]),
  ("<<( <http://a/s> <http://a/p> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> )>> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)"]),
  ("<<( <http://a/s> )>> .", ["error(triple-term nesting too deep,7)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)"]),
  ("<<( <<( <http://a/s> <http://a/p> <http://a/o> )>> <http://a/p> <http://a/o> )>> .", ["error(triple-term nesting too deep,7)",
    "error(invalid character in IRIREF,12)",
    "error(invalid character in IRIREF,12)",
    "error(invalid character in IRIREF,12)",
    "error(invalid character in IRIREF,12)",
    "error(invalid character in IRIREF,12)",
    "error(invalid character in IRIREF,12)",
    "error(invalid character in IRIREF,12)"]),
  ("<<( \"x\" <http://a/p> <http://a/o> )>> .", ["error(triple-term nesting too deep,7)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)"]),
  ("<<( <http://a/s> _:p <http://a/o> )>> .", ["error(triple-term nesting too deep,7)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)",
    "error(expected '<' (IRIREF),24)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> \"p\" <http://a/o> )>> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(expected '<' (IRIREF),54)",
    "error(expected '<' (IRIREF),54)",
    "error(expected '<' (IRIREF),54)",
    "error(expected '<' (IRIREF),54)",
    "error(expected '<' (IRIREF),54)",
    "error(expected '<' (IRIREF),54)"]),
  ("<< <http://a/s> <http://a/p> <http://a/o> >> .", ["error(triple-term nesting too deep,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)"]),
  ("<<( <http://a/s> <http://a/p> << <http://a/s> <http://a/p> <http://a/o> >> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,37)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,37)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,37)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,37)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,37)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,37)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> << <http://a/s> <http://a/p> <http://a/o> >> )>> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,67)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,67)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,67)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,67)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,67)"]),
  ("<<", ["error(triple-term nesting too deep,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,7)"]),
  ("<<(", ["error(triple-term nesting too deep,7)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),10)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),10)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),10)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),10)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),10)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),10)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),10)"]),
  ("<<( ", ["error(triple-term nesting too deep,7)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),11)"]),
  ("", ["error(triple-term nesting too deep,7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)"]),
  ("?", ["error(triple-term nesting too deep,7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),7)"]),
  ("<<( <http://a/s> <http://a/p> ? )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),37)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> ? )>> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),67)"]),
  ("<<( <http://a/s <http://a/p> <http://a/o> )>> .", ["error(triple-term nesting too deep,7)",
    "error(invalid character in IRIREF,22)",
    "error(invalid character in IRIREF,22)",
    "error(invalid character in IRIREF,22)",
    "error(invalid character in IRIREF,22)",
    "error(invalid character in IRIREF,22)",
    "error(invalid character in IRIREF,22)",
    "error(invalid character in IRIREF,22)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"unterminated )>> )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(unterminated string literal (expected '\"'),90)",
    "error(unterminated string literal (expected '\"'),90)",
    "error(unterminated string literal (expected '\"'),90)",
    "error(unterminated string literal (expected '\"'),90)",
    "error(unterminated string literal (expected '\"'),90)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> \n )>> .", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)",
    "error(expected ')>>',84)"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>>\t\t )>>\t.", ["error(triple-term nesting too deep,7)",
    "error(triple-term nesting too deep,37)",
    "error(triple-term nesting too deep,67)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> )>>|89|\t.)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> )>>|89|\t.)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> )>>|89|\t.)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> )>>|89|\t.)",
    "ok(<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <http://a/o> )>> )>>|89|\t.)"])
]

#guard objectTable.all fun (d, want) =>
  [0, 1, 2, 3, 4, 5, 8, 100].map (fun f => showObj (readObject12 f 7 d.toList)) == want

/-! ### The readers and writers on whole documents: 31 documents

For each document: `parseNTriples` in RDF 1.2 mode and then `Graph.toNTriples` (the number of
triples and the text), `parseNTriples` in RDF 1.1 mode, `parseNQuads` in 1.2 and in 1.1 mode
and then `Dataset.toNQuads`, and `parseNQuadsFast` in 1.2 mode; or the error with its offset. -/

def documentTable : List (String × List String) := [
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> .\n", ["ok(1;\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n\")"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"@EN--rtl )>> )>> )>> .\n", ["ok(1;\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\"@EN--rtl )>> )>> )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\"@EN--rtl )>> )>> )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\"@EN--rtl )>> )>> )>> .\\n\")"]),
  ("<http://a/s> <http://a/p> <<( _:b <http://a/p> <<( <http://a/s> <http://a/p> \"q\\\"r\\n\"^^<http://a/dt> )>> )>> .\n_:c <http://a/p> <<( <http://a/s> <http://a/p> _:d )>> .\n", ["ok(2;\"<http://a/s> <http://a/p> <<( _:b <http://a/p> <<( <http://a/s> <http://a/p> \\\"q\\\\\\\"r\\\\n\\\"^^<http://a/dt> )>> )>> .\\n_:c <http://a/p> <<( <http://a/s> <http://a/p> _:d )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( _:b <http://a/p> <<( <http://a/s> <http://a/p> \\\"q\\\\\\\"r\\\\n\\\"^^<http://a/dt> )>> )>> .\\n_:c <http://a/p> <<( <http://a/s> <http://a/p> _:d )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( _:b <http://a/p> <<( <http://a/s> <http://a/p> \\\"q\\\\\\\"r\\\\n\\\"^^<http://a/dt> )>> )>> .\\n_:c <http://a/p> <<( <http://a/s> <http://a/p> _:d )>> .\\n\")"]),
  ("<http://a/s> <http://a/p> <<(  <http://a/s>\t<http://a/p>   <<(\t<http://a/s> <http://a/p> \"x\"  )>>  )>>   .\n", ["ok(1;\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> )>> .\\n\")"]),
  ("<http://a/s> <http://a/p> <<(<http://a/s> <http://a/p> \"x\")>> .\n", ["ok(1;\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n\")"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> <http://a/g> .\n", ["error(expected '.' terminator,64)",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> <http://a/g> .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> <http://a/g> .\\n\")"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> )>> _:g .\n", ["error(expected '.' terminator,98)",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> )>> _:g .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> )>> _:g .\\n\")"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> .\n<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"y\" )>> .\n# c\n\n<http://a/s> <http://a/p> \"z\" .\n", ["ok(3;\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"y\\\" )>> .\\n<http://a/s> <http://a/p> \\\"z\\\" .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"y\\\" )>> .\\n<http://a/s> <http://a/p> \\\"z\\\" .\\n\")",
    "error(invalid character in IRIREF,27)",
    "ok(\"<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\" )>> .\\n<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"y\\\" )>> .\\n<http://a/s> <http://a/p> \\\"z\\\" .\\n\")"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" ) .\n", ["error(expected ')>>',60)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',60)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',60)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )> .\n", ["error(expected ')>>',60)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',60)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',60)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>>\n", ["error(expected '.' terminator,63)",
    "error(invalid character in IRIREF,27)",
    "error(expected '.' terminator,63)",
    "error(invalid character in IRIREF,27)",
    "error(expected '.' terminator,63)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> .\n", ["error(expected ')>>',94)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',94)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',94)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> )> .\n", ["error(expected ')>>',94)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',94)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',94)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> )>> .\n", ["error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),56)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),56)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),56)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> )>> )>> .\n", ["error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)"]),
  ("<http://a/s> <http://a/p> <<( <<( <http://a/s> <http://a/p> \"x\" )>> <http://a/p> \"x\" )>> .\n", ["error(invalid character in IRIREF,31)",
    "error(invalid character in IRIREF,27)",
    "error(invalid character in IRIREF,31)",
    "error(invalid character in IRIREF,27)",
    "error(invalid character in IRIREF,31)"]),
  ("<http://a/s> <http://a/p> <<( \"x\" <http://a/p> \"x\" )>> .\n", ["error(expected subject (IRIREF or BLANK_NODE_LABEL),30)",
    "error(invalid character in IRIREF,27)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),30)",
    "error(invalid character in IRIREF,27)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),30)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> _:p \"x\" )>> .\n", ["error(expected '<' (IRIREF),43)",
    "error(invalid character in IRIREF,27)",
    "error(expected '<' (IRIREF),43)",
    "error(invalid character in IRIREF,27)",
    "error(expected '<' (IRIREF),43)"]),
  ("<http://a/s> <http://a/p> << <http://a/s> <http://a/p> \"x\" >> .\n", ["error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,26)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,26)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,26)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> << <http://a/s> <http://a/p> \"x\" >> )>> .\n", ["error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,56)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,56)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,56)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> << <http://a/s> <http://a/p> \"x\" >> )>> )>> .\n", ["error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,86)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,86)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,86)"]),
  ("<http://a/s> <http://a/p> <<", ["error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,26)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,26)",
    "error(invalid character in IRIREF,27)",
    "error(legacy '<< >>' quoted triple is not RDF 1.2 syntax,26)"]),
  ("<http://a/s> <http://a/p> <<(", ["error(expected subject (IRIREF or BLANK_NODE_LABEL),29)",
    "error(invalid character in IRIREF,27)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),29)",
    "error(invalid character in IRIREF,27)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),29)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> ", ["error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> ? )>> .\n", ["error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),56)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),56)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),56)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> ? )>> )>> .\n", ["error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)",
    "error(invalid character in IRIREF,27)",
    "error(expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term),86)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"unterminated )>> .\n", ["error(unescaped newline in string literal,75)",
    "error(invalid character in IRIREF,27)",
    "error(unescaped newline in string literal,75)",
    "error(invalid character in IRIREF,27)",
    "error(unescaped newline in string literal,75)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> . junk\n", ["error(expected subject (IRIREF or BLANK_NODE_LABEL),66)",
    "error(invalid character in IRIREF,27)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),66)",
    "error(invalid character in IRIREF,27)",
    "error(expected subject (IRIREF or BLANK_NODE_LABEL),66)"]),
  ("<http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\" )>> \n )>> .\n", ["error(expected ')>>',94)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',94)",
    "error(invalid character in IRIREF,27)",
    "error(expected ')>>',94)"]),
  ("<http://a/s> <http://a/p> \"d\"@en--ltr .\n", ["ok(1;\"<http://a/s> <http://a/p> \\\"d\\\"@en--ltr .\\n\")",
    "ok(1;\"<http://a/s> <http://a/p> \\\"d\\\"@en--ltr .\\n\")",
    "ok(\"<http://a/s> <http://a/p> \\\"d\\\"@en--ltr .\\n\")",
    "ok(\"<http://a/s> <http://a/p> \\\"d\\\"@en--ltr .\\n\")",
    "ok(\"<http://a/s> <http://a/p> \\\"d\\\"@en--ltr .\\n\")"]),
  ("<http://a/s> <http://a/p> \"d\"@EN--ltr <http://a/s> .\n", ["error(expected '.' terminator,38)",
    "error(expected '.' terminator,38)",
    "ok(\"<http://a/s> <http://a/p> \\\"d\\\"@EN--ltr <http://a/s> .\\n\")",
    "ok(\"<http://a/s> <http://a/p> \\\"d\\\"@EN--ltr <http://a/s> .\\n\")",
    "ok(\"<http://a/s> <http://a/p> \\\"d\\\"@EN--ltr <http://a/s> .\\n\")"])
]

#guard documentTable.all fun (d, want) =>
  [showNT .rdf12 d, showNT .rdf11 d, showNQ .rdf12 d, showNQ .rdf11 d, showNQF .rdf12 d] == want

/-! ### The writer, the hash and the join key on 14 terms

For each term: `Term.toNTriples` in RDF 1.2 and in RDF 1.1 mode (a triple term and a
directional literal are errors in RDF 1.1 mode), the hash, the text of the join key and the hash
of the join key. -/

def termTable : List (String × List String) := [
  ("<http://a/o> .", ["ok(\"<http://a/o>\")",
    "ok(\"<http://a/o>\")",
    "8732809600198315820",
    "ok(\"<http://a/o>\")",
    "8732809600198315820"]),
  ("_:b .", ["ok(\"_:b\")",
    "ok(\"_:b\")",
    "14532251648326466365",
    "ok(\"_:b\")",
    "14532251648326466365"]),
  ("\"x\\ty\\\\z\\\"\\n\" .", ["ok(\"\\\"x\\\\ty\\\\\\\\z\\\\\\\"\\\\n\\\"\")",
    "ok(\"\\\"x\\\\ty\\\\\\\\z\\\\\\\"\\\\n\\\"\")",
    "16166736122313722437",
    "ok(\"\\\"x\\\\ty\\\\\\\\z\\\\\\\"\\\\n\\\"\")",
    "16166736122313722437"]),
  ("\"x\"@EN .", ["ok(\"\\\"x\\\"@EN\")",
    "ok(\"\\\"x\\\"@EN\")",
    "12654457648059830671",
    "ok(\"\\\"x\\\"@en\")",
    "11046329921231523505"]),
  ("\"x\"@en--ltr .", ["ok(\"\\\"x\\\"@en--ltr\")",
    "error(RDF 1.2 directional literal requires mode .rdf12)",
    "9240642286959074817",
    "ok(\"\\\"x\\\"@en--ltr\")",
    "9240642286959074817"]),
  ("\"x\"@fr--rtl .", ["ok(\"\\\"x\\\"@fr--rtl\")",
    "error(RDF 1.2 directional literal requires mode .rdf12)",
    "16154356133416141454",
    "ok(\"\\\"x\\\"@fr--rtl\")",
    "16154356133416141454"]),
  ("\"x\"^^<http://a/dt> .", ["ok(\"\\\"x\\\"^^<http://a/dt>\")",
    "ok(\"\\\"x\\\"^^<http://a/dt>\")",
    "2178375097982463206",
    "ok(\"\\\"x\\\"^^<http://a/dt>\")",
    "2178375097982463206"]),
  ("\"x\"^^<http://www.w3.org/2001/XMLSchema#string> .", ["ok(\"\\\"x\\\"\")",
    "ok(\"\\\"x\\\"\")",
    "8312788614569023568",
    "ok(\"\\\"x\\\"\")",
    "8312788614569023568"]),
  ("\"<a  b='1'/>\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral> .", ["ok(\"\\\"<a  b='1'/>\\\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral>\")",
    "ok(\"\\\"<a  b='1'/>\\\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral>\")",
    "1333030609920413699",
    "ok(\"\\\"<a b=\\\\\\\"1\\\\\\\"></a>\\\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral>\")",
    "12044940314552929710"]),
  ("<<( <http://a/s> <http://a/p> <http://a/o> )>> .", ["ok(\"<<( <http://a/s> <http://a/p> <http://a/o> )>>\")",
    "error(RDF 1.2 triple term requires mode .rdf12)",
    "12131285083262620389",
    "ok(\"<<( <http://a/s> <http://a/p> <http://a/o> )>>\")",
    "12131285083262620389"]),
  ("<<( _:b <http://a/p> \"x\"@EN )>> .", ["ok(\"<<( _:b <http://a/p> \\\"x\\\"@EN )>>\")",
    "error(RDF 1.2 triple term requires mode .rdf12)",
    "13288748515673953220",
    "ok(\"<<( _:b <http://a/p> \\\"x\\\"@en )>>\")",
    "16294478112122863863"]),
  ("<<( <http://a/s> <http://a/p> \"x\"@en--ltr )>> .", ["ok(\"<<( <http://a/s> <http://a/p> \\\"x\\\"@en--ltr )>>\")",
    "error(RDF 1.2 triple term requires mode .rdf12)",
    "16271508862075559149",
    "ok(\"<<( <http://a/s> <http://a/p> \\\"x\\\"@en--ltr )>>\")",
    "16271508862075559149"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \"x\"@EN--rtl )>> )>> .", ["ok(\"<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\"@EN--rtl )>> )>>\")",
    "error(RDF 1.2 triple term requires mode .rdf12)",
    "15483159445457347648",
    "ok(\"<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> \\\"x\\\"@en--rtl )>> )>>\")",
    "18269412113221777653"]),
  ("<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \"<a  b='1'/>\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral> )>> )>> )>> .", ["ok(\"<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \\\"<a  b='1'/>\\\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral> )>> )>> )>>\")",
    "error(RDF 1.2 triple term requires mode .rdf12)",
    "568093988719086980",
    "ok(\"<<( <http://a/s> <http://a/p> <<( <http://a/s> <http://a/p> <<( _:b <http://a/p> \\\"<a b=\\\\\\\"1\\\\\\\"></a>\\\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral> )>> )>> )>>\")",
    "16181699609238892708"])
]

#guard termTable.all fun (d, want) =>
  match termOf d with
  | none => false
  | some t =>
      [showTT .rdf12 t, showTT .rdf11 t, toString (hash t), showTT .rdf12 t.joinKey,
       toString (hash t.joinKey)] == want

/-! ### Deep terms

A term nested `n` deep, with the literal `"x"` at the bottom, built by a repeated string and
by a repeated constructor, and the values that a repeated step gives. -/

def subj : Subject := .iri ⟨"http://a/s", rfl⟩
def pred : WfIri := ⟨"http://a/p", rfl⟩
def leaf : Term := .literal (Literal.string "x")

/-- `<<( s p <<( s p ... "x" )>> )>>`, `n` triple terms. -/
def deepText (n : Nat) : String :=
  String.join (List.replicate n "<<( <http://a/s> <http://a/p> ") ++ "\"x\"" ++
    String.join (List.replicate n " )>>")

def deepTerm (n : Nat) : Term := Nat.repeat (fun t => Term.tripleTerm subj pred t) n leaf

/-- The same with a language tag in capitals at the bottom, and with the tag in lower case. -/
def deepTagged (n : Nat) : Term :=
  Nat.repeat (fun t => Term.tripleTerm subj pred t) n (.literal (Literal.langString "x" "EN"))
def deepLowered (n : Nat) : Term :=
  Nat.repeat (fun t => Term.tripleTerm subj pred t) n (.literal (Literal.langString "x" "en"))

def deepLine (n : Nat) : String := "<http://a/s> <http://a/p> " ++ deepText n ++ " .\n"

def deepLineGraph (n : Nat) : String :=
  "<http://a/s> <http://a/p> " ++ deepText n ++ " <http://a/g> .\n"

-- The reader reads the line, and the writer writes the line it read: 5,000 levels.
#guard showNT .rdf12 (deepLine 5000) == s!"ok(1;{(deepLine 5000).quote})"
#guard showNQ .rdf12 (deepLine 5000) == s!"ok({(deepLine 5000).quote})"
#guard showNQF .rdf12 (deepLine 5000) == s!"ok({(deepLine 5000).quote})"
#guard (match parseNTriples (deepLine 5000) .rdf12 with
        | .ok [t] => t.o == deepTerm 5000
        | _ => false)

-- With a graph name at the end of the line: the same term.
#guard showNQ .rdf12 (deepLineGraph 3000) == s!"ok({(deepLineGraph 3000).quote})"

-- The text of a term: the writer in RDF 1.2 mode writes `deepText`, in RDF 1.1 mode it is the
-- error of a triple term, and a term with no triple term is the same in both modes.
#guard showTT .rdf12 (deepTerm 5000) == s!"ok({(deepText 5000).quote})"
#guard showTT .rdf11 (deepTerm 5000) == "error(RDF 1.2 triple term requires mode .rdf12)"
#guard showTT .rdf11 (deepTerm 0) == "ok(\"\\\"x\\\"\")"
#guard showTT .rdf12 (deepTerm 0) == "ok(\"\\\"x\\\"\")"

-- The hash: `mixHash` of the part of each level and of the hash of the term below it. 100,000
-- levels, no frame.
#guard hash (deepTerm 100000) ==
  Nat.repeat (fun h => mixHash (mixHash (mixHash 3 (hash subj)) (hash pred)) h) 100000 (hash leaf)
#guard hash (deepTerm 0) == hash leaf
#guard hash (deepTerm 1) == mixHash (mixHash (mixHash 3 (hash subj)) (hash pred)) (hash leaf)

-- The loop and the derived function (`deriving Hashable`, still in the library as
-- `instHashableTerm`) give the same value on the terms of the table and on a term nested 3,000
-- deep, with a language tag at the bottom.
#guard termTable.all fun (d, _) =>
  match termOf d with
  | none => false
  | some t => hash t == @Hashable.hash Term instHashableTerm t
#guard hash (deepTerm 3000) == @Hashable.hash Term instHashableTerm (deepTerm 3000)
#guard hash (deepTagged 3000) == @Hashable.hash Term instHashableTerm (deepTagged 3000)

-- The join key of a term whose literal has a language tag in capitals: the tag is lowered at the
-- bottom, and the levels above it are kept. 3,000 levels.
#guard (deepTagged 3000).joinKey == deepLowered 3000
#guard (deepTagged 0).joinKey == deepLowered 0
#guard (deepTerm 3000).joinKey == deepTerm 3000
#guard ((deepTagged 3000).joinKey != deepTagged 3000)

-- The language tags of a term, inside the triple terms too: the tag is lowered at the bottom and
-- the levels above it are kept. The terms of the table are parsed from their text, and the
-- results are written here by hand.
def lowerCases : List (String × String) := [
  ("<http://a/o> .", "<http://a/o>"),
  ("_:b .", "_:b"),
  ("\"x\" .", "\"x\""),
  ("\"x\"@EN .", "\"x\"@en"),
  ("\"x\"@Fr-CA--rtl .", "\"x\"@fr-ca--rtl"),
  ("\"x\"^^<http://a/DT> .", "\"x\"^^<http://a/DT>"),
  ("<<( _:b <http://a/p> \"x\"@FR-ca )>> .", "<<( _:b <http://a/p> \"x\"@fr-ca )>>"),
  ("<<( <http://a/s> <http://a/P> <<( <http://a/s> <http://a/p> \"X\"@EN--ltr )>> )>> .",
   "<<( <http://a/s> <http://a/P> <<( <http://a/s> <http://a/p> \"X\"@en--ltr )>> )>>")
]
#guard lowerCases.all fun (d, want) =>
  match termOf d with
  | none => false
  | some t => showTerm t.lowerTags == want
#guard (deepTagged 3000).lowerTags == deepLowered 3000
#guard (deepTagged 0).lowerTags == deepLowered 0
#guard (deepLowered 3000).lowerTags == deepLowered 3000
#guard (deepTerm 3000).lowerTags == deepTerm 3000
#guard hash (deepTagged 100000).lowerTags == hash (deepLowered 100000)
#guard (Triple.lowerTags { s := subj, p := pred, o := deepTagged 2000 }).o == deepLowered 2000

-- A term with a deep triple term in a hash map and in a triple key: the join key of the triple
-- is the key of the term and the map finds it again. 3,000 levels.
#guard (let k := (subj, pred, (deepTagged 3000).joinKey)
        let m : Std.HashMap (Subject × WfIri × Term) Nat := Std.HashMap.emptyWithCapacity.insert k 1
        m.get? (subj, pred, (deepLowered 3000)) == some 1)

#print axioms readObject12_eq_loop
#print axioms Term.joinKey_eq_fast
#print axioms Term.hashFast_eq
#print axioms Term.toNTriples_eq_fast
#print axioms Term.lowerTags_eq_fast

end L4Factoidal.Syntax.NestedTermTests
