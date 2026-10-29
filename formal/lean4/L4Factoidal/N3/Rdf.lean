/-
L4Factoidal.N3.Rdf — an N3 graph that is an RDF graph, as RDF triples.

Notation3 Semantics § "Abstract syntax": "an RDF graph is a graph that does
not contain graph terms nor lists, does not have literals as subjects or
predicates, does not have variables as predicates, and for which U = ∅". The
one exception made here is lists: an N3 list in subject or object position is
written as the RDF collection Turtle writes for it (RDF 1.1 Turtle § 2.8,
`rdf:first`/`rdf:rest` cells ending in `rdf:nil`, the empty list being
`rdf:nil`). That is the reading the Turtle reader gives the same text, so a
Turtle document read by the N3 reader and converted here is the graph the
Turtle reader gives (`N3/Tests.lean`, and the differential run of
`Harness/N3Run.lean` over the Turtle suite).

`toRdf` refuses a graph term, a variable, a literal subject, and a predicate
that is not an IRI, with a message that names the term.

No `sorry`, no `axiom`, no `partial def`.
-/
import L4Factoidal.N3.Parser
import L4Factoidal.RDF.Graph

namespace L4Factoidal.N3

open L4Factoidal.RDF
open L4Factoidal.Syntax

def rdfFirstI : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#first", rfl⟩
def rdfRestI : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", rfl⟩
def rdfNilI : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", rfl⟩

/-- Conversion state: the label prefix for collection cells, the next cell
number, and the triples emitted. -/
structure RdfAcc where
  pfx : String
  n   : Nat
  out : Array Triple

mutual

/-- An N3 term in object position, as an RDF term. Fuel bounds the nesting of
lists (the reader's `maxNesting`); a list member loop is a tail call. -/
def termToRdf (fuel : Nat) (t : N3Term) (acc : RdfAcc) : Except String (Term × RdfAcc) :=
  match fuel, t with
  | 0, _ => .error "N3 list nesting too deep for conversion to RDF"
  | _ + 1, .iri i => .ok (.iri i, acc)
  | _ + 1, .bnode b => .ok (.bnode b, acc)
  | _ + 1, .lit l => .ok (.literal l, acc)
  | _ + 1, .triple s p o => .ok (.tripleTerm s p o, acc)
  | _ + 1, .var v => .error s!"the variable ?{v} is not an RDF term"
  | _ + 1, .graph _ => .error "a graph term is not an RDF term"
  | f + 1, .list xs => listToRdf f xs [] acc
termination_by (fuel, 0)

/-- The members of a list, converted in order (`cellsRev`: the cells so far,
newest first), then linked. -/
def listToRdf (fuel : Nat) (xs : List N3Term) (cellsRev : List (BNodeId × Term))
    (acc : RdfAcc) : Except String (Term × RdfAcc) :=
  match xs with
  | [] =>
      -- Link newest first: each cell's rest is the cell after it.
      let link : (Term × Array Triple) → (BNodeId × Term) → (Term × Array Triple) :=
        fun (restT, out) (node, first) =>
          (.bnode node, (out.push { s := .bnode node, p := rdfFirstI, o := first }).push
                          { s := .bnode node, p := rdfRestI, o := restT })
      let (head, out) := cellsRev.foldl link (.iri rdfNilI, acc.out)
      .ok (head, { acc with out := out })
  | x :: rest =>
      let node := acc.pfx ++ "l" ++ toString acc.n
      match termToRdf fuel x { acc with n := acc.n + 1 } with
      | .error e => .error e
      | .ok (e, acc1) => listToRdf fuel rest ((node, e) :: cellsRev) acc1
termination_by (fuel, xs.length + 1)

end

/-- An N3 term in subject position. -/
def subjectToRdf (t : N3Term) (acc : RdfAcc) : Except String (Subject × RdfAcc) :=
  match termToRdf (maxNesting + 2) t acc with
  | .error e => .error e
  | .ok (.iri i, acc1) => .ok (.iri i, acc1)
  | .ok (.bnode b, acc1) => .ok (.bnode b, acc1)
  | .ok (_, _) => .error "a literal subject is not RDF"

/-- One N3 triple as RDF triples (the triple, after the cells of its lists). -/
def tripleToRdf (acc : RdfAcc) (t : N3Triple) : Except String RdfAcc :=
  let (s, p, o) := t
  match subjectToRdf s acc with
  | .error e => .error e
  | .ok (s', acc1) =>
      match p with
      | .iri pi =>
          match termToRdf (maxNesting + 2) o acc1 with
          | .error e => .error e
          | .ok (o', acc2) => .ok { acc2 with out := acc2.out.push { s := s', p := pi, o := o' } }
      | _ => .error "a predicate that is not an IRI is not RDF"

/-- An N3 graph as an RDF graph (module header). `pfx` must be a label
prefix no label of the graph begins with: `N3Document.bnodePrefix`. -/
def toRdf (pfx : String) (g : N3Graph) : Except String Graph :=
  match g.foldlM tripleToRdf { pfx, n := 0, out := #[] } with
  | .error e => .error e
  | .ok acc => .ok acc.out.toList

/-- Read N3 text and convert it to an RDF graph. -/
def parseN3ToRdf (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except String Graph :=
  match parseN3 text base mode with
  | .error e => .error s!"{e.msg} (offset {e.pos})"
  | .ok d => toRdf (d.bnodePrefix ++ "c") d.triples

/-! ## Lists as collections, inside N3

`expandLists` writes every N3 list of a graph, at any depth, as the
`rdf:first`/`rdf:rest` collection of RDF 1.1 Turtle § 2.8, and keeps
everything else (graph terms, variables, literals in any position): the
reading that a generalized RDF serialization such as cwm's N-Triples output
gives a list. The cells of a list inside a graph term are triples of that
graph term. -/

/-- Expansion state: the label prefix, the next cell number. -/
structure ExpandAcc where
  pfx : String
  n   : Nat

mutual

/-- A term with its lists as collections; the cells go to `out`. -/
def expandTerm (fuel : Nat) (t : N3Term) (acc : ExpandAcc) (out : Array N3Triple) :
    Except String (N3Term × ExpandAcc × Array N3Triple) :=
  match fuel, t with
  | 0, _ => .error "N3 nesting too deep to expand lists"
  | f + 1, .list xs => expandList f xs [] acc out
  | f + 1, .graph ts =>
      match expandTriples f ts acc #[] with
      | .error e => .error e
      | .ok (acc1, inner) => .ok (.graph inner.toList, acc1, out)
  | _ + 1, t => .ok (t, acc, out)
termination_by (fuel, 0, 0)

def expandList (fuel : Nat) (xs : List N3Term) (cellsRev : List (BNodeId × N3Term))
    (acc : ExpandAcc) (out : Array N3Triple) : Except String (N3Term × ExpandAcc × Array N3Triple) :=
  match xs with
  | [] =>
      let link : (N3Term × Array N3Triple) → (BNodeId × N3Term) → (N3Term × Array N3Triple) :=
        fun (restT, o) (node, first) =>
          (.bnode node, (o.push (.bnode node, .iri rdfFirstI, first)).push (.bnode node, .iri rdfRestI, restT))
      let (head, out1) := cellsRev.foldl link (.iri rdfNilI, out)
      .ok (head, acc, out1)
  | x :: rest =>
      let node := acc.pfx ++ "e" ++ toString acc.n
      match expandTerm fuel x { acc with n := acc.n + 1 } out with
      | .error e => .error e
      | .ok (e, acc1, out1) => expandList fuel rest ((node, e) :: cellsRev) acc1 out1
termination_by (fuel, 1, xs.length)

def expandTriples (fuel : Nat) (ts : List N3Triple) (acc : ExpandAcc) (out : Array N3Triple) :
    Except String (ExpandAcc × Array N3Triple) :=
  match ts with
  | [] => .ok (acc, out)
  | (s, p, o) :: rest =>
      match expandTerm fuel s acc out with
      | .error e => .error e
      | .ok (s', acc1, out1) =>
      match expandTerm fuel p acc1 out1 with
      | .error e => .error e
      | .ok (p', acc2, out2) =>
      match expandTerm fuel o acc2 out2 with
      | .error e => .error e
      | .ok (o', acc3, out3) => expandTriples fuel rest acc3 (out3.push (s', p', o'))
termination_by (fuel, 1, ts.length)

end

/-- A graph with its lists as collections (section header). `pfx` must be a
label prefix that no label of the graph begins with. -/
def expandLists (pfx : String) (g : N3Graph) : Except String N3Graph :=
  match expandTriples (maxNesting + 2) g { pfx, n := 0 } #[] with
  | .error e => .error e
  | .ok (_, out) => .ok out.toList

end L4Factoidal.N3
