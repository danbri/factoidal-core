/-
L4Factoidal.RDF.Collections — RDF lists (`rdf:first`/`rdf:rest`) and RDF
containers (`rdf:_n`) of one graph.

https://github.com/danbri/factoidal/issues/1051 item 6 (Jena `RDFList`,
`Seq`, `Bag`, `Alt`; RDFLib `Collection`, `Graph.items`).

## Lists

RDF 1.2 Schema, section 5.2 (RDF collections) and RDF 1.2 Semantics, the
collection vocabulary: a list is `rdf:nil`, or a node with one `rdf:first`
(the item) and one `rdf:rest` (the rest of the list). `listItemsBy` walks a
list from its head. It refuses a list that is not well formed, with the
reason:

  * `no-first` / `no-rest`: a node other than `rdf:nil` with no `rdf:first`
    or no `rdf:rest`;
  * `branch`: a node with two or more `rdf:first` or `rdf:rest` objects;
  * `cycle`: a node that comes again on the walk.

The walk reads the graph only through two lookups (`firsts`, `rests`), so a
caller gives it an index (`Wasm/Ops/Collections.lean` uses the dataset
indexes) and the cost is one lookup per item. `listTriples` builds the
triples of a new list over given blank-node labels; `listItems` of the result
gives the items back (a `#guard`).

## Containers

RDF 1.2 Schema, section 5.1: a container is a resource with the members
`rdf:_1`, `rdf:_2`, ... `containerMembers` gives the members of a resource
in the order of `n`, members of one `n` in graph order. A gap in the
numbering is kept (the ordinals are in the answer). `containerKind` gives
`rdf:Bag`, `rdf:Seq` or `rdf:Alt` when the resource has that type.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.TermIdentity
import L4Factoidal.RDF.TermJson
import L4Factoidal.RDF.VocabularyTable
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RDF

open L4Factoidal.RDFS

/-- Why a list is not well formed. -/
inductive ListFault where
  | noFirst | noRest | branch | cycle
  deriving DecidableEq, Repr

/-- The reason word of a fault. -/
def ListFault.word : ListFault → String
  | .noFirst => "no-first"
  | .noRest => "no-rest"
  | .branch => "branch"
  | .cycle => "cycle"

def rdfNilTerm : Term := .iri rdfNil

/-- Walk a list from `node`; `fuel` bounds the number of nodes. -/
def listWalk (firsts rests : Term → List Term) :
    Nat → List Term → Array Term → Term → Except (ListFault × Term) (List Term)
  | 0, _, _, node => .error (.cycle, node)
  | fuel + 1, seen, acc, node =>
    if node.sameTerm rdfNilTerm then .ok acc.toList
    else if seen.any (·.sameTerm node) then .error (.cycle, node)
    else
      match firsts node, rests node with
      | [f], [r] => listWalk firsts rests fuel (node :: seen) (acc.push f) r
      | [], _ => .error (.noFirst, node)
      | _, [] => .error (.noRest, node)
      | _, _ => .error (.branch, node)

/-- The items of the list at `head`, with `bound` an upper bound of its
number of nodes (the number of `rdf:rest` triples of the graph, plus one). -/
def listItemsBy (firsts rests : Term → List Term) (bound : Nat) (head : Term) :
    Except (ListFault × Term) (List Term) :=
  listWalk firsts rests bound [] #[] head

/-- The objects of `(node, p, ?)` in `g`. -/
def objectsIn (g : Graph) (p : WfIri) (node : Term) : List Term :=
  g.filterMap fun t => if t.p == p && t.s.toTerm.sameTerm node then some t.o else none

/-- The items of the list at `head` in `g` (the specification form, by scans). -/
def listItems (g : Graph) (head : Term) : Except (ListFault × Term) (List Term) :=
  listItemsBy (objectsIn g rdfFirst) (objectsIn g rdfRest) (g.length + 1) head

/-- The triples of a list of `items` over the node labels `labels` (one label
per item; extra labels are not used), and its head. The empty list is
`rdf:nil` with no triple. -/
def listTriples : List BNodeId → List Term → Term × List Triple
  | _, [] => (rdfNilTerm, [])
  | [], _ :: _ => (rdfNilTerm, [])
  | b :: bs, x :: xs =>
    let (rest, ts) := listTriples bs xs
    (.bnode b, ⟨.bnode b, rdfFirst, x⟩ :: ⟨.bnode b, rdfRest, rest⟩ :: ts)

/-- The members of a resource, `(n, member)` sorted by `n` (stable). -/
def containerMembersOf (outs : List (WfIri × Term)) : List (Nat × Term) :=
  let ms := outs.filterMap fun (p, o) => (memberOrdinal? p.val).map (·, o)
  ms.mergeSort (fun a b => a.1 ≤ b.1)

/-- The members of `node` in `g`. -/
def containerMembers (g : Graph) (node : Term) : List (Nat × Term) :=
  containerMembersOf (g.filterMap fun t => if t.s.toTerm.sameTerm node then some (t.p, t.o) else none)

/-- The container kinds of RDF 1.2 Schema section 5.1. -/
def containerKindIris : List String :=
  [rdfNamespace ++ "Bag", rdfNamespace ++ "Seq", rdfNamespace ++ "Alt"]

/-- The first `rdf:Bag`, `rdf:Seq` or `rdf:Alt` among the types `types`. -/
def containerKindOf (types : List Term) : Option Term :=
  types.find? fun t => match t with | .iri i => containerKindIris.contains i.val | _ => false

/-! ### Build-time checks -/

private def ex (s : String) : WfIri :=
  match TermJson.iriOf? ("http://e/" ++ s) with | some i => i | none => rdfNil

private def items3 : List Term := [.iri (ex "a"), .bnode "x", .literal (Literal.string "c")]

#guard listItems (listTriples ["l0", "l1", "l2"] items3).2 (listTriples ["l0", "l1", "l2"] items3).1
  == .ok items3
#guard listItems [] rdfNilTerm == .ok []
#guard (listTriples [] []).1 == rdfNilTerm
-- A cycle: l0 -> l1 -> l0.
#guard (listItems [⟨.bnode "l0", rdfFirst, .bnode "x"⟩, ⟨.bnode "l0", rdfRest, .bnode "l1"⟩,
                   ⟨.bnode "l1", rdfFirst, .bnode "y"⟩, ⟨.bnode "l1", rdfRest, .bnode "l0"⟩]
          (.bnode "l0")).toOption.isNone
#guard (match listItems [⟨.bnode "l0", rdfFirst, .bnode "x"⟩, ⟨.bnode "l0", rdfRest, .bnode "l0"⟩]
          (.bnode "l0") with | .error (f, _) => f == .cycle | _ => false)
#guard (match listItems [⟨.bnode "l0", rdfRest, rdfNilTerm⟩] (.bnode "l0") with
          | .error (f, _) => f == .noFirst | _ => false)
#guard (match listItems [⟨.bnode "l0", rdfFirst, .bnode "x"⟩] (.bnode "l0") with
          | .error (f, _) => f == .noRest | _ => false)
#guard (match listItems [⟨.bnode "l0", rdfFirst, .bnode "x"⟩, ⟨.bnode "l0", rdfFirst, .bnode "y"⟩,
                         ⟨.bnode "l0", rdfRest, rdfNilTerm⟩] (.bnode "l0") with
          | .error (f, _) => f == .branch | _ => false)

private def mem (n : Nat) : WfIri :=
  match TermJson.iriOf? (memberIri n) with | some i => i | none => rdfNil

#guard containerMembers [⟨.iri (ex "c"), mem 2, .bnode "b"⟩, ⟨.iri (ex "c"), mem 1, .bnode "a"⟩,
                         ⟨.iri (ex "c"), ex "p", .bnode "z"⟩, ⟨.iri (ex "d"), mem 1, .bnode "q"⟩,
                         ⟨.iri (ex "c"), mem 10, .bnode "j"⟩]
          (.iri (ex "c")) == [(1, .bnode "a"), (2, .bnode "b"), (10, .bnode "j")]
#guard containerKindOf [.iri (ex "T"), .iri ⟨rdfNamespace ++ "Seq", rfl⟩] == some (.iri ⟨rdfNamespace ++ "Seq", rfl⟩)
#guard containerKindOf [.iri (ex "T")] == none

end L4Factoidal.RDF
