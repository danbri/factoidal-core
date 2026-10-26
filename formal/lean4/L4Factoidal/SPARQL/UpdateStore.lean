/-
L4Factoidal.SPARQL.UpdateStore — SPARQL 1.1 Update on a store that keeps quads
and records an update as one delta-log batch (SBM11 stage 5,
https://github.com/danbri/factoidal/issues/849 for the WHERE clause and
https://github.com/danbri/factoidal/issues/850 for blank nodes).

`SPARQL/Update.lean` is the reference semantics over a `Dataset` in memory.
`SPARQL/UpdateDelta.lean` translates the ground operations (INSERT DATA,
DELETE DATA, CLEAR of one graph, DROP, CREATE) to log entries. This module
adds what a disk-resident store needs for the rest:

  * WHERE clauses. The store evaluates the WHERE clause itself, on the
    overlaid generation, and gives this module the solution sequence. This
    module instantiates the templates from that sequence with the reference
    functions (`instQuads`, `redirectQuad`) and turns the quads into log
    entries: the removes first, then the adds, both from the same solution
    sequence (SPARQL 1.1 Update section 3.1.3). `applyModify` is this
    computation with one particular blank node supply
    (`UpdateStoreTheorems.applyModify_eq`).
  * Fresh blank nodes. INSERT DATA and INSERT templates create new blank nodes
    (sections 3.1.1 and 3.1.3). The label of each is drawn from a supply
    (`chooseGo`): the first label of the form `sbm11u<n>` that the store, the
    log and the request do not hold. The labels are written to the log batch,
    so replay and compaction give the same blank nodes.
  * Graph management with graph-wide forms and graphs that are read: CLEAR
    and DROP of the named graphs, ADD, COPY and MOVE, given the facts the store
    computes (which named graphs exist, the triples of a graph).

The store keeps every named graph of the dataset, also a graph with no triple
(RDF 1.1 Concepts section 4; 2026-10-15,
https://github.com/danbri/factoidal/issues/855), and a graph name can be a
blank node (https://github.com/danbri/factoidal/issues/856): a log entry names a
graph by a `DeltaGraphName`, and a log that holds a blank node graph name has DLOG
version 3. The functions below take `has` (does the graph of an IRI exist) and
`named` (the named graphs, IRIs and blank nodes) as parameters; the harness
computes them from the named graphs of the overlaid generation.

Nothing here does I/O. Every function over a list or over the nesting of a
triple term is a fold or a tail call. No `sorry`, no `axiom`, no
`native_decide`.
-/
import L4Factoidal.SPARQL.UpdateDelta

namespace L4Factoidal.SPARQL.UpdateStore

open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## 1. Fresh blank node labels

The supply is a counter. The label of counter value `n` is `sbm11u` followed by
the decimal digits of `n`. No parser or serialiser of this repository produces
a label with that prefix (`tests/sbm11/update_where.sh`, group `labels`, reads
blank nodes from each syntax and checks their labels), so a label of the supply
meets a label of a document only when the document was written from an earlier
store of this kind. The supply never relies on that: `chooseGo` tests each
candidate against everything the store holds and everything the request drew
before, and skips the candidate that is held. The store tests a label by a
dictionary lookup, which is I/O, so `Harness/Sbm11Update.lean` looks up the
candidates a block at a time and gives `chooseGo` the set of labels it found. -/

/-- The prefix of the blank node labels that updates create. -/
def freshPrefix : String := "sbm11u"

/-- The label of counter value `n`. -/
def freshLabel (n : Nat) : BNodeId := freshPrefix ++ toString n

/-- The first counter value `m` in `[n, n + fuel)` whose label `taken` does not
    hold. A tail call: a loop. -/
def chooseGo (taken : String → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n => if taken (freshLabel n) then chooseGo taken fuel (n + 1) else some n

/-- `k` labels in a row: each is the first free label at or after the counter,
    where free means "not taken, and not drawn earlier in this call". `acc`
    holds the labels drawn so far, newest first. -/
def drawMany (taken : String → Bool) (fuel : Nat) : Nat → Nat → List BNodeId → Option (List BNodeId)
  | 0, _, acc => some acc.reverse
  | k + 1, n, acc =>
    match chooseGo (fun l => taken l || acc.contains l) fuel n with
    | none => none
    | some m => drawMany taken fuel k (m + 1) (freshLabel m :: acc)

/-! ## 2. The blank nodes of INSERT DATA

A blank node label of INSERT DATA is scoped to the request: the label denotes
one node wherever the request uses it (W3C `insert-data-same-bnode`: two graph
blocks of one operation), and no label denotes a node that the store holds
(section 3.1.1). So the request's labels are collected, each gets one fresh
label, and every INSERT DATA quad is renamed through that table. -/

/-- The blank node labels of a term, innermost last, onto `acc`. A triple term
    nested `d` deep is `d` iterations. -/
def termBnodesGo (acc : List BNodeId) : Term → List BNodeId
  | .bnode b => b :: acc
  | .tripleTerm s _ o => termBnodesGo (match s with | .bnode b => b :: acc | .iri _ => acc) o
  | _ => acc

/-- The blank node labels of a triple, inside triple terms too. -/
def tripleBnodes (t : Triple) : List BNodeId :=
  termBnodesGo (match t.s with | .bnode b => [b] | .iri _ => []) t.o

/-- A triple term wrapped around `t`, innermost level first. -/
def wrapLevels : List (Subject × WfIri) → Term → Term
  | [], t => t
  | (s, p) :: rest, t => wrapLevels rest (.tripleTerm s p t)

/-- `Term.renameBnodes` as a loop over the nesting of triple terms. -/
def renameTermGo (f : BNodeId → BNodeId) (levels : List (Subject × WfIri)) : Term → Term
  | .tripleTerm s p o => renameTermGo f ((s.renameBnodes f, p) :: levels) o
  | t => wrapLevels levels (t.renameBnodes f)

def renameTriple (f : BNodeId → BNodeId) (t : Triple) : Triple :=
  { s := t.s.renameBnodes f, p := t.p, o := renameTermGo f [] t.o }

def renameQuad (f : BNodeId → BNodeId) (q : Quad) : Quad := (q.1, renameTriple f q.2)

/-- The quads of an INSERT DATA operation (`collectQuads`), renamed through `f`. -/
def insertDataQuads (f : BNodeId → BNodeId) (quads : QueryPattern) : List Quad :=
  (collectQuads none quads).map (renameQuad f)

/-- The blank node labels of the INSERT DATA operations of a request, in the
    order of the operations (a label may occur more than once). -/
def insertDataLabels (ops : List UpdateOp) : List BNodeId :=
  ops.flatMap fun op =>
    match op with
    | .insertData quads => (collectQuads none quads).flatMap fun q => tripleBnodes q.2
    | _ => []

/-- The label that a request label stands for: the table's entry, else the
    label itself. -/
def renameFrom (tbl : List (BNodeId × BNodeId)) (l : BNodeId) : BNodeId :=
  match tbl.find? (·.1 == l) with
  | some (_, fresh) => fresh
  | none => l

/-! ## The blank nodes of an INSERT template

A blank node of an INSERT template is a new node for each solution (section
3.1.3.2), so the store draws one fresh label per solution and per label of the
template. -/

/-- The blank node labels of a subject position of a triple pattern. -/
def subjectLabel : PatternSubject → List BNodeId → List BNodeId
  | .bnode b, acc => b :: acc
  | _, acc => acc

/-- The blank node labels of a list of pattern terms, triple terms included:
    a worklist, the first term first. -/
def termLabelsGo (acc : List BNodeId) : List PatternTerm → List BNodeId
  | [] => acc
  | .bnode b :: rest => termLabelsGo (b :: acc) rest
  | .tripleTerm s p o :: rest => termLabelsGo acc (s :: p :: o :: rest)
  | _ :: rest => termLabelsGo acc rest
termination_by ts => (ts.map (fun t => 3 * sizeOf t + 1)).sum
decreasing_by all_goals (simp_wf <;> (try simp only [List.map_cons, List.sum_cons]) <;> omega)

/-- The blank node labels of a basic graph pattern. -/
def bgpLabels (b : Bgp) : List BNodeId :=
  b.foldl (fun acc tp => termLabelsGo (subjectLabel tp.s acc) [tp.p, tp.o]) []

/-- The blank node labels of a template (`bgp`, `join`, `graph`), a worklist of
    patterns: a template with `n` triple patterns is `n` iterations. -/
def templateLabelsGo (acc : List BNodeId) : List QueryPattern → List BNodeId
  | [] => acc
  | .bgp b :: rest => templateLabelsGo (bgpLabels b ++ acc) rest
  | .join a b :: rest => templateLabelsGo acc (a :: b :: rest)
  | .graph _ inner :: rest => templateLabelsGo acc (inner :: rest)
  | _ :: rest => templateLabelsGo acc rest
termination_by ps => (ps.map (fun p => 3 * sizeOf p + 1)).sum
decreasing_by all_goals (simp_wf <;> (try simp only [List.map_cons, List.sum_cons]) <;> omega)

def templateLabels (p : QueryPattern) : List BNodeId := templateLabelsGo [] [p]

/-! ## 3. DELETE/INSERT and DELETE WHERE from a solution sequence

Section 3.1.3: the WHERE clause is evaluated once, on the state before the
operation; the DELETE template and the INSERT template are both instantiated
from that solution sequence; then the deletes are applied, then the inserts.
`fresh ix` is the blank node supply of solution number `ix` (section 3.1.3.2:
a blank node of the INSERT template is a new node for each solution). -/

/-- The quads the DELETE template removes: each solution instantiates it, a
    template triple with an unbound variable, a literal or triple-term subject
    or a predicate that is not an IRI is dropped (`instQuads`), and a triple of
    the default graph goes to the `WITH` graph. -/
def modifyDeleteQuads (withIri : Option WfIri) (deleteTmpl : Option QueryPattern)
    (sols : SolutionSeq) : List Quad :=
  match deleteTmpl with
  | none => []
  | some dt => (sols.flatMap fun mu => instQuads id mu none dt).map (redirectQuad withIri)

/-- The quads the INSERT template adds, solution `ix` with the blank node
    supply `fresh ix`. -/
def modifyInsertQuads (withIri : Option WfIri) (insertTmpl : Option QueryPattern)
    (fresh : Nat → String → BNodeId) (sols : SolutionSeq) : List Quad :=
  match insertTmpl with
  | none => []
  | some it =>
    sols.zipIdx.flatMap fun (mu, ix) => (instQuads (fresh ix) mu none it).map (redirectQuad withIri)

/-- The quads `DELETE WHERE` removes (section 3.1.3.3): the pattern is the
    template, after the rewrite that makes its blank nodes variables. -/
def deleteWhereQuads (sols : SolutionSeq) (p : QueryPattern) : List Quad :=
  let rewritten := p.rewriteBnodes
  sols.flatMap fun mu => instQuads id mu none rewritten

def addEntry (q : Quad) : DeltaEntry := .add q.2 (q.1.map DeltaGraphName.ofWf)
def removeEntry (q : Quad) : DeltaEntry := .remove q.2 (q.1.map DeltaGraphName.ofWf)

/-- The log entries of one DELETE/INSERT: every remove, then every add. -/
def changeEntries (dels adds : List Quad) : List DeltaEntry :=
  dels.map removeEntry ++ adds.map addEntry

/-! ## 4. Graph management

`has g` says that the named graph `g` exists in the state before the
operation; the harness computes it from the overlaid generation. -/

/-- The slot a graph reference names in a log entry: `some none` the default
    graph, `some (some g)` the named graph `g`; the forms `NAMED` and `ALL` name
    no one slot. -/
def slotOf : GraphRef → Option (Option DeltaGraphName)
  | .default => some none
  | .graph i => some (some (DeltaGraphName.ofWf i))
  | _ => none

/-- CLEAR (section 3.1.5): the triples go, the graphs stay. `named` are the
    named graphs the store holds, a graph with no triple and a graph named by a
    blank node included. -/
def clearEntries (silent : Bool) (named : List DeltaGraphName) (has : WfIri → Bool) :
    GraphRef → Except UpdateError (List DeltaEntry)
  | .default => .ok [.clear none]
  | .named => .ok (named.map fun g => .clear (some g))
  | .all => .ok (.clear none :: named.map fun g => .clear (some g))
  | .graph i =>
    if has i then .ok [.clear (some (DeltaGraphName.ofWf i))]
    else if silent then .ok []
    else .error (.graphMissing i)

/-- DROP (section 3.2.2): the graphs go; the default graph cannot be removed,
    so DROP DEFAULT empties it. -/
def dropEntries (silent : Bool) (named : List DeltaGraphName) (has : WfIri → Bool) :
    GraphRef → Except UpdateError (List DeltaEntry)
  | .default => .ok [.clear none]
  | .named => .ok (named.map .drop)
  | .all => .ok (.clear none :: named.map .drop)
  | .graph i =>
    if has i then .ok [.drop (DeltaGraphName.ofWf i)]
    else if silent then .ok []
    else .error (.graphMissing i)

/-- CREATE (section 3.2.1): a graph with no triple. -/
def createEntries (silent : Bool) (has : WfIri → Bool) (i : WfIri) :
    Except UpdateError (List DeltaEntry) :=
  if has i then (if silent then .ok [] else .error (.graphExists i))
  else .ok [.create (DeltaGraphName.ofWf i)]

/-- LOAD (section 3.1.4) fetches a document, which this semantics does not do:
    LOAD SILENT does nothing, any other LOAD is an error. -/
def loadEntries (silent : Bool) (source : WfIri) : Except UpdateError (List DeltaEntry) :=
  if silent then .ok [] else .error (.loadUnavailable source)

/-- Does the graph a reference names exist? The default graph always does. -/
def refExistsWith (has : WfIri → Bool) : GraphRef → Bool
  | .default => true
  | .graph i => has i
  | _ => false

/-- A source graph that the store does not hold is an error unless `SILENT`
    (sections 3.2.3 to 3.2.5). -/
def sourceMissing (silent : Bool) (has : WfIri → Bool) : GraphRef → Option UpdateError
  | .graph i => if has i || silent then none else some (.graphMissing i)
  | _ => none

/-- The slot of a named destination of ADD, COPY or MOVE: the reference writes
    the destination with `Dataset.setGraph`, which creates the graph when it does
    not exist, also when the source has no triple (sections 3.2.3 to 3.2.5). A
    CREATE entry is idempotent on replay (`Overlay.named_create`). -/
def createSlot : Option DeltaGraphName → List DeltaEntry
  | some g => [.create g]
  | none => []

/-- ADD (section 3.2.5): every triple of the source goes into the destination.
    `triples src` are the triples of the source graph. -/
def addGraphEntries (silent : Bool) (has : WfIri → Bool) (triples : List Triple)
    (src dst : GraphRef) : Except UpdateError (List DeltaEntry) :=
  if src == dst then .ok []
  else match sourceMissing silent has src with
    | some e => .error e
    | none =>
      if !refExistsWith has src then .ok []
      else match slotOf dst with
        | none => .ok []
        | some dg => .ok (createSlot dg ++ triples.map fun t => .add t dg)

/-- COPY (section 3.2.3): the destination becomes a copy of the source. -/
def copyGraphEntries (silent : Bool) (has : WfIri → Bool) (triples : List Triple)
    (src dst : GraphRef) : Except UpdateError (List DeltaEntry) :=
  if src == dst then .ok []
  else match sourceMissing silent has src with
    | some e => .error e
    | none =>
      if !refExistsWith has src then .ok []
      else match slotOf dst with
        | none => .ok []
        | some dg => .ok (createSlot dg ++ .clear dg :: triples.map fun t => .add t dg)

/-- MOVE (section 3.2.4): COPY, then DROP of the source (CLEAR for the default
    graph). -/
def moveGraphEntries (silent : Bool) (has : WfIri → Bool) (triples : List Triple)
    (src dst : GraphRef) : Except UpdateError (List DeltaEntry) :=
  if src == dst then .ok []
  else match sourceMissing silent has src with
    | some e => .error e
    | none =>
      if !refExistsWith has src then .ok []
      else match slotOf dst with
        | none => .ok []
        | some dg =>
          let tail : List DeltaEntry := match src with
            | .default => [.clear none]
            | .graph i => [.drop (DeltaGraphName.ofWf i)]
            | _ => []
          .ok (createSlot dg ++ .clear dg :: (triples.map fun t => .add t dg) ++ tail)

/-! ## Examples, checked when the module is built -/

#guard freshLabel 7 == "sbm11u7"
-- the first counter at or after 3 whose label is not taken
#guard chooseGo (fun l => l == "sbm11u3" || l == "sbm11u4") 10 3 == some 5
-- the fuel counts the candidates: three are taken, the fourth would be free
#guard chooseGo (fun l => l == "sbm11u0" || l == "sbm11u1" || l == "sbm11u2") 3 0 == none
#guard chooseGo (fun l => l == "sbm11u0" || l == "sbm11u1" || l == "sbm11u2") 4 0 == some 3
#guard chooseGo (fun _ => false) 0 7 == none
-- three labels in a row, skipping a taken one
#guard drawMany (fun l => l == "sbm11u1") 10 3 0 [] == some ["sbm11u0", "sbm11u2", "sbm11u3"]
#guard drawMany (fun _ => false) 10 0 5 [] == some []
-- a request label stands for its table entry, else for itself
#guard renameFrom [("a", "sbm11u1")] "a" == "sbm11u1"
#guard renameFrom [("a", "sbm11u1")] "b" == "b"
#guard (changeEntries [] []).isEmpty

end L4Factoidal.SPARQL.UpdateStore
