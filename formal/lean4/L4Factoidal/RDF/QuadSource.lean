/-
L4Factoidal.RDF.QuadSource — a producer of RDF quads.

Owner, 2026-10-15, verbatim: "isn't packing (into shardborough?) done against
abstract rdf graph or dataset API not a text file format???". Tracking:
https://github.com/danbri/factoidal/issues/866. The rule behind it is the owner
rule of 2026-10-14 (https://github.com/danbri/factoidal/issues/837): the store
takes the RDF abstract syntax (the terms, triples and quads of RDF 1.1 and RDF
1.2 Concepts) and does not know a concrete syntax.

A `QuadSource` gives the quads of an RDF dataset batch by batch. Each call of
`next` returns the next batch, or `none` at the end. A batch is an array of
quads in the order the producer states them, and an array of graph names that
the source declares.

## Graph names

RDF 1.1 Concepts section 4: a named graph is a pair of a graph name (an IRI or
a blank node) and an RDF graph, and that graph can be empty. A quad states a
named graph that has a triple; it cannot state an empty one. So a batch also
carries `graphs`: the names of the named graphs the source declares, empty or
not (2026-10-15, https://github.com/danbri/factoidal/issues/855). A source of
quads only (an N-Quads document, an array of quads, an HDT file) declares no
graph, and the named graphs it gives are the graph names of its quads. A source
that can state an empty graph declares its graphs: `ofDataset` declares every
named graph of the `Dataset`; the source layer declares each graph block of a
TriG document and each named graph of a JSON-LD document. A consumer takes the
union: the named graphs are the declared names and the graph names of the
quads. The type names no syntax and
imports none (`tests/sbm11/storage_layering.py` checks both). A consumer, such as
the SBM11 packer (`Harness/Sbm11PackLib.lean`, `packQuads`), takes a `QuadSource`
and does not know where the quads come from. The producers in the tree are:

* a byte range of a file, read through the source layer
  (`Harness/Sbm11PackLib.lean`, `fileRangeSource`; the syntax is chosen there, at
  the edge);
* an RDF `Dataset` value (`ofDataset`) and an array of quads (`ofArray`), in this
  file;
* the reader of another store (`L4Factoidal/HDT/QuadSource.lean`).

## The pure model and the lift

A producer has a state. `Pull σ` is the pure form: from a state, the next batch
and the state after it, or `none` when no quad is left. `Pull.batches` runs it
for at most `fuel` steps. `ofPull` and `ofStep` lift a state and a step to a
`QuadSource`: they keep the state in a mutable reference, and `next` takes the
state out of it, applies the step and puts the new state back. The theorems
(`QuadSourceTheorems.lean`) are about the pure form. `l4sbm11-quad-source
selftest` (`Harness/Sbm11QuadSource.lean`, run by `tests/sbm11/quad_source.sh`)
checks that the batches the lift gives are the batches of the pure form.

## Order

`ofDataset` gives the default graph, then each named graph in the order of
`Dataset.named`, each graph in the order of its triples. This is the list
`Dataset.quadList` (`RDF/DatasetNormalize.lean`, the order in which
`Dataset.toCanonicalNQuads` writes the quads), and the order of
`Source.foldDataset`, in which the source layer gives the quads of a document
that it parses as a whole (`QuadSourceTheorems.quadList_eq_foldDataset`). It
declares the name of each named graph when it starts on that graph, so the
declared names are the names of `Dataset.named`, in order
(`QuadSourceTheorems.ofDataset_graphs`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDF

namespace QuadSource

/-- One quad of an RDF dataset: a triple and the name of its graph. `none` is
    the default graph (RDF 1.1 Concepts section 4). -/
abbrev Quad := Triple × Option Subject

/-- What one call of `next` gives: quads, in the order the producer states them,
    and the names of named graphs that the source declares (see "Graph names"). -/
structure Batch where
  quads : Array Quad := #[]
  graphs : Array Subject := #[]
  deriving Inhabited, BEq

/-- No quad and no graph name. -/
def Batch.isEmpty (b : Batch) : Bool := b.quads.isEmpty && b.graphs.isEmpty

/-- The number of quads and graph names. -/
def Batch.size (b : Batch) : Nat := b.quads.size + b.graphs.size

/-- A batch of quads only. -/
def Batch.ofQuads (qs : Array Quad) : Batch := { quads := qs }

/-- One more quad. -/
def Batch.pushQuad (b : Batch) (q : Quad) : Batch := { b with quads := b.quads.push q }

/-- One more declared graph name. -/
def Batch.pushGraph (b : Batch) (g : Subject) : Batch := { b with graphs := b.graphs.push g }

end QuadSource

/-- A producer of RDF quads. `next` gives the next batch and `none` at the end.
    After the first `none`, every call gives `none`. A batch is never empty: it
    has a quad or a declared graph name. When
    a call throws, every later call throws. A producer is used by one consumer in
    one thread: a consumer that starts workers gives each worker a way to open its
    producer (`Harness/Sbm11PackLib.lean`, `packQuads`), so that the producer and
    its state belong to the thread that uses them. -/
structure QuadSource where
  next : IO (Option QuadSource.Batch)

namespace QuadSource

/-! ## The pure form -/

/-- A pure producer. From a state, it gives the next batch and the state after
    it, or `none` when no quad is left. Asking again from the same state gives
    the same answer. -/
abbrev Pull (σ : Type) := σ → Option (Batch × σ)

/-- The batches of at most `fuel` steps of `p` from the state `s`, added to `acc`
    newest first. A tail call: the depth of the stack does not depend on the number
    of batches. -/
def Pull.batchesAcc {σ : Type} (p : Pull σ) : Nat → σ → List Batch → List Batch
  | 0, _, acc => acc
  | fuel + 1, s, acc =>
      match p s with
      | none => acc
      | some (b, s') => Pull.batchesAcc p fuel s' (b :: acc)

/-- The batches of at most `fuel` steps of `p` from the state `s`, in order. -/
def Pull.batches {σ : Type} (p : Pull σ) (fuel : Nat) (s : σ) : List Batch :=
  (p.batchesAcc fuel s []).reverse

/-! ## The lift to a producer -/

/-- What a producer made by `ofStep` has done: it is running from a state, it has
    ended, or a call has thrown. -/
private inductive Life (σ : Type) where
  | running (s : σ)
  | ended
  | failed

/-- A producer from a state and a step that may use `IO` (a reader of a file or
    of another store). The state is kept in a mutable reference. A call takes the
    state out of the reference while the step runs, so the step holds the only
    reference to it and can update it in place. When the step throws, the
    reference holds `failed`, and every later call throws. -/
def ofStep {σ : Type} (init : σ) (step : σ → IO (Option (Batch × σ))) : IO QuadSource := do
  let life ← IO.mkRef (Life.running init)
  pure { next := do
    match ← life.swap Life.failed with
    | .ended => do
        life.set .ended
        pure none
    | .failed => throw (IO.userError "QuadSource: an earlier call of next failed")
    | .running s =>
        match ← step s with
        | none => do
            life.set .ended
            pure none
        | some (b, s') => do
            life.set (.running s')
            pure (some b) }

/-- A producer from a pure form. -/
def ofPull {σ : Type} (init : σ) (p : Pull σ) : IO QuadSource :=
  ofStep init fun s => pure (p s)

/-- A producer that has no quad. -/
def empty : IO QuadSource := ofPull () fun _ => none

/-! ## An array of quads -/

/-- An array and the index of the next quad. -/
structure ArrayPos where
  quads : Array Quad
  pos : Nat

/-- Batches of `batch` quads (at least 1), the last one possibly shorter. An
    array of quads declares no graph name. -/
def arrayPull (batch : Nat) : Pull ArrayPos := fun s =>
  if s.pos < s.quads.size then
    let stop := min s.quads.size (s.pos + max 1 batch)
    some (Batch.ofQuads (s.quads.extract s.pos stop), { s with pos := stop })
  else none

/-- The quads of an array, `batch` at a time. -/
def ofArray (quads : Array Quad) (batch : Nat) : IO QuadSource :=
  ofPull ⟨quads, 0⟩ (arrayPull batch)

/-! ## A dataset -/

/-- A position in a dataset: the name of the graph being read, the triples of
    that graph still to give, and the named graphs after it. The first position
    is the default graph. -/
structure Cursor where
  graph : Option Subject
  triples : List Triple
  later : List NamedGraph

/-- The position before the first quad of a dataset. -/
def Cursor.start (ds : Dataset) : Cursor := ⟨none, ds.default, ds.named⟩

/-- The quads from a position to the end. -/
def Cursor.quads (c : Cursor) : List Quad :=
  c.triples.map (fun t => (t, c.graph)) ++
    c.later.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))

/-- The names of the named graphs still to declare: those after the graph being
    read. -/
def Cursor.names (c : Cursor) : List Subject := c.later.map (·.name)

/-- Add quads and graph names to `acc` until it holds `n` of them or the dataset
    has no more, and give the position after them. Passing to the next named graph
    declares its name, so a named graph with no triple is declared too. Each step
    gives one triple or passes to the next graph, so the triples still to give, and
    one for each later graph, decrease (`termination_by`). -/
def Cursor.take (n : Nat) (c : Cursor) (acc : Batch) : Batch × Cursor :=
  if n ≤ acc.size then (acc, c)
  else
    match c with
    | ⟨g, t :: ts, later⟩ => Cursor.take n ⟨g, ts, later⟩ (acc.pushQuad (t, g))
    | ⟨_, [], ng :: rest⟩ => Cursor.take n ⟨some ng.name, ng.graph, rest⟩ (acc.pushGraph ng.name)
    | ⟨_, [], []⟩ => (acc, c)
termination_by c.triples.length + (c.later.map fun ng => ng.graph.length + 1).sum
decreasing_by
  all_goals simp_wf
  all_goals simp
  all_goals omega

/-- Batches of `batch` quads and graph names (at least 1) of a dataset, the last
    one possibly shorter. A position with no quad and no graph name left gives
    `none`. -/
def datasetPull (batch : Nat) : Pull Cursor := fun c =>
  match c.take (max 1 batch) {} with
  | (b, c') => if b.isEmpty then none else some (b, c')

/-- The quads of a dataset, `batch` at a time: the default graph, then each
    named graph in order, each declared when the producer starts on it. The
    producer holds the dataset and a position in it, and copies one batch at a
    time. -/
def ofDataset (ds : Dataset) (batch : Nat) : IO QuadSource :=
  ofPull (Cursor.start ds) (datasetPull batch)

/-! ## Using a producer -/

/-- Call `f` on each batch, in order, until the end. -/
def foldBatches {α : Type} (src : QuadSource) (init : α) (f : α → Batch → IO α) : IO α := do
  let mut acc := init
  repeat
    match ← src.next with
    | none => break
    | some b => acc ← f acc b
  pure acc

/-- All the quads and declared graph names that remain, in order. -/
def drain (src : QuadSource) : IO Batch :=
  src.foldBatches {} fun acc b => pure { quads := acc.quads ++ b.quads, graphs := acc.graphs ++ b.graphs }

end QuadSource

end L4Factoidal.RDF
