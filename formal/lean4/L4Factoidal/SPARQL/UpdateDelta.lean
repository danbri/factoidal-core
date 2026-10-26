/-
L4Factoidal.SPARQL.UpdateDelta — the narrow translation from parsed SPARQL
Update to durable delta-log operations.

This is deliberately a translation layer, not another update evaluator.  The
existing `SPARQL.Update` module remains the reference semantics, while
`RDF.StoreDeltaMerge` proves that replaying the resulting `DeltaEntry` list
over an immutable base has the same membership behaviour as applying those
entries directly.

The first persistent execution path admits ground DATA operations and the
single-graph management forms that already map one-to-one to `DeltaEntry`.
WHERE-dependent modifications and cross-graph COPY/MOVE/ADD are retained by
the full Update semantics but are intentionally refused here until the
disk-backed evaluator can execute their WHERE clause against the composed
base-plus-delta view.
-/
import L4Factoidal.SPARQL.Update
import L4Factoidal.Storage.DeltaLog

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.Storage

/-- A blank node anywhere in the term: inside a triple term too, at any depth
    (a loop over the object chain). `Triple.hasBnode` looks at the top level
    only; a SPARQL 1.2 update can put a blank node inside a triple term
    (https://github.com/danbri/factoidal/issues/792 item 1). -/
def termMentionsBnode : Term → Bool
  | .bnode _ => true
  | .tripleTerm s _ o =>
      match s with
      | .bnode _ => true
      | .iri _ => termMentionsBnode o
  | _ => false

def tripleMentionsBnode (t : Triple) : Bool :=
  (match t.s with | .bnode _ => true | .iri _ => false) || termMentionsBnode t.o

/-- Compile one parsed update operation for a durable log.  The caller supplies
    the request-scoped blank-node renaming function required by SPARQL 1.1
    INSERT DATA.  DELETE DATA blank nodes were already rejected by the parser
    and are refused defensively here as well. -/
def deltaEntriesForOp? (renameBnode : BNodeId → BNodeId) : UpdateOp → Option (List DeltaEntry)
  | .insertData quads =>
      some ((collectQuads none quads).map fun q =>
        let (graph, triple) := Quad.renameBnodes renameBnode q
        DeltaEntry.add triple (graph.map DeltaGraphName.ofWf))
  | .deleteData quads =>
      let collected := collectQuads none quads
      if collected.any (fun q => tripleMentionsBnode q.2) then none
      else some (collected.map fun q => DeltaEntry.remove q.2 (q.1.map DeltaGraphName.ofWf))
  | .clear _ .default => some [.clear none]
  | .clear _ (.graph graph) => some [.clear (some (DeltaGraphName.ofWf graph))]
  | .drop _ (.graph graph) => some [.drop (DeltaGraphName.ofWf graph)]
  | .create _ graph => some [.create (DeltaGraphName.ofWf graph)]
  | _ => none

/-- Compile a whole request in source order.  `none` is an explicit admission
    refusal, never a silently skipped operation. -/
def deltaEntriesForUpdate? (renameBnode : BNodeId → BNodeId) (update : Update) : Option (List DeltaEntry) :=
  update.ops.foldl (fun acc op => do
    let entries ← acc
    let next ← deltaEntriesForOp? renameBnode op
    some (entries ++ next)) (some [])

/-- Give the request one commit identity after its parsed operations have been
    admitted.  Sequence/epoch allocation belongs to the durable store edge,
    not to the SPARQL parser. -/
def deltaBatchForUpdate? (seq epoch : Nat) (renameBnode : BNodeId → BNodeId)
    (update : Update) : Option DeltaBatch :=
  (deltaEntriesForUpdate? renameBnode update).map fun ops => { seq, epoch, ops }

end L4Factoidal.SPARQL
