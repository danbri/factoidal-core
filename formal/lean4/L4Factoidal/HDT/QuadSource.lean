/-
L4Factoidal.HDT.QuadSource — the triples of an HDT store as a producer of RDF
quads (https://github.com/danbri/factoidal/issues/866).

An HDT file is a store, not a text syntax. `HDT/Store.lean` opens it into a
`GraphStore` (the bytes, the dictionary inventory and the triples section), and
`HDT/Triples.lean` and `HDT/Dictionary.lean` turn ids into RDF terms. This module
gives the triples of a `GraphStore` to a consumer of `QuadSource`
(`RDF/QuadSource.lean`), for example the SBM11 packer, with no document text in
between: the packer receives `Triple` values whose terms the HDT dictionary
decoded (`idToTerm`).

The order is the order of the file: subject by subject in id order, and for a
subject its predicates and objects in the order `triplesForSubject` gives, which
is the order of the BitmapTriples sections. An HDT file holds one graph, so every
quad is in the default graph. A batch holds the triples of whole subjects, at
least `batch` triples unless the file ends first (a subject with more triples than
`batch` gives a larger batch).

A structure of the file that cannot be read stops the producer with an error that
names the subject or the id. The reader of `HDT/Store.lean` that answers a query
(`decodeSubject`, `decodePredicate`, `decodeObject`) replaces a failed decode with
a visible sentinel term; a pack of the store is a copy, and a sentinel in a copy
would be a wrong triple that nothing flags, so the producer refuses instead.

The cost of one subject is the cost of `triplesForSubject`, which
`HDT/Triples.lean` describes in its header.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.HDT.Store
import L4Factoidal.RDF.QuadSource

namespace L4Factoidal.HDT

open L4Factoidal.RDF
open L4Factoidal.RDF.QuadSource

/-- The subject of an id of the subject role. -/
def GraphStore.subjectOf (gs : GraphStore) (id : Nat) : Except String Subject :=
  match idToTerm gs.bytes gs.inventory .subject id with
  | none => .error s!"the subject id {id} has no term in the dictionary"
  | some t =>
      match t.toSubject? with
      | some s => .ok s
      | none => .error s!"the subject id {id} stands for a literal or a triple term"

/-- The predicate of an id of the predicate role. -/
def GraphStore.predicateOf (gs : GraphStore) (id : Nat) : Except String WfIri :=
  match idToTerm gs.bytes gs.inventory .predicate id with
  | some (.iri i) => .ok i
  | some _ => .error s!"the predicate id {id} does not stand for an IRI"
  | none => .error s!"the predicate id {id} has no term in the dictionary"

/-- The object of an id of the object role. -/
def GraphStore.objectOf (gs : GraphStore) (id : Nat) : Except String Term :=
  match idToTerm gs.bytes gs.inventory .object id with
  | some t => .ok t
  | none => .error s!"the object id {id} has no term in the dictionary"

/-- The triples of the subjects `first`, `first + 1`, ... as quads of the default
    graph, until the batch holds `size` quads or the `subjects` subjects end, and
    the id of the subject after the last one read. -/
def GraphStore.subjectBatch (gs : GraphStore) (subjects size first : Nat) :
    Except String (Batch × Nat) := do
  let mut out : Batch := {}
  let mut sid := first
  for _ in [0:subjects + 1] do
    if subjects < sid || size ≤ out.size then break
    let some pairs := triplesForSubject gs.bytes gs.triples sid
      | throw s!"the triples of the subject id {sid} cannot be read from the triples section"
    let s ← gs.subjectOf sid
    for (pid, oid) in pairs do
      let p ← gs.predicateOf pid
      let o ← gs.objectOf oid
      out := out.pushQuad ({ s := s, p := p, o := o }, none)
    sid := sid + 1
  return (out, sid)

/-- The triples of an HDT store as a `QuadSource`: subject by subject, a batch of
    at least `batch` triples. Fails when the number of subjects cannot be read
    from the triples section, and a call of `next` fails when a subject cannot
    be read. -/
def GraphStore.quadSource (gs : GraphStore) (batch : Nat) : IO QuadSource := do
  let some subjects := numSubjects gs.bytes gs.triples
    | throw (IO.userError "HDT: the number of subjects cannot be read from the triples section")
  ofStep 1 fun first =>
    if subjects < first then pure none
    else
      match gs.subjectBatch subjects (max 1 batch) first with
      | .error e => throw (IO.userError s!"HDT: {e}")
      | .ok (out, next) => pure (if out.isEmpty then none else some (out, next))

end L4Factoidal.HDT
