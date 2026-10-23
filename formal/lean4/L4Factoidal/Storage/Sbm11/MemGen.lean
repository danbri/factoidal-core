/-
L4Factoidal.Storage.Sbm11.MemGen — an SBM11 generation in memory, and the
store (`IdQuery.Store Id`) that answers from it
(https://github.com/danbri/factoidal/issues/776; rows E0, L3c and L4e of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

A generation in memory has the dictionary keys in rank order, and for each of
the four permutations the PRB1 bytes and the PRM1 entries; and the ids of the
named graphs. `MemGen.store` answers:

* the PRM1 range queries by `PrmRange.rangeM` over the entries in an array
  (`arrayReader`, the reader of the in-memory store of L4e);
* the PRB1 reads from the byte array;
* a term's id by `TermId.toCode?` of the term with its language tags in lower
  case (`normalizeTerm`, RDF 1.1 Concepts section 3.3), the function
  `Session.idOf` computes with `Dict.lookupM` over the dictionary file
  (`DictLookupTheorems.lookupM_encodeDict`: the rank of the key);
* an id's term by `TermId.ofCode?` (`Session.termOf`).

`MemGenDictTheorems` proves the dictionary hypotheses of
`HarnessWhereTheorems.harness_where_allowed` for this store from one check of
the keys (`keysOk`). Not proved here: that the I/O store of
`Harness/Sbm11Query.lean` answers as this store does (L4e for `IO`), and that
the packer writes a generation that passes the checks (E0, L3c).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PrmRange
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.Storage.Sbm11.DictRange

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery (Store)

/-- An SBM11 generation in memory: the dictionary keys in rank order; per
    permutation (0 PSO, 1 POS, 2 SPO, 3 OSP) the PRB1 bytes and the PRM1
    entries; the ids of the named graphs. -/
structure MemGen where
  keys : List Key
  prb : Nat → ByteArray
  ms : Nat → List BlockMeta
  named : Array UInt64

/-- The id of a term: the code of the term with its language tags in lower
    case. -/
def MemGen.cid (G : MemGen) (t : Term) : Option UInt64 :=
  (toCode? G.keys (normalizeTerm t)).map UInt64.ofNat

/-- The term of an id (a blank node with the empty label for an id with no
    term; `ok` excludes such an id). -/
def MemGen.dec (G : MemGen) (x : UInt64) : Term :=
  (ofCode? G.keys x.toNat).getD (.bnode "")

/-- An id of the store: the code of a term. -/
def MemGen.ok (G : MemGen) (x : UInt64) : Prop :=
  ∃ t, toCode? G.keys t = some x.toNat

/-- The id of a constant of a query, 0 when it has none. -/
def MemGen.idv (G : MemGen) (t : Term) : UInt64 := (G.cid t).getD 0

/-- The key of the dictionary id `x` (the empty key for an id that is not a
    dictionary id). -/
def MemGen.keyBytes (G : MemGen) (x : UInt64) : ByteArray :=
  ⟨((G.keys[x.toNat % two60]?).getD []).toArray⟩

/-- The store of the generation (`m = Id`, no overlay, single-thread scans). -/
def MemGen.store (G : MemGen) : Store Id where
  blockCount p := pure (G.ms p).length
  blocksForRange p key := PrmRange.rangeM (PrmRange.arrayReader (G.ms p).toArray) key
  prb p off len := pure ((G.prb p).extract off (off + len))
  idOf t := pure (G.cid t)
  keyOf x := pure (G.keyBytes x)
  keySlice x := pure (G.keyBytes x, 0, (G.keyBytes x).size)
  termOf x :=
    match ofCode? G.keys x.toNat with
    | some t => pure t
    | none => throw s!"id {x}: no term"
  lowerBound k := pure (DictRange.lowerBoundList (G.keys.map fun key => ⟨key.toArray⟩) k)
  namedGraphs := some (pure G.named)

/-! ## The check of the dictionary keys -/

/-- No `rdf:XMLLiteral` literal in the term. `Term.eqb` compares two
    `rdf:XMLLiteral` literals by their canonical XML
    (`XmlCanon.xmlCanonEq`), not by their lexical forms; two such literals
    with different lexical forms are different RDF terms with two ids, and
    `Term.eqb` says they are equal. -/
def noXml : Term → Bool
  | .literal l => l.val.datatype != rdfXMLLiteral
  | .tripleTerm _ _ o => noXml o
  | _ => true

/-- Every key decodes to a term whose language tags are in lower case and
    that holds no `rdf:XMLLiteral` literal. -/
def keysOk (keys : List Key) : Bool :=
  keys.all fun k =>
    match decodeKey? k with
    | some t => normalizeTerm t == t && noXml t
    | none => false

end L4Factoidal.Storage.Sbm11.MemGen
