/-
L4Factoidal.Storage.BlockDenotation — the block layers mapped into the one
dataset denotation `RDF.DatasetDen` (https://github.com/danbri/factoidal/issues/975,
phase A1). No code of a block layer changes; this module adds definitions and
theorems over the existing `denotes` functions.

| Layer | Existing denotation | Into `DatasetDen` |
| --- | --- | --- |
| `BlockMvp.Block` | `denotes : Graph` | `Block.den`: the default graph |
| `IndexedBlock.Block` (IBK1 to IBK3) | `denotes : Graph` (decoded id rows) | `Block.den`: the default graph, decode after denote (`Block.den_eq_ofRows`) |
| `IndexedBlockWireV4.QuadBlock` (IBK4) | `denotes : List QuadRow` | `QuadBlock.den`: `DatasetDen.ofQuads` |
| `IndexedBlockWireV5.QuadBlock` (IBK5) | `denotes` over wire terms, `resolveBlock` to RDF quads | `QuadBlock.den?`: the resolved quads, `none` when a blob does not resolve |

Theorems per layer: membership iff (`den_graph`, `den_names`), and the
denotation equality from the existing list equality of the wire round trip
(`IndexedBlockWireV3.den_decode_encode?`, `IndexedBlockWireV4.den_decode_encode?`,
`IndexedBlockWireV5.den?_decode_encode?`, `IndexedBlockWireV5.den?_decode_encode?_toWire`).

A block of one graph has no named graph. A quad block (IBK4, IBK5) has the
graph names of its rows only: a list of quads cannot hold an empty named graph
(`IndexedBlockWireV4.QuadBlock.den_names_nonempty`). The manifest must carry the
empty named graphs (RDF 1.1 Concepts section 4); see
https://github.com/danbri/factoidal/issues/880.

The dictionary of an indexed block is not needed to be injective here: the
denotation is of the decoded triples. Injectivity matters where ids are
compared without decoding (step 2 of issue 975).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetDenotation
import L4Factoidal.Storage.BlockMvp
import L4Factoidal.Storage.IndexedBlockWireV3Theorems
import L4Factoidal.Storage.IndexedBlockWireV5Theorems

namespace L4Factoidal.Storage

open L4Factoidal.RDF

/-! ## One graph as the default graph -/

/-- The denotation of a graph as the default graph of a dataset with no named
graph. -/
def graphDen (g : Graph) : DatasetDen := ({ default := g, named := [] } : Dataset).den

theorem graphDen_graph (g : Graph) (gn : Option Subject) (t : Triple) :
    (graphDen g).graph gn t ↔ gn = none ∧ ∃ u ∈ g, u.key = t.key := by
  unfold graphDen
  rw [Dataset.den_graph_iff]
  cases gn with
  | none =>
    show (∃ u, u ∈ g ∧ u.key = t.key) ↔ _
    simp
  | some n =>
    show (∃ u, (∃ ng ∈ ([] : List NamedGraph), ng.name = n ∧ u ∈ ng.graph) ∧ u.key = t.key) ↔ _
    simp

theorem graphDen_names (g : Graph) (n : Subject) : ¬ (graphDen g).names n := by
  show ¬ n ∈ ([] : List NamedGraph).map (·.name)
  simp

/-! ## `BlockMvp` -/

/-- The dataset an MVP block denotes: its rows as the default graph. -/
def BlockMvp.Block.den (b : BlockMvp.Block) : DatasetDen := graphDen b.denotes

theorem BlockMvp.Block.den_graph (b : BlockMvp.Block) (gn : Option Subject) (t : Triple) :
    b.den.graph gn t ↔ gn = none ∧ ∃ u ∈ b.rows, u.key = t.key :=
  graphDen_graph b.rows gn t

theorem BlockMvp.Block.den_names (b : BlockMvp.Block) (n : Subject) : ¬ b.den.names n :=
  graphDen_names b.rows n

/-! ## `IndexedBlock` (IBK1, IBK2, IBK3) -/

/-- The dataset an indexed block denotes: its decoded rows as the default
graph. -/
def IndexedBlock.Block.den (b : IndexedBlock.Block) : DatasetDen := graphDen b.denotes

/-- Membership iff: a triple is a member exactly when a row of the block
decodes to an RDF-term-equal triple. -/
theorem IndexedBlock.Block.den_graph (b : IndexedBlock.Block) (gn : Option Subject) (t : Triple) :
    b.den.graph gn t ↔
      gn = none ∧ ∃ r ∈ b.rows.toList, ∃ u, IndexedBlock.decodeTriple? b.dict r = some u ∧ u.key = t.key := by
  rw [IndexedBlock.Block.den, graphDen_graph]
  unfold IndexedBlock.Block.denotes
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨hg, u, ⟨r, hr, hd⟩, e⟩
    exact ⟨hg, r, hr, u, hd, e⟩
  · rintro ⟨hg, r, hr, u, hd, e⟩
    exact ⟨hg, u, ⟨r, hr, hd⟩, e⟩

theorem IndexedBlock.Block.den_names (b : IndexedBlock.Block) (n : Subject) : ¬ b.den.names n :=
  graphDen_names b.denotes n

/-- The indexed block is decode after denote: its rows, with the dictionary
decoder, as `DatasetDen.ofRows`. -/
theorem IndexedBlock.Block.den_eq_ofRows (b : IndexedBlock.Block) :
    b.den = DatasetDen.ofRows (fun r => (IndexedBlock.decodeTriple? b.dict r).map (fun u => (none, u)))
      (· ∈ b.rows.toList) (fun _ => False) := by
  apply DatasetDen.ext
  · intro gn t
    rw [IndexedBlock.Block.den_graph]
    constructor
    · rintro ⟨rfl, r, hr, u, hd, e⟩
      exact ⟨r, hr, u, by simp only [hd, Option.map_some], e⟩
    · rintro ⟨r, hr, u, hd, e⟩
      cases hdec : IndexedBlock.decodeTriple? b.dict r with
      | none => simp [hdec] at hd
      | some v =>
        simp only [hdec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨rfl, r, hr, v, hdec, e⟩
  · intro n
    constructor
    · intro h; exact absurd h (IndexedBlock.Block.den_names b n)
    · rintro (h | ⟨r, u, _, hd⟩)
      · exact h.elim
      · cases hdec : IndexedBlock.decodeTriple? b.dict r with
        | none => simp [hdec] at hd
        | some v => simp [hdec] at hd

/-- IBK3: the decoded artifact denotes the dataset its source block denotes
(from `denotes_decode_encode?`). -/
theorem IndexedBlockWireV3.den_decode_encode? (block : IndexedBlock.Block) (bytes : ByteArray)
    (h : IndexedBlockWireV3.encode? block = some bytes) :
    ∃ decoded, IndexedBlockWireV3.decode bytes = some decoded ∧ decoded.den = block.den := by
  obtain ⟨decoded, hd, he⟩ := IndexedBlockWireV3.denotes_decode_encode? block bytes h
  exact ⟨decoded, hd, by rw [IndexedBlock.Block.den, IndexedBlock.Block.den, he]⟩

/-! ## IBK4 quad blocks -/

/-- The dataset an IBK4 block denotes: its decoded quads. -/
def IndexedBlockWireV4.QuadBlock.den (b : IndexedBlockWireV4.QuadBlock) : DatasetDen :=
  DatasetDen.ofQuads b.denotes []

theorem IndexedBlockWireV4.QuadBlock.den_graph (b : IndexedBlockWireV4.QuadBlock)
    (gn : Option Subject) (t : Triple) :
    b.den.graph gn t ↔
      ∃ r ∈ b.rows.toList, ∃ u, IndexedBlockWireV4.decodeQuad? b.dict r = some (gn, u) ∧ u.key = t.key := by
  rw [IndexedBlockWireV4.QuadBlock.den, DatasetDen.ofQuads_graph]
  unfold IndexedBlockWireV4.QuadBlock.denotes
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨u, ⟨r, hr, hd⟩, e⟩
    exact ⟨r, hr, u, hd, e⟩
  · rintro ⟨r, hr, u, hd, e⟩
    exact ⟨u, ⟨r, hr, hd⟩, e⟩

theorem IndexedBlockWireV4.QuadBlock.den_names (b : IndexedBlockWireV4.QuadBlock) (n : Subject) :
    b.den.names n ↔ ∃ u, (some n, u) ∈ b.denotes := by
  rw [IndexedBlockWireV4.QuadBlock.den, DatasetDen.ofQuads_names]
  simp

/-- An IBK4 block names only graphs that have a triple: it cannot hold an
empty named graph. -/
theorem IndexedBlockWireV4.QuadBlock.den_names_nonempty (b : IndexedBlockWireV4.QuadBlock)
    (n : Subject) (h : b.den.names n) : ∃ t, b.den.graph (some n) t := by
  obtain ⟨u, hu⟩ := (IndexedBlockWireV4.QuadBlock.den_names b n).mp h
  exact ⟨u, (DatasetDen.ofQuads_graph _ _ _ _).mpr ⟨u, hu, rfl⟩⟩

/-- IBK4: the decoded artifact denotes the dataset its source block denotes. -/
theorem IndexedBlockWireV4.den_decode_encode? (block : IndexedBlockWireV4.QuadBlock) (bytes : ByteArray)
    (h : IndexedBlockWireV4.encode? block = some bytes) :
    ∃ decoded, IndexedBlockWireV4.decode bytes = some decoded ∧ decoded.den = block.den := by
  obtain ⟨decoded, hd, he⟩ := IndexedBlockWireV4.denotes_decode_encode? block bytes h
  exact ⟨decoded, hd, by rw [IndexedBlockWireV4.QuadBlock.den, IndexedBlockWireV4.QuadBlock.den, he]⟩

/-! ## IBK5 quad blocks -/

/-- The dataset an IBK5 block denotes once its out-of-line literals are
resolved through `lookup` and checked with `h`; `none` when a blob does not
resolve. -/
def IndexedBlockWireV5.QuadBlock.den? (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    (b : IndexedBlockWireV5.QuadBlock) : Option DatasetDen :=
  (IndexedBlockWireV5.resolveBlock h lookup b).map (fun qs => DatasetDen.ofQuads qs [])

/-- IBK5: the decoded artifact denotes the dataset its source block denotes,
for every hash function and every lookup. -/
theorem IndexedBlockWireV5.den?_decode_encode? (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) (block : IndexedBlockWireV5.QuadBlock) (bytes : ByteArray)
    (henc : IndexedBlockWireV5.encode? block = some bytes) :
    ∃ decoded, IndexedBlockWireV5.decode bytes = some decoded ∧
      decoded.den? h lookup = block.den? h lookup := by
  obtain ⟨decoded, hd, he⟩ := IndexedBlockWireV5.resolveBlock_decode_encode? h lookup block bytes henc
  exact ⟨decoded, hd, by rw [IndexedBlockWireV5.QuadBlock.den?, IndexedBlockWireV5.QuadBlock.den?, he]⟩

/-- IBK5: a block built by `toWire` from RDF quads, written and read back,
denotes those quads. The hypotheses are those of
`resolveBlock_decode_encode?_toWire`: the interning step and the blob lookup. -/
theorem IndexedBlockWireV5.den?_decode_encode?_toWire (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) (block : IndexedBlockWireV5.QuadBlock) (bytes : ByteArray)
    (quads : List (Option GraphRef × Triple))
    (henc : IndexedBlockWireV5.encode? block = some bytes)
    (hdenotes : block.denotes = quads.map (IndexedBlockWireV5.toWireQuad h))
    (hlookup : ∀ q ∈ quads, TermWireV2.resolve h lookup (TermWireV2.toWire h q.2.o) = some q.2.o) :
    ∃ decoded, IndexedBlockWireV5.decode bytes = some decoded ∧
      decoded.den? h lookup = some (DatasetDen.ofQuads quads []) := by
  obtain ⟨decoded, hd, he⟩ :=
    IndexedBlockWireV5.resolveBlock_decode_encode?_toWire h lookup block bytes quads henc hdenotes hlookup
  exact ⟨decoded, hd, by rw [IndexedBlockWireV5.QuadBlock.den?, he]; rfl⟩

#print axioms IndexedBlock.Block.den_eq_ofRows
#print axioms IndexedBlockWireV3.den_decode_encode?
#print axioms IndexedBlockWireV4.QuadBlock.den_graph
#print axioms IndexedBlockWireV4.den_decode_encode?
#print axioms IndexedBlockWireV5.den?_decode_encode?_toWire

end L4Factoidal.Storage
