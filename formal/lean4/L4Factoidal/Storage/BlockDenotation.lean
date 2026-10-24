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
import L4Factoidal.Storage.TermFoldTheorems

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

/-! ## The builders denote their input

The builders fold every term (`TermFold.foldTerm`, language tags in lower
case) before they give it an id. The fold keeps `Triple.key`
(`key_foldTriple`), so the built block denotes the dataset of its input. No
hypothesis is needed: the denotation is membership up to `Triple.key`, so a
repeated or an RDF-term-equal triple of the input changes nothing.

* `IndexedBlock.fromGraph_den`: `(fromGraph g).den = graphDen g`.
* `IndexedBlockWireV4.fromQuads_den`: `(fromQuads qs).den = DatasetDen.ofQuads qs []`;
  `fromQuads_listQuads_den`: for a dataset with no empty named graph, `ds.den`.
* `IndexedBlockWireV5.den?_fromRdfQuads`: with a lookup that resolves each
  object (`hlookup`), `den? = some (DatasetDen.ofQuads qs [])`.
* End to end, build then write then read: `IndexedBlockWireV3.den_decode_encode?_fromGraph`,
  `IndexedBlockWireV4.den_decode_encode?_fromQuads`,
  `IndexedBlockWireV5.den?_decode_encode?_fromRdfQuads`. -/

open L4Factoidal.Storage.TermFold (foldTerm foldTriple foldQuad foldTerm_idem joinKey_eq_foldTerm)

/-- The fold of a triple has the key of the triple. -/
theorem key_foldTriple (t : Triple) : (foldTriple t).key = t.key := by
  show ({ s := t.s, p := t.p, o := (foldTerm t.o).joinKey } : Triple) = { s := t.s, p := t.p, o := t.o.joinKey }
  rw [joinKey_eq_foldTerm, joinKey_eq_foldTerm, foldTerm_idem]

theorem graphDen_map_foldTriple (g : Graph) : graphDen (g.map foldTriple) = graphDen g := by
  apply DatasetDen.ext
  · intro gn t
    rw [graphDen_graph, graphDen_graph]
    simp only [List.mem_map]
    constructor
    · rintro ⟨hg, _, ⟨u, hu, rfl⟩, e⟩
      exact ⟨hg, u, hu, (key_foldTriple u).symm.trans e⟩
    · rintro ⟨hg, u, hu, e⟩
      exact ⟨hg, foldTriple u, ⟨u, hu, rfl⟩, (key_foldTriple u).trans e⟩
  · intro n
    exact iff_of_false (graphDen_names _ n) (graphDen_names _ n)

/-- **`fromGraph` denotes its input.** -/
theorem IndexedBlock.fromGraph_den (g : Graph) : (IndexedBlock.fromGraph g).den = graphDen g := by
  rw [IndexedBlock.Block.den, IndexedBlock.fromGraph_denotes, graphDen_map_foldTriple]

theorem DatasetDen.ofQuads_map_foldQuad (qs : List (Option Subject × Triple)) (decl : List Subject) :
    DatasetDen.ofQuads (qs.map foldQuad) decl = DatasetDen.ofQuads qs decl := by
  apply DatasetDen.ext
  · intro gn t
    rw [DatasetDen.ofQuads_graph, DatasetDen.ofQuads_graph]
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨⟨gq, u⟩, hu, e1⟩, e⟩
      simp only [foldQuad, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨u, hu, (key_foldTriple u).symm.trans e⟩
    · rintro ⟨u, hu, e⟩
      exact ⟨foldTriple u, ⟨(gn, u), hu, rfl⟩, (key_foldTriple u).trans e⟩
  · intro n
    rw [DatasetDen.ofQuads_names, DatasetDen.ofQuads_names]
    simp only [List.mem_map]
    constructor
    · rintro (h | ⟨_, ⟨gq, u⟩, hu, e1⟩)
      · exact Or.inl h
      · simp only [foldQuad, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        exact Or.inr ⟨u, hu⟩
    · rintro (h | ⟨u, hu⟩)
      · exact Or.inl h
      · exact Or.inr ⟨foldTriple u, (some n, u), hu, rfl⟩

/-- **`fromQuads` (IBK4) denotes its input.** -/
theorem IndexedBlockWireV4.fromQuads_den (qs : List (Option Subject × Triple)) :
    (IndexedBlockWireV4.fromQuads qs).den = DatasetDen.ofQuads qs [] := by
  rw [IndexedBlockWireV4.QuadBlock.den, IndexedBlockWireV4.fromQuads_denotes,
    DatasetDen.ofQuads_map_foldQuad]

/-- **A dataset built into an IBK4 block.** The quads of a dataset with no
empty named graph denote the dataset. The hypothesis is needed: a quad block
cannot hold an empty named graph (`QuadBlock.den_names_nonempty`). -/
theorem IndexedBlockWireV4.fromQuads_listQuads_den (ds : Dataset)
    (hne : ∀ ng ∈ ds.named, ng.graph ≠ []) :
    (IndexedBlockWireV4.fromQuads ds.listQuads).den = ds.den := by
  rw [IndexedBlockWireV4.fromQuads_den, Dataset.den_eq_ofQuads]
  apply DatasetDen.ext
  · intro gn t
    rw [DatasetDen.ofQuads_graph, DatasetDen.ofQuads_graph]
  · intro n
    rw [DatasetDen.ofQuads_names, DatasetDen.ofQuads_names]
    constructor
    · rintro (h | h)
      · simp at h
      · exact Or.inr h
    · rintro (h | h)
      · simp only [Dataset.names, List.mem_map] at h
        obtain ⟨ng, hng, rfl⟩ := h
        obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (hne ng hng)
        refine Or.inr ⟨u, ?_⟩
        simp only [Dataset.listQuads, List.mem_append, List.mem_map, List.mem_flatMap]
        exact Or.inr ⟨ng, hng, u, hu, rfl⟩
      · exact Or.inr h

/-- Resolving the fold of a wire term gives the fold of its resolution. -/
theorem TermWireV2.resolve_foldWire (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    (w : TermWireV2.WireTerm) :
    TermWireV2.resolve h lookup (TermWireV2.foldWire w) = (TermWireV2.resolve h lookup w).map foldTerm := by
  cases w with
  | inline t => rfl
  | blob b =>
    obtain ⟨dt, tag, dir, len, sha⟩ := b
    simp only [TermWireV2.foldWire, TermWireV2.resolve]
    have hwf : ∀ lex, literalWf (⟨lex, dt, tag.map String.toLower, dir⟩ : Literal) =
        literalWf (⟨lex, dt, tag, dir⟩ : Literal) := by
      intro lex; cases tag <;> cases dir <;> rfl
    cases hl : lookup sha with
    | none => rfl
    | some bytes =>
      by_cases hs : bytes.size = len
      · by_cases hh : h bytes = sha
        · cases hu : String.fromUTF8? bytes with
          | none => simp [hs, hh, hu]
          | some lex =>
            simp only [hs, hh, hu, bne_self_eq_false, Bool.false_eq_true, if_false, ne_eq,
              not_true_eq_false, Option.bind_some, Option.bind_eq_bind]
            by_cases hw : literalWf (⟨lex, dt, tag, dir⟩ : Literal) = true
            · rw [dif_pos ((hwf lex).trans hw), dif_pos hw]
              cases tag with
              | none => rfl
              | some tg =>
                show some _ = some (Sbm11.normalizeLit _)
                unfold Sbm11.normalizeLit
                simp only
                rw [dif_pos (show literalWf (⟨lex, dt, some tg.toLower, dir⟩ : Literal) = true from
                  (hwf lex).trans hw)]
                rfl
            · rw [dif_neg (by rw [hwf]; exact hw), dif_neg hw]
              rfl
        · simp [hs, hh]
      · simp [hs]

private theorem mapM_fold_toWireQuad (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) :
    ∀ (quads : List (Option Subject × Triple)),
      (∀ q ∈ quads, TermWireV2.resolve h lookup (TermWireV2.toWire h q.2.o) = some q.2.o) →
      (((quads.map (IndexedBlockWireV5.toWireQuad h)).map IndexedBlockWireV5.foldWireQuad).mapM
          fun quad => do
            let o ← TermWireV2.resolve h lookup quad.2.o
            some (quad.1, ({ s := quad.2.s, p := quad.2.p, o := o } : Triple)))
        = some (quads.map foldQuad) := by
  intro quads
  induction quads with
  | nil => intro _; rfl
  | cons q rest ih =>
    intro hlk
    have hq : TermWireV2.resolve h lookup (TermWireV2.foldWire (TermWireV2.toWire h q.2.o)) =
        some (foldTerm q.2.o) := by
      rw [TermWireV2.resolve_foldWire, hlk q List.mem_cons_self]
      rfl
    have hrest := ih (fun x hx => hlk x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.mapM_cons, IndexedBlockWireV5.toWireQuad,
      IndexedBlockWireV5.foldWireQuad, hq, hrest]
    rfl

/-- IBK5: the block built by `toWire` from RDF quads resolves to the quads
with every term folded. `hlookup`: the lookup resolves the wire form of each
object (`TermWireV2.resolve_toWire` discharges it for the packer's own
lookup). -/
theorem IndexedBlockWireV5.resolveBlock_fromRdfQuads (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) (quads : List (Option Subject × Triple))
    (hlookup : ∀ q ∈ quads, TermWireV2.resolve h lookup (TermWireV2.toWire h q.2.o) = some q.2.o) :
    IndexedBlockWireV5.resolveBlock h lookup (IndexedBlockWireV5.fromRdfQuads h quads) =
      some (quads.map foldQuad) := by
  rw [IndexedBlockWireV5.resolveBlock, IndexedBlockWireV5.fromRdfQuads,
    IndexedBlockWireV5.fromQuads_denotes]
  exact mapM_fold_toWireQuad h lookup quads hlookup

/-- **The IBK5 builder (`toWire`) denotes its input**, for a lookup that
resolves each object. -/
theorem IndexedBlockWireV5.den?_fromRdfQuads (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) (quads : List (Option Subject × Triple))
    (hlookup : ∀ q ∈ quads, TermWireV2.resolve h lookup (TermWireV2.toWire h q.2.o) = some q.2.o) :
    (IndexedBlockWireV5.fromRdfQuads h quads).den? h lookup = some (DatasetDen.ofQuads quads []) := by
  rw [IndexedBlockWireV5.QuadBlock.den?, IndexedBlockWireV5.resolveBlock_fromRdfQuads h lookup quads hlookup]
  simp only [Option.map_some, DatasetDen.ofQuads_map_foldQuad]

/-! ### Build, write, read -/

/-- **IBK3 end to end**: a graph built into a block, written and read back,
denotes the graph. -/
theorem IndexedBlockWireV3.den_decode_encode?_fromGraph (g : Graph) (bytes : ByteArray)
    (h : IndexedBlockWireV3.encode? (IndexedBlock.fromGraph g) = some bytes) :
    ∃ decoded, IndexedBlockWireV3.decode bytes = some decoded ∧ decoded.den = graphDen g := by
  obtain ⟨decoded, hd, he⟩ := IndexedBlockWireV3.den_decode_encode? _ bytes h
  exact ⟨decoded, hd, he.trans (IndexedBlock.fromGraph_den g)⟩

/-- **IBK4 end to end**: quads built into a block, written and read back,
denote the quads. -/
theorem IndexedBlockWireV4.den_decode_encode?_fromQuads (qs : List (Option Subject × Triple))
    (bytes : ByteArray) (h : IndexedBlockWireV4.encode? (IndexedBlockWireV4.fromQuads qs) = some bytes) :
    ∃ decoded, IndexedBlockWireV4.decode bytes = some decoded ∧
      decoded.den = DatasetDen.ofQuads qs [] := by
  obtain ⟨decoded, hd, he⟩ := IndexedBlockWireV4.den_decode_encode? _ bytes h
  exact ⟨decoded, hd, he.trans (IndexedBlockWireV4.fromQuads_den qs)⟩

/-- **IBK5 end to end**: RDF quads built into a block by `toWire`, written
and read back, denote the quads, for a lookup that resolves each object. -/
theorem IndexedBlockWireV5.den?_decode_encode?_fromRdfQuads (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) (quads : List (Option Subject × Triple))
    (bytes : ByteArray)
    (henc : IndexedBlockWireV5.encode? (IndexedBlockWireV5.fromRdfQuads h quads) = some bytes)
    (hlookup : ∀ q ∈ quads, TermWireV2.resolve h lookup (TermWireV2.toWire h q.2.o) = some q.2.o) :
    ∃ decoded, IndexedBlockWireV5.decode bytes = some decoded ∧
      decoded.den? h lookup = some (DatasetDen.ofQuads quads []) := by
  obtain ⟨decoded, hd, he⟩ := IndexedBlockWireV5.den?_decode_encode? h lookup _ bytes henc
  exact ⟨decoded, hd, he.trans (IndexedBlockWireV5.den?_fromRdfQuads h lookup quads hlookup)⟩

#print axioms IndexedBlock.fromGraph_den
#print axioms IndexedBlockWireV4.fromQuads_den
#print axioms IndexedBlockWireV4.fromQuads_listQuads_den
#print axioms TermWireV2.resolve_foldWire
#print axioms IndexedBlockWireV5.den?_fromRdfQuads
#print axioms IndexedBlockWireV3.den_decode_encode?_fromGraph
#print axioms IndexedBlockWireV4.den_decode_encode?_fromQuads
#print axioms IndexedBlockWireV5.den?_decode_encode?_fromRdfQuads

end L4Factoidal.Storage
