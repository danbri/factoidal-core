/-
L4Factoidal.Dataflow.PhaseStorage — stages for the storage components whose
denotation theorems exist (https://github.com/danbri/factoidal/issues/975).

Each contract is stated against `RDF.DatasetDen` (`RDF/DatasetDenotation.lean`).
This module adds stages and theorems only; no store code changes.

## Stages

| stage | in → out | contract | from |
|---|---|---|---|
| `sbm11OverlayStage` | `State × Op` → `State` | `OverlayStepContract`: INSERT adds the quad of the row, DELETE removes it, CREATE adds the graph name and no triple | `overlayDen_add`, `overlayDen_remove_sbm11_vocab`, `overlayDen_create_names`, `overlayDen_create_graph` |
| `ibk3RoundTripStage` | `IndexedBlock.Block` → `IndexedBlock.Block` | `BlockDenEq`: the block read back denotes the dataset of the block written | `IndexedBlockWireV3.den_decode_encode?` |
| `ibk4RoundTripStage` | `QuadBlock` (IBK4) → `QuadBlock` | `Ibk4DenEq` | `IndexedBlockWireV4.den_decode_encode?` |
| `ibk5RoundTripStage h lookup` | `QuadBlock` (IBK5) → `QuadBlock` | `Ibk5DenEq`: equal `den?` for the hash `h` and the blob lookup `lookup` | `IndexedBlockWireV5.den?_decode_encode?` |
| `ibk3BuildWriteReadStage` | `Graph` → `IndexedBlock.Block` | `Ibk3BuildDen`: build (`fromGraph`), write, read; the block denotes the graph | `IndexedBlock.fromGraph_den`, `IndexedBlockWireV3.den_decode_encode?` |
| `ibk4BuildWriteReadStage` | quads → `QuadBlock` (IBK4) | `Ibk4BuildDen`: build (`fromQuads`), write, read; the block denotes `DatasetDen.ofQuads qs []` | `IndexedBlockWireV4.fromQuads_den`, `IndexedBlockWireV4.den_decode_encode?` |
| `ibk5BuildWriteReadStage h lookup` | RDF quads → `QuadBlock` (IBK5) | `Ibk5BuildDen`: build (`fromRdfQuads`, `toWire`), write, read; when the lookup resolves each object, `den? = some (DatasetDen.ofQuads qs [])` | `IndexedBlockWireV5.den?_fromRdfQuads`, `IndexedBlockWireV5.den?_decode_encode?` |
| `storeSearchStage gb d gn hx` | `PatternBound` → `List Triple` | `SearchContract d gn`: the rows are the triples of graph `gn` of `d` that match the bound, up to RDF term equality, each once | `capsOfBackend_exact`, `backendSearch_exact`, `backendSearch_nodupKeys` |
| `indexedDefaultSearchStage ds hset` | `PatternBound` → `List Triple` | `SearchContract ds.den none` | `capsOfIndexed_default_denotes` |

The write and read stages of a block (`ibk4EncodeStage`, `ibk4DecodeStage`,
and so on) are separate stages. Their composition is the round-trip stage, and
its contract follows from `Stage.comp_ok_contract`.

## SBM11 delta overlay: what remains open

* DELETE has no `HeldFolded` hypothesis: `heldFolded_sbm11`
  (`Storage/Sbm11/HeldFoldedTheorems.lean`) proves it from `MemGen.keysOk` and
  `MemGen.idOkB`. The stage takes the dictionary checks `vocabOk`, `idOkB` and
  `keysOk` as parameters, and the contract of DELETE takes the condition that
  the ids of the row and of every row that the overlay holds are in use.
* The vocabulary is `vocabAddAll keys [] ts`. That the IO steps of the harness
  (`Session.idOrNew`) compute this vocabulary is not proved
  (`OverlayDict.lean`).
* CLEAR and DROP have no denotation theorem; their contract is only
  `out = step st op`.
* A log of several entries (`Overlay.replay`) has no stage here; it is the
  fold of this stage.

## Block stores: what remains open

* The builders from RDF data have denotation theorems
  (`IndexedBlock.fromGraph_den`, `IndexedBlockWireV4.fromQuads_den`,
  `IndexedBlockWireV5.den?_fromRdfQuads`; `Storage/BlockDenotation.lean`). The
  builders fold every term (language tags in lower case), so the rows decode
  to the folded input (`fromGraph_denotes`, `fromQuads_denotes`); the fold
  keeps `Triple.key`, so the denotation is that of the input. They need no
  `Dataset.IsSet` hypothesis.
* `encode?` can refuse a built block (for example a block over the size
  limits). The build stages then stop with an error; no theorem says when
  `encode?` of a built block succeeds.
* The IBK5 build stage takes the blob obligation (the lookup resolves the wire
  form of each object) as a premise of its contract; for the packer's own
  lookup `TermWireV2.resolve_toWire` discharges it.
* `BlockMvp.Block` is built by its record constructor: its `den` is
  `graphDen` of its rows by definition.
* An IBK4 block holds the graph names of its rows only: it cannot hold an empty
  named graph (`IndexedBlockWireV4.QuadBlock.den_names_nonempty`).
* `BlockMvp.Block` has no wire format.

## StoreCaps

`BackendExact gb G` is the law of each arm of the dispatch point
(`SPARQL/StoreBackendDenotation.lean`). For the list and index arms it follows
from `Dataset.IsSet` (`indexedDefaultSearchStage` has only that hypothesis).
For the HDT and COTTAS reader arms it is the reader law
(`BackendReadOpsExact`, `CottasReadOpsExact`), a named assumption about file
access, not proved. For the RML arm it needs `RmlPushdownInvisible` and
`RmlVirtualIsMaterialised`, which are open.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Stage
import L4Factoidal.Storage.Sbm11.HeldFoldedTheorems
import L4Factoidal.Storage.BlockDenotation
import L4Factoidal.SPARQL.StoreBackendDenotation

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF

/-! ## SBM11 delta overlay -/

section Overlay

open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Overlay
open L4Factoidal.Storage.Sbm11.OverlayDict
open L4Factoidal.Storage.Sbm11.Block (Row)

/-- The contract of one log entry, against the dataset `overlayDen dec base bn`
of the overlay before (`inp.1`) and after (`out`). -/
def OverlayStepContract (dec : Nat → Option Term) (used : Nat → Prop) (base : Row → Bool)
    (bn : Nat → Bool) (inp : State × Op) (out : State) : Prop :=
  out = step inp.1 inp.2 ∧
  match inp.2 with
  | .add q =>
      ∀ gn t, (overlayDen dec base bn out).graph gn t ↔
        (overlayDen dec base bn inp.1).graph gn t ∨
          ∃ u, rowQuad? dec q = some (gn, u) ∧ u.key = t.key
  | .remove q =>
      RowInUse used q → (∀ r, denote base inp.1 r = true → RowInUse used r) →
      ∀ gn t, (overlayDen dec base bn out).graph gn t ↔
        (overlayDen dec base bn inp.1).graph gn t ∧
          ¬ ∃ u, rowQuad? dec q = some (gn, u) ∧ u.key = t.key
  | .create g =>
      (∀ n, (overlayDen dec base bn out).names n ↔
        (overlayDen dec base bn inp.1).names n ∨ (g ≠ 0 ∧ subjAt dec g = some n)) ∧
      ∀ gn t, (overlayDen dec base bn out).graph gn t ↔ (overlayDen dec base bn inp.1).graph gn t
  | .clear _ => True
  | .drop _ => True

/-- The vocabulary that the harness builds for the overlay. -/
abbrev harnessVocab (keys : List Key) (ts : List Term) : List Term := vocabAddAll keys [] ts

/-- One SBM11 log entry applied to the overlay state, with the dictionary of
a generation and the harness vocabulary. The parameters are the dictionary
checks of the generation. -/
def sbm11OverlayStage (keys : List Key) (ts : List Term) (baseUsed : Nat → Prop)
    (hv : vocabOk keys (harnessVocab keys ts) = true)
    (hb : ∀ n, baseUsed n → MemGen.idOkB keys n = true)
    (hk : MemGen.keysOk keys = true) (base : Row → Bool) (bn : Nat → Bool) :
    Stage String (State × Op) State :=
  Stage.ofFun (fun p => step p.1 p.2)
    (OverlayStepContract (ovDec keys (harnessVocab keys ts)) (ovUsed baseUsed (harnessVocab keys ts))
      base bn)
    (by
      rintro ⟨st, op⟩
      refine ⟨rfl, ?_⟩
      cases op with
      | add q => exact fun gn t => overlayDen_add _ base bn st q gn t
      | remove q =>
        intro hq hrows gn t
        exact overlayDen_remove_sbm11_vocab keys ts baseUsed hv hb hk base bn st q hq hrows gn t
      | create g =>
        exact ⟨fun n => overlayDen_create_names _ base bn st g n,
          fun gn t => overlayDen_create_graph _ base bn st g gn t⟩
      | clear _ => trivial
      | drop _ => trivial)

/-- **INSERT DATA through the stage.** -/
theorem sbm11OverlayStage_add (keys : List Key) (ts : List Term) (baseUsed : Nat → Prop)
    (hv : vocabOk keys (harnessVocab keys ts) = true)
    (hb : ∀ n, baseUsed n → MemGen.idOkB keys n = true)
    (hk : MemGen.keysOk keys = true) (base : Row → Bool) (bn : Nat → Bool)
    (st st' : State) (q : Row)
    (h : (sbm11OverlayStage keys ts baseUsed hv hb hk base bn).run (st, .add q) = .ok st')
    (gn : Option Subject) (t : Triple) :
    (overlayDen (ovDec keys (harnessVocab keys ts)) base bn st').graph gn t ↔
      (overlayDen (ovDec keys (harnessVocab keys ts)) base bn st).graph gn t ∨
        ∃ u, rowQuad? (ovDec keys (harnessVocab keys ts)) q = some (gn, u) ∧ u.key = t.key :=
  ((sbm11OverlayStage keys ts baseUsed hv hb hk base bn).sound _ _ h).2 gn t

/-- **DELETE DATA through the stage**, with no `HeldFolded` hypothesis. -/
theorem sbm11OverlayStage_remove (keys : List Key) (ts : List Term) (baseUsed : Nat → Prop)
    (hv : vocabOk keys (harnessVocab keys ts) = true)
    (hb : ∀ n, baseUsed n → MemGen.idOkB keys n = true)
    (hk : MemGen.keysOk keys = true) (base : Row → Bool) (bn : Nat → Bool)
    (st st' : State) (q : Row)
    (h : (sbm11OverlayStage keys ts baseUsed hv hb hk base bn).run (st, .remove q) = .ok st')
    (hq : RowInUse (ovUsed baseUsed (harnessVocab keys ts)) q)
    (hrows : ∀ r, denote base st r = true → RowInUse (ovUsed baseUsed (harnessVocab keys ts)) r)
    (gn : Option Subject) (t : Triple) :
    (overlayDen (ovDec keys (harnessVocab keys ts)) base bn st').graph gn t ↔
      (overlayDen (ovDec keys (harnessVocab keys ts)) base bn st).graph gn t ∧
        ¬ ∃ u, rowQuad? (ovDec keys (harnessVocab keys ts)) q = some (gn, u) ∧ u.key = t.key :=
  ((sbm11OverlayStage keys ts baseUsed hv hb hk base bn).sound _ _ h).2 hq hrows gn t

end Overlay

/-! ## Block stores: write, then read -/

section Blocks

open L4Factoidal.Storage

/-- The bytes read back denote the dataset of the block written. -/
def BlockDenEq (b : IndexedBlock.Block) (bytes : ByteArray) : Prop :=
  ∃ d, IndexedBlockWireV3.decode bytes = some d ∧ d.den = b.den

/-- IBK3: write a block of one graph. -/
def ibk3EncodeStage : Stage String IndexedBlock.Block ByteArray where
  run b :=
    match IndexedBlockWireV3.encode? b with
    | some bytes => .ok bytes
    | none => .error "IBK3: the block is not supported by the wire format"
  contract := BlockDenEq
  sound := by
    intro b bytes h
    revert h
    cases he : IndexedBlockWireV3.encode? b with
    | none => intro h; cases h
    | some bs =>
      intro h
      cases h
      exact IndexedBlockWireV3.den_decode_encode? b _ he

/-- IBK3: read a block. -/
def ibk3DecodeStage : Stage String ByteArray IndexedBlock.Block where
  run bytes :=
    match IndexedBlockWireV3.decode bytes with
    | some d => .ok d
    | none => .error "IBK3: the bytes do not decode"
  contract bytes d := IndexedBlockWireV3.decode bytes = some d
  sound := by
    intro bytes d h
    revert h
    cases hd : IndexedBlockWireV3.decode bytes with
    | none => intro h; cases h
    | some d' => intro h; cases h; rfl

/-- IBK3: write, then read. -/
def ibk3RoundTripStage : Stage String IndexedBlock.Block IndexedBlock.Block :=
  ibk3EncodeStage.comp ibk3DecodeStage

/-- **IBK3 round trip**: the block read back denotes the dataset of the block
written. -/
theorem ibk3RoundTrip_den {b d : IndexedBlock.Block} (h : ibk3RoundTripStage.run b = .ok d) :
    d.den = b.den := by
  obtain ⟨bytes, ⟨d', hd', e⟩, hd⟩ := Stage.comp_ok_contract ibk3EncodeStage ibk3DecodeStage h
  have : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst this
  exact e

/-- IBK4: the bytes read back denote the dataset of the quad block written. -/
def Ibk4DenEq (b : IndexedBlockWireV4.QuadBlock) (bytes : ByteArray) : Prop :=
  ∃ d, IndexedBlockWireV4.decode bytes = some d ∧ d.den = b.den

/-- IBK4: write a quad block. -/
def ibk4EncodeStage : Stage String IndexedBlockWireV4.QuadBlock ByteArray where
  run b :=
    match IndexedBlockWireV4.encode? b with
    | some bytes => .ok bytes
    | none => .error "IBK4: the block is not supported by the wire format"
  contract := Ibk4DenEq
  sound := by
    intro b bytes h
    revert h
    cases he : IndexedBlockWireV4.encode? b with
    | none => intro h; cases h
    | some bs =>
      intro h
      cases h
      exact IndexedBlockWireV4.den_decode_encode? b _ he

/-- IBK4: read a quad block. -/
def ibk4DecodeStage : Stage String ByteArray IndexedBlockWireV4.QuadBlock where
  run bytes :=
    match IndexedBlockWireV4.decode bytes with
    | some d => .ok d
    | none => .error "IBK4: the bytes do not decode"
  contract bytes d := IndexedBlockWireV4.decode bytes = some d
  sound := by
    intro bytes d h
    revert h
    cases hd : IndexedBlockWireV4.decode bytes with
    | none => intro h; cases h
    | some d' => intro h; cases h; rfl

/-- IBK4: write, then read. -/
def ibk4RoundTripStage : Stage String IndexedBlockWireV4.QuadBlock IndexedBlockWireV4.QuadBlock :=
  ibk4EncodeStage.comp ibk4DecodeStage

/-- **IBK4 round trip**: the quad block read back denotes the dataset of the
block written. -/
theorem ibk4RoundTrip_den {b d : IndexedBlockWireV4.QuadBlock} (h : ibk4RoundTripStage.run b = .ok d) :
    d.den = b.den := by
  obtain ⟨bytes, ⟨d', hd', e⟩, hd⟩ := Stage.comp_ok_contract ibk4EncodeStage ibk4DecodeStage h
  have : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst this
  exact e

/-- IBK5: the bytes read back denote, for the hash `h` and the blob lookup
`lookup`, what the block written denotes. -/
def Ibk5DenEq (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    (b : IndexedBlockWireV5.QuadBlock) (bytes : ByteArray) : Prop :=
  ∃ d, IndexedBlockWireV5.decode bytes = some d ∧ d.den? h lookup = b.den? h lookup

/-- IBK5: write a quad block. -/
def ibk5EncodeStage (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray) :
    Stage String IndexedBlockWireV5.QuadBlock ByteArray where
  run b :=
    match IndexedBlockWireV5.encode? b with
    | some bytes => .ok bytes
    | none => .error "IBK5: the block is not supported by the wire format"
  contract := Ibk5DenEq h lookup
  sound := by
    intro b bytes hr
    revert hr
    cases he : IndexedBlockWireV5.encode? b with
    | none => intro hr; cases hr
    | some bs =>
      intro hr
      cases hr
      exact IndexedBlockWireV5.den?_decode_encode? h lookup b _ he

/-- IBK5: read a quad block. -/
def ibk5DecodeStage : Stage String ByteArray IndexedBlockWireV5.QuadBlock where
  run bytes :=
    match IndexedBlockWireV5.decode bytes with
    | some d => .ok d
    | none => .error "IBK5: the bytes do not decode"
  contract bytes d := IndexedBlockWireV5.decode bytes = some d
  sound := by
    intro bytes d hr
    revert hr
    cases hd : IndexedBlockWireV5.decode bytes with
    | none => intro hr; cases hr
    | some d' => intro hr; cases hr; rfl

/-- IBK5: write, then read. -/
def ibk5RoundTripStage (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray) :
    Stage String IndexedBlockWireV5.QuadBlock IndexedBlockWireV5.QuadBlock :=
  (ibk5EncodeStage h lookup).comp ibk5DecodeStage

/-- **IBK5 round trip.** -/
theorem ibk5RoundTrip_den (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    {b d : IndexedBlockWireV5.QuadBlock} (hr : (ibk5RoundTripStage h lookup).run b = .ok d) :
    d.den? h lookup = b.den? h lookup := by
  obtain ⟨bytes, ⟨d', hd', e⟩, hd⟩ :=
    Stage.comp_ok_contract (ibk5EncodeStage h lookup) ibk5DecodeStage hr
  have : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst this
  exact e

/-! ## Block stores: build from RDF data, write, then read -/

/-- IBK3: the block built from the graph `g`, written and read back, denotes
`g`. -/
def Ibk3BuildDen (g : Graph) (d : IndexedBlock.Block) : Prop := d.den = graphDen g

/-- IBK3: build a block from a graph. -/
def ibk3BuildStage : Stage String Graph IndexedBlock.Block :=
  Stage.ofFun IndexedBlock.fromGraph Ibk3BuildDen IndexedBlock.fromGraph_den

/-- IBK3: build, write, then read. -/
def ibk3BuildWriteReadStage : Stage String Graph IndexedBlock.Block where
  run := (ibk3BuildStage.comp ibk3RoundTripStage).run
  contract := Ibk3BuildDen
  sound := by
    intro g d h
    obtain ⟨b, hb, bytes, ⟨d', hd', e⟩, hd⟩ := Stage.comp_ok_contract ibk3BuildStage ibk3RoundTripStage h
    have : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst this
    exact e.trans hb

/-- **IBK3 build, write, read**: the block read back denotes the graph. -/
theorem ibk3BuildWriteRead_den {g : Graph} {d : IndexedBlock.Block}
    (h : ibk3BuildWriteReadStage.run g = .ok d) : d.den = graphDen g :=
  ibk3BuildWriteReadStage.sound g d h

/-- IBK4: the block built from the quads `qs`, written and read back, denotes
`qs`. -/
def Ibk4BuildDen (qs : List (Option Subject × Triple)) (d : IndexedBlockWireV4.QuadBlock) : Prop :=
  d.den = DatasetDen.ofQuads qs []

/-- IBK4: build a block from quads. -/
def ibk4BuildStage : Stage String (List (Option Subject × Triple)) IndexedBlockWireV4.QuadBlock :=
  Stage.ofFun IndexedBlockWireV4.fromQuads Ibk4BuildDen IndexedBlockWireV4.fromQuads_den

/-- IBK4: build, write, then read. -/
def ibk4BuildWriteReadStage : Stage String (List (Option Subject × Triple)) IndexedBlockWireV4.QuadBlock where
  run := (ibk4BuildStage.comp ibk4RoundTripStage).run
  contract := Ibk4BuildDen
  sound := by
    intro qs d h
    obtain ⟨b, hb, bytes, ⟨d', hd', e⟩, hd⟩ := Stage.comp_ok_contract ibk4BuildStage ibk4RoundTripStage h
    have : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst this
    exact e.trans hb

/-- **IBK4 build, write, read**: the block read back denotes the quads. -/
theorem ibk4BuildWriteRead_den {qs : List (Option Subject × Triple)} {d : IndexedBlockWireV4.QuadBlock}
    (h : ibk4BuildWriteReadStage.run qs = .ok d) : d.den = DatasetDen.ofQuads qs [] :=
  ibk4BuildWriteReadStage.sound qs d h

/-- **A dataset through IBK4**: a dataset with no empty named graph, built
from its quads, written and read back, denotes the dataset. -/
theorem ibk4BuildWriteRead_dataset {ds : Dataset} {d : IndexedBlockWireV4.QuadBlock}
    (hne : ∀ ng ∈ ds.named, ng.graph ≠ [])
    (h : ibk4BuildWriteReadStage.run ds.listQuads = .ok d) : d.den = ds.den :=
  (ibk4BuildWriteRead_den h).trans
    ((IndexedBlockWireV4.fromQuads_den _).symm.trans (IndexedBlockWireV4.fromQuads_listQuads_den ds hne))

/-- IBK5: when the lookup resolves the wire form of each object, the block
built from the RDF quads `qs`, written and read back, denotes `qs`. -/
def Ibk5BuildDen (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    (qs : List (Option Subject × Triple)) (d : IndexedBlockWireV5.QuadBlock) : Prop :=
  (∀ q ∈ qs, TermWireV2.resolve h lookup (TermWireV2.toWire h q.2.o) = some q.2.o) →
    d.den? h lookup = some (DatasetDen.ofQuads qs [])

/-- IBK5: build a block from RDF quads (`toWire` chooses inline or blob). -/
def ibk5BuildStage (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray) :
    Stage String (List (Option Subject × Triple)) IndexedBlockWireV5.QuadBlock :=
  Stage.ofFun (IndexedBlockWireV5.fromRdfQuads h) (Ibk5BuildDen h lookup)
    (fun qs hl => IndexedBlockWireV5.den?_fromRdfQuads h lookup qs hl)

/-- IBK5: build, write, then read. -/
def ibk5BuildWriteReadStage (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray) :
    Stage String (List (Option Subject × Triple)) IndexedBlockWireV5.QuadBlock where
  run := ((ibk5BuildStage h lookup).comp (ibk5RoundTripStage h lookup)).run
  contract := Ibk5BuildDen h lookup
  sound := by
    intro qs d hr
    obtain ⟨b, hb, bytes, ⟨d', hd', e⟩, hd⟩ :=
      Stage.comp_ok_contract (ibk5BuildStage h lookup) (ibk5RoundTripStage h lookup) hr
    have : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst this
    intro hl
    exact e.trans (hb hl)

/-- **IBK5 build, write, read**: for a lookup that resolves each object, the
block read back denotes the quads. -/
theorem ibk5BuildWriteRead_den (h : ByteArray → ByteArray) (lookup : ByteArray → Option ByteArray)
    {qs : List (Option Subject × Triple)} {d : IndexedBlockWireV5.QuadBlock}
    (hr : (ibk5BuildWriteReadStage h lookup).run qs = .ok d)
    (hl : ∀ q ∈ qs, TermWireV2.resolve h lookup (TermWireV2.toWire h q.2.o) = some q.2.o) :
    d.den? h lookup = some (DatasetDen.ofQuads qs []) :=
  (ibk5BuildWriteReadStage h lookup).sound qs d hr hl

end Blocks

/-! ## StoreCaps: a search against the denotation -/

section Caps

open L4Factoidal.SPARQL (PatternBound boundMatches)
open L4Factoidal.SPARQL.StoreBackend

/-- The rows of a search of graph `gn` of `d` with the bound `b`: the triples
of that graph that match `b`, up to RDF term equality (`KeyMem`), and no two
rows RDF-term-equal. -/
def SearchContract (d : DatasetDen) (gn : Option Subject) (b : PatternBound) (out : List Triple) :
    Prop :=
  (∀ t, KeyMem out t ↔ d.graph gn t ∧ boundMatches b t = true) ∧ (out.map Triple.key).Nodup

/-- A search of a backend through its `StoreCaps` record (`capsOfBackend`),
for a backend whose arm law holds for graph `gn` of `d`. -/
def storeSearchStage (gb : GraphBackend) (d : DatasetDen) (gn : Option Subject)
    (hx : BackendExact gb (d.graph gn)) : Stage String PatternBound (List Triple) :=
  Stage.ofFun (fun b => backendSearch gb b) (SearchContract d gn)
    (fun b => ⟨backendSearch_exact hx b, backendSearch_nodupKeys hx b⟩)

/-- The law of the index arm for the default graph of a dataset that is a set. -/
theorem backendExact_indexed_default {ds : Dataset} (hset : ds.IsSet) :
    BackendExact (.indexed (OWL.RL.Index.ofGraph ds.default)) (ds.den.graph none) :=
  ⟨ds.default, OWL.RL.Index.Wf.ofGraph _, hset.default, Dataset.den_default_iff_keyMem (ds := ds)⟩

/-- A search of the in-memory index of the default graph of a dataset that is
a set. Its only hypothesis is `Dataset.IsSet`. -/
def indexedDefaultSearchStage (ds : Dataset) (hset : ds.IsSet) :
    Stage String PatternBound (List Triple) :=
  storeSearchStage (.indexed (OWL.RL.Index.ofGraph ds.default)) ds.den none
    (backendExact_indexed_default hset)

/-- **A search of the default graph returns the matching triples of the
dataset's default graph, each once.** -/
theorem indexedDefaultSearch_sound {ds : Dataset} (hset : ds.IsSet) {b : PatternBound}
    {out : List Triple} (h : (indexedDefaultSearchStage ds hset).run b = .ok out) :
    SearchContract ds.den none b out :=
  (indexedDefaultSearchStage ds hset).sound b out h

end Caps

#print axioms sbm11OverlayStage
#print axioms sbm11OverlayStage_add
#print axioms sbm11OverlayStage_remove
#print axioms ibk3RoundTrip_den
#print axioms ibk4RoundTrip_den
#print axioms ibk5RoundTrip_den
#print axioms ibk3BuildWriteReadStage
#print axioms ibk3BuildWriteRead_den
#print axioms ibk4BuildWriteReadStage
#print axioms ibk4BuildWriteRead_den
#print axioms ibk4BuildWriteRead_dataset
#print axioms ibk5BuildWriteReadStage
#print axioms ibk5BuildWriteRead_den
#print axioms storeSearchStage
#print axioms backendExact_indexed_default
#print axioms indexedDefaultSearch_sound

end L4Factoidal.Dataflow
