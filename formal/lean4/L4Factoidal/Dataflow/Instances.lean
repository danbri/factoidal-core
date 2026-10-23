/-
L4Factoidal.Dataflow.Instances — the first stages of the system, made from
theorems that exist, and one end-to-end composition
(https://github.com/danbri/factoidal/issues/975, phase A3).

This module proves no new property of a component. Each stage's `sound` is an
existing theorem; the only new lemmas are hand-over facts about the wire types
(`SetOf.den_eq`, `inputDen_qsOf`, `Sbm11Folded.*`).

## Stages

| stage | in → out | contract | from |
|---|---|---|---|
| `decodeStage` | `Document` → `RdfFormat × String` | `DecodeContract`: the media type (or, when it is absent, the registered extension of the source) gives the format, the text is the UTF-8 decoding of the bytes | `RDF.formatOfDocument`, `String.fromUTF8?` (core) |
| `parseStage` | `RdfFormat × String` → `Dataset` | `ParseContract`: a set, with the denotation of the raw parse | `Source.parseDocument_set`, `Dataset.memQuad_toSet` |
| `sbm11PackStage` | `Dataset` → `MemGen × FileGen` | `PackContract`: the generation denotes the dataset, the files hold the bytes the encoders write, and the generation answers as the dataset | `den_packSpec`, `packSpec_written`, `packSpec_check`, `AllowedPerm.allowed_perm` |
| `sbm11Disk` (IO) | `FileGen` → `FileGen` | `ReadsWritten`: the bytes read are the bytes written | named assumption |
| `sbm11WhereStage` | `MemGen × FileGen` → harness output | `WhereContract`: the WHERE answer is an answer SPARQL 1.1 allows over the generation | `harness_where_allowed_file` |
| `sbm11DecodeStage` | harness output → `SolutionSeq` | `DecodeRowsContract`: the rows decoded with any decoder that agrees with the output store | `decodeRowsM_run` |
| `plannerSelectStage` | `Dataset` → `SolutionSeq` | `PlannerSelectContract`: the answer over the kept entries is the answer over all entries | `plannerSoundnessSelect` |
| `sbm11SelectedRead` (IO) | `MemGen × FileGen` → `Dataset` | `SelectedAgrees`: after the restriction, the dataset read is the generation's | named assumption |
| `proofCheckStage` | `FPP0.Bundle` → `Claim` | `CheckContract`: accept implies the claim is derivable from the merge | `checkBundle_merge` |
| `rdfsClosureStage` | `Graph` → `Graph` | `RdfsEntails`: the closure is RDFS-entailed | `fullClosure_entails` |

## The end-to-end composition

`documentToWhere` is `decodeStage`, then `parseStage`, then `sbm11PackStage`,
then `sbm11Disk` on the files, then `sbm11WhereStage`.
`documentToWhere_sound` states what a successful run gives.
`documentToSolutions` adds `sbm11DecodeStage`; `documentToSolutions_sound`
ends at `SolutionSeq`. `sbm11PlannerSelect` is the reference fallback of
`l4sbm11 query`: `sbm11SelectedRead`, then `plannerSelectStage`
(`sbm11PlannerSelect_sound`). The premises of `documentToWhere_sound`:

* `ReadsWritten` (named IO assumption, `sbm11Disk.Realised readBack`);
* the parameters of the WHERE stage: `plan.nested = some p` and
  `plan.dataset = none` (the harness theorem's hypotheses on the plan);
* inside the conclusion, for the answer: `QHyps G.cid p` (the harness
  theorem's hypothesis on the query and the generation's ids);
* inside the conclusion, for the answer over the PARSED dataset:
  `Sbm11Folded ds` and `PermOk p` (the hypotheses of
  `harness_where_allowed_den` / `allowed_perm`).

## Hand-over findings

1. Media type (closed). `decodeStage` uses `RDF.formatOfDocument`
   (`RDF/MediaType.lean`): the six registered media types, parameters
   allowed, and the registered extension of the source only when the media
   type is absent. `decodeParse_mediaType`: a known media type gives the
   format whose parser the parse stage calls. The shipped CLI and harness
   paths take format labels (`formatOfLabel`) and do not read a media type,
   so no runtime path changed. `SPARQL/GraphStoreService.lean`,
   `SPARQL/Protocol.lean` and the Solid modules keep their own lists.
2. Blank-node scope. `Document.source` is not an input of any parser
   contract. Blank nodes are labels; two documents that use `_:b` give the
   same term. Phase C of issue 975.
3. Language-tag case, parse → SBM11. The packer folds language tags, so the
   generation denotes the parsed dataset with no hypothesis (`den_packSpec`).
   But the transfer of SPARQL answers from the generation to the parsed
   dataset (`allowed_perm` through `harness_where_allowed_den`) needs
   `Sbm11Folded ds`: every triple of the parsed dataset is its own join key
   and its own `normTriple`. No parser theorem gives it, and a document with
   `"x"@EN` breaks it (`InstancesTests.lean`). So the end-to-end answer over
   the parsed dataset is conditional on that premise.
4. Id table → solution sequence (closed). The WHERE stage's output carries
   the store with the query-local vocabulary, and that is enough:
   `sbm11DecodeStage` runs `decodeRowsM` on it (the shipped nested path), and
   `documentToSolutions_sound` proves that the decoded rows are
   `t.idRows.map (decRow (decV G.dec s.vocab))`, the sequence that `WhereOk`
   allows (`termOf_withLocal`, `store_written`, `mem_htermOf`, `mem_hloc`).
5. Reasoners take one graph. `rdfsClosureStage` maps `Graph` to `Graph`;
   there is no stage from `Dataset` (RDF 1.1 Semantics defines entailment on
   graphs; a dataset regime is a choice, not stated here).
6. Planner stage input (partly closed). The planner SELECT stage is on the
   shipped path: the reference fallback of `l4sbm11 query` reads a dataset
   from the generation (`selectedDataset`) and runs it. `sbm11PlannerSelect`
   composes the read (IO, named assumption `SelectedAgrees`) with
   `plannerSelectStage`; `sbm11PlannerSelect_sound` gives the planner answer
   over `G.denote`. Missing: a pure model of `selectedDataset` over `FileGen`
   with a proof of `SelectedAgrees`; the planner theorem needs non-empty
   named graphs, and the read keeps a named graph that the predicate
   selection empties; and no theorem relates the planner answer over
   `G.denote` to the id path's answer or to the answer over the parsed
   dataset (`G.den = ds.den` is equality of denotations, not of lists).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Stage
import L4Factoidal.RDF.MediaType
import L4Factoidal.RDF.Source
import L4Factoidal.Storage.Sbm11.SubSelectTableTheorems
import L4Factoidal.Storage.Sbm11.DenotationTheorems
import L4Factoidal.Storage.Sbm11.FileGenTheorems
import L4Factoidal.Storage.PlannerSoundness
import L4Factoidal.Proof.Checker
import L4Factoidal.RDF.EntailmentRegimeSoundness

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDF.Source
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.PackSpec
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (nestedTableM queryEnvOf Allowed NSt)
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (WhereOk)
open L4Factoidal.Storage.Sbm11.LocalVocab
open L4Factoidal.Storage.Sbm11.AllowedPerm

/-! ## Decode: bytes to text -/

/-- The document's media type gives the format (the registered extension of
its source when the media type is absent: `RDF.formatOfDocument`), and the
text is the UTF-8 decoding of its bytes. -/
def DecodeContract (d : Document) (out : RdfFormat × String) : Prop :=
  formatOfDocument d.mediaType d.source = some out.1 ∧ out.2.toUTF8 = d.bytes

theorem fromUTF8?_toUTF8 {b : ByteArray} {s : String} (h : String.fromUTF8? b = some s) :
    s.toUTF8 = b := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

def decodeStage : Stage String Document (RdfFormat × String) where
  run d :=
    match formatOfDocument d.mediaType d.source, String.fromUTF8? d.bytes with
    | some f, some s => .ok (f, s)
    | none, _ => .error s!"{d.source}: no RDF format for media type '{d.mediaType}'"
    | some _, none => .error s!"{d.source}: the bytes are not UTF-8"
  contract := DecodeContract
  sound := by
    intro d out h
    revert h
    cases hf : formatOfDocument d.mediaType d.source with
    | none => intro h; cases h
    | some f =>
      cases hs : String.fromUTF8? d.bytes with
      | none => intro h; cases h
      | some s =>
        intro h
        cases h
        exact ⟨hf, fromUTF8?_toUTF8 hs⟩

/-! ## Parse: text to a dataset -/

/-- `SetOf` keeps the denotation. -/
theorem SetOf.den_eq {ds raw : Dataset} (h : SetOf ds raw) : ds.den = raw.den :=
  DatasetDen.ext (fun gn t => h.memQuad t gn) (fun n => h.names n)

/-- The parser's output is a set, it is the set of quads of the raw parse of
the format, and it has the raw parse's denotation. -/
def ParseContract (extra : Extra) (mode : Syntax.Mode) (base : Option String)
    (inp : RdfFormat × String) (ds : Dataset) : Prop :=
  ∃ raw, parseDocumentRaw extra inp.1 mode base inp.2 = .ok raw ∧ SetOf ds raw ∧ ds.IsSet ∧
    ds.den = raw.den

def parseStage (extra : Extra) (mode : Syntax.Mode) (base : Option String) :
    Stage String (RdfFormat × String) Dataset where
  run inp :=
    match parseDocument extra inp.1 mode base inp.2 with
    | .ok ds => .ok ds
    | .error e => .error e.msg
  contract := ParseContract extra mode base
  sound := by
    rintro ⟨f, s⟩ ds h
    revert h
    show (match parseDocument extra f mode base s with
      | .ok ds => (.ok ds : Except String Dataset) | .error e => .error e.msg) = .ok ds → _
    cases hp : parseDocument extra f mode base s with
    | error e => intro h; cases h
    | ok ds' =>
      intro h
      injection h with h
      subst h
      obtain ⟨raw, hr, hs⟩ := parseDocument_set extra f mode base s ds' hp
      exact ⟨raw, hr, hs, hs.isSet, SetOf.den_eq hs⟩

/-- **A known media type selects the parser.** When the media type of `d`
names the format `f` (`formatOfMediaType`, parameters allowed), a successful
decode and parse of `d` is the output of `parseDocument` for `f` on the UTF-8
text of `d`; the source name is not read. -/
theorem decodeParse_mediaType (extra : Extra) (mode : Syntax.Mode) (base : Option String)
    {d : Document} {f : RdfFormat} (hf : formatOfMediaType d.mediaType = some f) {ds : Dataset}
    (h : (decodeStage.comp (parseStage extra mode base)).run d = .ok ds) :
    ∃ text : String, text.toUTF8 = d.bytes ∧ parseDocument extra f mode base text = .ok ds := by
  obtain ⟨⟨f', text⟩, hd, hp⟩ := Stage.comp_ok _ _ h
  obtain ⟨hf', hutf⟩ := decodeStage.sound d _ hd
  rw [formatOfDocument_of_mediaType d.source hf] at hf'
  have e : f' = f := by injection hf' with e; exact e.symm
  rw [e] at hp
  refine ⟨text, hutf, ?_⟩
  revert hp
  show (match parseDocument extra f mode base text with
    | .ok ds => (.ok ds : Except String Dataset) | .error e => .error e.msg) = .ok ds → _
  cases parseDocument extra f mode base text with
  | error e => intro h; cases h
  | ok ds' => intro h; injection h with h; rw [h]

/-! ## SBM11: pack, write, read back, WHERE -/

/-- The quads of a dataset in the packer's order (triple first). -/
def qsOf (ds : Dataset) : List Storage.Sbm11.PackSpec.Quad := ds.listQuads.map Prod.swap

theorem inputDen_qsOf (ds : Dataset) : inputDen (qsOf ds) ds.names = ds.den := by
  rw [Dataset.den_eq_ofQuads, inputDen, qsOf, List.map_map]
  have : (Prod.swap ∘ Prod.swap : Option Subject × Triple → Option Subject × Triple) = id := by
    funext x; rfl
  rw [this, List.map_id]

/-- Every triple of the dataset is its own join key and its own `normTriple`:
the form in which SBM11 holds terms (language tags in lower case). This is a
hand-over condition between a parser and SBM11 (module header, finding 3). -/
def Sbm11Folded (ds : Dataset) : Prop :=
  ∀ u gn, ds.listQuad u gn → normTriple u = u ∧ u.key = u

theorem Sbm11Folded.listQuad_qsOf {ds : Dataset} {q : Storage.Sbm11.PackSpec.Quad} (hq : q ∈ qsOf ds) :
    ds.listQuad q.1 q.2 := by
  rw [qsOf, List.mem_map] at hq
  obtain ⟨⟨gn, u⟩, hm, rfl⟩ := hq
  exact (ds.mem_listQuads gn u).mp hm

theorem Sbm11Folded.norm {ds : Dataset} (h : Sbm11Folded ds) :
    ∀ q ∈ qsOf ds, normTriple q.1 = q.1 :=
  fun _ hq => (h _ _ (Sbm11Folded.listQuad_qsOf hq)).1

theorem Sbm11Folded.fix {ds : Dataset} (h : Sbm11Folded ds) :
    ∀ q ∈ qsOf ds, q.1.o.joinKey = q.1.o := fun q hq => by
  have e := (h _ _ (Sbm11Folded.listQuad_qsOf hq)).2
  exact congrArg Triple.o e

theorem Sbm11Folded.keyD {ds : Dataset} (h : Sbm11Folded ds) :
    ∀ u gn, ds.listQuad u gn → u.key = u := fun u gn hu => (h u gn hu).2

/-- What the pack step guarantees about the generation `G` and its files `F`
made from the dataset `ds`. -/
structure PackContract (ds : Dataset) (G : MemGen) (F : FileGen) : Prop where
  /-- The generation denotes the dataset (`den_packSpec`). -/
  den : G.den = ds.den
  /-- The files hold the bytes the encoders write for `G` (`packSpec_written`). -/
  written : Written G F
  /-- No blocks in permutations 4 and above (`packSpec_written`). -/
  noHigh : ∀ p, 4 ≤ p → G.ms p = []
  /-- The generation passes its check (`packSpec_check`). -/
  check : G.check = true
  /-- An answer that SPARQL 1.1 allows over the generation is one it allows
  over the dataset, when the dataset is a set in the form SBM11 holds and the
  pattern is in the fragment of `PermOk` (`allowed_perm`). -/
  answers : ds.IsSet → Sbm11Folded ds → ∀ (clock : EvalEnv) (base : Option String)
    (p : QueryPattern) (A : SolutionSeq), PermOk p →
    Allowed { queryEnvOf clock base with dataset := some G.denote } G.denote p G.denote.default A →
    Allowed { queryEnvOf clock base with dataset := some ds } ds p ds.default A

theorem packContract_of (B : Nat) (ds : Dataset) (G : MemGen) (F : FileGen)
    (h : packSpec B (qsOf ds) ds.names = some (G, F)) : PackContract ds G F := by
  obtain ⟨hw, h4⟩ := packSpec_written B (qsOf ds) ds.names G F h
  refine ⟨?_, hw, h4, packSpec_check B (qsOf ds) ds.names G F h, ?_⟩
  · rw [den_packSpec B (qsOf ds) ds.names G F h, inputDen_qsOf]
  · intro hset hfold clock base p A hp hA
    have hD : DatasetOf (qsOf ds) ds.names ds :=
      datasetOf_of_den (qsOf ds) ds.names ds hset (Sbm11Folded.keyD hfold) (Sbm11Folded.fix hfold) (inputDen_qsOf ds).symm
    exact allowed_perm (env := { queryEnvOf clock base with dataset := some G.denote })
      (env' := { queryEnvOf clock base with dataset := some ds }) ⟨rfl, rfl, rfl⟩
      (namedPerm B (qsOf ds) ds.names G F h ds hD (Sbm11Folded.norm hfold) (Sbm11Folded.fix hfold)) hA
      (default_perm B (qsOf ds) ds.names G F h ds hD (Sbm11Folded.norm hfold))
      (default_fixed B (qsOf ds) ds.names G F h (Sbm11Folded.norm hfold) (Sbm11Folded.fix hfold)) hp

def sbm11PackStage (B : Nat) : Stage String Dataset (MemGen × FileGen) where
  run ds :=
    match packSpec B (qsOf ds) ds.names with
    | some gf => .ok gf
    | none => .error "SBM11 pack: the packer refused the dataset"
  contract ds gf := PackContract ds gf.1 gf.2
  sound := by
    intro ds ⟨G, F⟩ h
    revert h
    show (match packSpec B (qsOf ds) ds.names with
      | some gf => (.ok gf : Except String (MemGen × FileGen)) | none => .error _) = .ok (G, F) → _
    cases hp : packSpec B (qsOf ds) ds.names with
    | none => intro h; cases h
    | some gf =>
      intro h
      injection h with h
      subst h
      exact packContract_of B ds _ _ hp

/-- **The named IO assumption of the SBM11 files** (`FileGenTheorems.lean`,
module header): every positioned read that `Session` makes of a file of the
generation returns the bytes that the packer wrote to that file. At the level
of `FileGen`: the bytes read back are the bytes written. The caches of
`Session` are not covered (`FileGenTheorems.lean`). -/
def ReadsWritten (written read : FileGen) : Prop := read = written

/-- The SBM11 disk: write the files, read them back. IO; its contract is the
named assumption `ReadsWritten`. -/
def sbm11Disk : IOStage String FileGen FileGen := { assumption := ReadsWritten }

/-- The output of the SBM11 WHERE harness: the id table, the store with the
query-local vocabulary, the plan lines and the scan counts. -/
abbrev WhereOut := Qlvr.Table × Store Id × Array String × ScanStats

/-- When the files hold what the encoders write for `G`, and the query's
constants meet `QHyps`, the answer is an answer SPARQL 1.1 allows over the
generation (`WhereOk`; the decoded rows use the evaluation state `s`). -/
def WhereContract (clock : EvalEnv) (base : Option String) (p : QueryPattern)
    (gf : MemGen × FileGen) (r : WhereOut) : Prop :=
  Written gf.1 gf.2 → (∀ q, 4 ≤ q → gf.1.ms q = []) → gf.1.check = true → QHyps gf.1.cid p →
    ∃ t, ∃ s : NSt, ∃ lines stats, r = (t, gf.2.store.withLocal s.vocab, lines, stats) ∧
      WhereOk { queryEnvOf clock base with dataset := some gf.1.denote } gf.1.denote gf.1.cid gf.1.dec
        gf.1.ok p gf.1.denote.default {} t s

def sbm11WhereStage (clock : EvalEnv) (base : Option String) (plan : Plan) (p : QueryPattern)
    (hnest : plan.nested = some p) (hdsq : plan.dataset = none) :
    Stage String (MemGen × FileGen) WhereOut where
  run gf := (nestedTableM gf.2.store plan (queryEnvOf clock base)).run
  contract := WhereContract clock base p
  sound := by
    rintro ⟨G, F⟩ r h
    unfold WhereContract
    intro hw h4 hG hq
    rcases harness_where_allowed_file G F hw h4 hG clock base plan p hnest hdsq hq with
      ⟨e, he, _⟩ | ⟨t, s, lines, stats, he, hok⟩
    · have h' := h
      simp only at h'
      rw [he] at h'
      cases h'
    · have h' := h
      simp only at h'
      rw [he] at h'
      cases h'
      exact ⟨t, s, lines, stats, rfl, hok⟩

/-! ## The end-to-end composition: document bytes to a WHERE answer -/

/-- Document bytes → decode → parse → SBM11 pack → disk (IO) → WHERE. -/
def documentToWhere (extra : Extra) (mode : Syntax.Mode) (docBase : Option String) (B : Nat)
    (readBack : FileGen → Except String FileGen) (hrw : sbm11Disk.Realised readBack)
    (clock : EvalEnv) (base : Option String) (plan : Plan) (p : QueryPattern)
    (hnest : plan.nested = some p) (hdsq : plan.dataset = none) : Stage String Document WhereOut :=
  ((((decodeStage.comp (parseStage extra mode docBase)).comp (sbm11PackStage B)).comp
    (Stage.second (sbm11Disk.toStage readBack hrw))).comp
    (sbm11WhereStage clock base plan p hnest hdsq))

/-- **End to end.** A successful run of `documentToWhere` on a document `d`
gives: the format and the UTF-8 text of `d`; a parsed dataset `ds` that is a
set with the denotation of the raw parse; a generation `G` that denotes `ds`;
files `F'` read back that are the files `F` written (named assumption
`ReadsWritten`); and, under the harness's hypothesis on the query `QHyps`, an
answer that SPARQL 1.1 allows over `G` and, when `ds` is in SBM11 form
(`Sbm11Folded`) and `PermOk p`, over the parsed dataset `ds` itself.

Premises: `hrw` (the named IO assumption `ReadsWritten`), `hnest` and `hdsq`
(the plan), and inside the conclusion `QHyps`, `Sbm11Folded`, `PermOk`. -/
theorem documentToWhere_sound (extra : Extra) (mode : Syntax.Mode) (docBase : Option String) (B : Nat)
    (readBack : FileGen → Except String FileGen) (hrw : sbm11Disk.Realised readBack)
    (clock : EvalEnv) (base : Option String) (plan : Plan) (p : QueryPattern)
    (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (d : Document) (r : WhereOut)
    (h : (documentToWhere extra mode docBase B readBack hrw clock base plan p hnest hdsq).run d = .ok r) :
    ∃ (fmt : RdfFormat) (text : String) (ds raw : Dataset) (G : MemGen) (F F' : FileGen),
      formatOfDocument d.mediaType d.source = some fmt ∧ text.toUTF8 = d.bytes ∧
      parseDocumentRaw extra fmt mode docBase text = .ok raw ∧ SetOf ds raw ∧ ds.den = raw.den ∧
      G.den = ds.den ∧ ReadsWritten F F' ∧ Written G F ∧ (∀ q, 4 ≤ q → G.ms q = []) ∧
      (QHyps G.cid p →
        ∃ t, ∃ s : NSt, ∃ lines stats, r = (t, F'.store.withLocal s.vocab, lines, stats) ∧
          WhereOk { queryEnvOf clock base with dataset := some G.denote } G.denote G.cid G.dec G.ok p
            G.denote.default {} t s ∧
          (Sbm11Folded ds → PermOk p →
            Allowed { queryEnvOf clock base with dataset := some ds } ds p ds.default
              (t.idRows.map (Storage.Sbm11.OptJoin.decRow (decV G.dec s.vocab))))) := by
  obtain ⟨⟨G, F'⟩, ⟨⟨G1, F⟩, ⟨ds, ⟨⟨fmt, text⟩, hdec, hpar⟩, hpack⟩, hG1, hdisk⟩, hwhere⟩ :=
    Stage.comp_ok_contract _ _ h
  obtain ⟨hlab, hutf⟩ := hdec
  obtain ⟨raw, hraw, hset, hisSet, hden⟩ := hpar
  have hG : G = G1 := hG1
  subst hG
  have hF : F' = F := hdisk
  subst hF
  refine ⟨fmt, text, ds, raw, G, F', F', hlab, hutf, hraw, hset, hden, hpack.den, rfl, hpack.written,
    hpack.noHigh, ?_⟩
  intro hq
  obtain ⟨t, s, lines, stats, hr, hok⟩ := hwhere hpack.written hpack.noHigh hpack.check hq
  exact ⟨t, s, lines, stats, hr, hok, fun hfold hp =>
    hpack.answers hisSet hfold clock base p _ hp hok.2.1⟩

/-! ## The id table to a solution sequence -/

open L4Factoidal.Storage.Sbm11.OptJoin (decRow unbound) in
/-- The decoded rows are the rows of the table decoded with any decoder `D`
that agrees with the output store's `termOf` on every bound cell. -/
def DecodeRowsContract (r : WhereOut) (sols : SolutionSeq) : Prop :=
  ∀ D : UInt64 → Term,
    (∀ i, i < r.1.rows → ∀ c, c < r.1.vars.size → r.1.at c i ≠ unbound →
      r.2.1.termOf (r.1.at c i) = pure (D (r.1.at c i))) →
    sols = r.1.idRows.map (decRow D)

/-- Decode the id table of the WHERE stage with the store it returns (the
store with the query-local vocabulary), as the shipped nested path does
(`IdGroup.runNestedM`, then `postAnswerM`, which calls `decodeRowsM`). -/
def sbm11DecodeStage : Stage String WhereOut SolutionSeq where
  run r := (decodeRowsM r.2.1 r.1).run
  contract := DecodeRowsContract
  sound := by
    intro r sols h D hD
    have e := L4Factoidal.Storage.Sbm11.SubSelect.decodeRowsM_run r.2.1 r.1 D hD
    have h' : (decodeRowsM r.2.1 r.1).run = Except.ok sols := h
    rw [e] at h'
    injection h' with h'
    exact h'.symm

/-- Document bytes → decode → parse → SBM11 pack → disk (IO) → WHERE →
decoded solutions. -/
def documentToSolutions (extra : Extra) (mode : Syntax.Mode) (docBase : Option String) (B : Nat)
    (readBack : FileGen → Except String FileGen) (hrw : sbm11Disk.Realised readBack)
    (clock : EvalEnv) (base : Option String) (plan : Plan) (p : QueryPattern)
    (hnest : plan.nested = some p) (hdsq : plan.dataset = none) : Stage String Document SolutionSeq :=
  (documentToWhere extra mode docBase B readBack hrw clock base plan p hnest hdsq).comp sbm11DecodeStage

open L4Factoidal.Storage.Sbm11.OptJoin (decRow) in
/-- **End to end, to a solution sequence.** A successful run of
`documentToSolutions` gives the facts of `documentToWhere_sound` and, under
`QHyps`, a solution sequence `sols` that is the id table decoded with the
decoder of the final evaluation state (with multiplicity, in table order), and
that SPARQL 1.1 allows over the generation and, under `Sbm11Folded` and
`PermOk`, over the parsed dataset. The decoding of the output store is proved
(`termOf_withLocal`, `store_written`), not assumed.

Premises: `hrw` (`ReadsWritten`), `hnest`, `hdsq`; inside the conclusion
`QHyps`, `Sbm11Folded`, `PermOk`. -/
theorem documentToSolutions_sound (extra : Extra) (mode : Syntax.Mode) (docBase : Option String)
    (B : Nat) (readBack : FileGen → Except String FileGen) (hrw : sbm11Disk.Realised readBack)
    (clock : EvalEnv) (base : Option String) (plan : Plan) (p : QueryPattern)
    (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (d : Document) (sols : SolutionSeq)
    (h : (documentToSolutions extra mode docBase B readBack hrw clock base plan p hnest hdsq).run d =
      .ok sols) :
    ∃ (fmt : RdfFormat) (text : String) (ds raw : Dataset) (G : MemGen),
      formatOfDocument d.mediaType d.source = some fmt ∧ text.toUTF8 = d.bytes ∧
      parseDocumentRaw extra fmt mode docBase text = .ok raw ∧ SetOf ds raw ∧ ds.den = raw.den ∧
      G.den = ds.den ∧
      (QHyps G.cid p →
        ∃ (t : Qlvr.Table) (s : NSt), sols = t.idRows.map (decRow (decV G.dec s.vocab)) ∧
          Allowed { queryEnvOf clock base with dataset := some G.denote } G.denote p
            G.denote.default sols ∧
          (Sbm11Folded ds → PermOk p →
            Allowed { queryEnvOf clock base with dataset := some ds } ds p ds.default sols)) := by
  obtain ⟨r, hw, hdec⟩ := Stage.comp_ok _ _ h
  obtain ⟨fmt, text, ds, raw, G, F, F', hlab, hutf, hraw, hset, hden, hGden, hrb, hwr, h4, hq⟩ :=
    documentToWhere_sound extra mode docBase B readBack hrw clock base plan p hnest hdsq d r hw
  refine ⟨fmt, text, ds, raw, G, hlab, hutf, hraw, hset, hden, hGden, fun hQ => ?_⟩
  obtain ⟨t, s, lines, stats, hr, hok, hds⟩ := hq hQ
  have hF : F' = F := hrb
  subst hF
  have hst : F'.store = G.store := store_written G F' hwr h4
  have hcon := sbm11DecodeStage.sound r sols hdec
  subst hr
  have hsols : sols = t.idRows.map (decRow (decV G.dec s.vocab)) := by
    apply hcon
    intro i hi c hc hx
    show (F'.store.withLocal s.vocab).termOf (t.at c i) = pure (decV G.dec s.vocab (t.at c i))
    rw [hst]
    apply termOf_withLocal G.store G.cid G.dec G.ok (mem_htermOf G) (mem_hloc G) hok.2.2.2.1
    have hrow := hok.2.2.1 (t.idRow i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    exact hrow (t.vars[c]!, t.at c i)
      (L4Factoidal.Storage.Sbm11.TableTheorems.mem_idRow.mpr ⟨c, hc, hx, rfl⟩)
  subst hsols
  exact ⟨t, s, rfl, hok.2.1, hds⟩

/-! ## SPARQL SELECT over the planner's restricted dataset -/

open L4Factoidal.Storage.PlannerSoundness in
open L4Factoidal.SPARQL.StoreDataset in
open L4Factoidal.SPARQL.DatasetRestriction in
/-- The answer of `q` over the dataset `dS` of the entries the planner kept is
its answer over the dataset `dE` of all entries, when the two agree after the
restriction `keep` and the query meets the planner's guards. -/
def PlannerSelectContract (env : EvalEnv) (q : Query) (dS : Dataset) (r : SolutionSeq) : Prop :=
  ∀ (keep : Triple → Bool) (readable : Option (List WfIri)) (dE : Dataset),
    distinctNames dE.named → (∀ ng ∈ dE.named, ng.graph ≠ []) →
    distinctNames dS.named → (∀ ng ∈ dS.named, ng.graph ≠ []) →
    restrictDataset keep dS = restrictDataset keep dE →
    plannerFragment q.pattern.rewriteBnodes = true →
    PatternKept keep q.pattern.rewriteBnodes →
    (∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i) →
    (graphVarIn q.pattern.rewriteBnodes = true → readable = none) →
    runSelectQueryBackendDataset env q (indexedDatasetBackend dE) = some r

open L4Factoidal.Storage.PlannerSoundness in
open L4Factoidal.SPARQL.StoreDataset in
def plannerSelectStage (env : EvalEnv) (q : Query) : Stage String Dataset SolutionSeq where
  run dS :=
    match runSelectQueryBackendDataset env q (indexedDatasetBackend dS) with
    | some r => .ok r
    | none => .error "query was not evaluated"
  contract := PlannerSelectContract env q
  sound := by
    intro dS r h keep readable dE hdE hneE hdS hneS hagree hf hk hn hv
    revert h
    cases hr : runSelectQueryBackendDataset env q (indexedDatasetBackend dS) with
    | none => intro h; cases h
    | some r' =>
      intro h
      cases h
      rw [← plannerSoundnessSelect env q hdE hneE hdS hneS hagree hf hk hn hv]
      exact hr

/-! ## The SBM11 generation to the planner SELECT stage

`l4sbm11 query` (`Harness/Sbm11Query.lean`) has two evaluation paths:

* the id path: a query in the id fragment (`IdQuery.translate`) runs on ids
  (`IdQuery.runPlanM`; for a nested WHERE clause `IdGroup.runNestedM`, the
  path of `documentToSolutions`);
* the reference fallback (`runReference`): every other SELECT reads a dataset
  from the generation (`selectedDataset`: the quads of the predicates the
  query names, in the graphs it reads, or every quad when the planner guard
  selects nothing) and runs
  `runSelectQueryBackendDataset env q (indexedDatasetBackend applied)`, which
  is `plannerSelectStage.run` (after `applyDataset`, when the graph names are
  IRIs).

So the planner SELECT stage is on the shipped query path, behind an IO read.
`sbm11SelectedRead` is that read, with the named assumption `SelectedAgrees`:
after the restriction `keep` of the planner guard, the dataset read is the
generation's dataset. `selectedDataset` is IO over `Session` and has no Lean
model, so this is an assumption, not a theorem (missing: a pure model of
`selectedDataset` over `FileGen` and the proof of `SelectedAgrees` for it). -/

open L4Factoidal.Storage.PlannerSoundness in
/-- **The named IO assumption of the reference fallback's read**: after the
restriction `keep`, the dataset read from the files is the dataset of the
generation. -/
def SelectedAgrees (keep : Triple → Bool) (gf : MemGen × FileGen) (dS : Dataset) : Prop :=
  restrictDataset keep dS = restrictDataset keep gf.1.denote

/-- The read of the reference fallback (`Harness.Sbm11Query.selectedDataset`).
IO; its contract is the named assumption `SelectedAgrees`. -/
def sbm11SelectedRead (keep : Triple → Bool) : IOStage String (MemGen × FileGen) Dataset :=
  { assumption := SelectedAgrees keep }

/-- SBM11 generation → selected dataset (IO) → planner SELECT. -/
def sbm11PlannerSelect (keep : Triple → Bool) (read : MemGen × FileGen → Except String Dataset)
    (hr : (sbm11SelectedRead keep).Realised read) (env : EvalEnv) (q : Query) :
    Stage String (MemGen × FileGen) SolutionSeq :=
  ((sbm11SelectedRead keep).toStage read hr).comp (plannerSelectStage env q)

open L4Factoidal.Storage.PlannerSoundness in
open L4Factoidal.SPARQL.StoreDataset in
open L4Factoidal.SPARQL.DatasetRestriction in
/-- **The reference fallback answers as over the generation.** A successful run
of `sbm11PlannerSelect` reads a dataset `dS` that meets `SelectedAgrees`, and,
when both datasets have distinct, non-empty named graphs and the query meets
the planner's guards for `keep`, its answer is the planner SELECT answer over
the whole generation `G.denote`.

Premises: `hr` (the named IO assumption `SelectedAgrees`); inside the
conclusion, the hypotheses of `plannerSoundnessSelect`. The dataset `dS` comes
from the read, so its hypotheses stay inside the conclusion. -/
theorem sbm11PlannerSelect_sound (keep : Triple → Bool)
    (read : MemGen × FileGen → Except String Dataset) (hr : (sbm11SelectedRead keep).Realised read)
    (env : EvalEnv) (q : Query) (gf : MemGen × FileGen) (r : SolutionSeq)
    (h : (sbm11PlannerSelect keep read hr env q).run gf = .ok r) :
    ∃ dS : Dataset, SelectedAgrees keep gf dS ∧
      runSelectQueryBackendDataset env q (indexedDatasetBackend dS) = some r ∧
      ∀ readable : Option (List WfIri),
        distinctNames gf.1.denote.named → (∀ ng ∈ gf.1.denote.named, ng.graph ≠ []) →
        distinctNames dS.named → (∀ ng ∈ dS.named, ng.graph ≠ []) →
        plannerFragment q.pattern.rewriteBnodes = true →
        PatternKept keep q.pattern.rewriteBnodes →
        (∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i) →
        (graphVarIn q.pattern.rewriteBnodes = true → readable = none) →
        runSelectQueryBackendDataset env q (indexedDatasetBackend gf.1.denote) = some r := by
  obtain ⟨dS, hrd, hp⟩ := Stage.comp_ok _ _ h
  have hagree : SelectedAgrees keep gf dS := hr gf dS hrd
  have hrun : runSelectQueryBackendDataset env q (indexedDatasetBackend dS) = some r := by
    revert hp
    show (match runSelectQueryBackendDataset env q (indexedDatasetBackend dS) with
      | some r => (.ok r : Except String SolutionSeq) | none => .error _) = .ok r → _
    cases runSelectQueryBackendDataset env q (indexedDatasetBackend dS) with
    | none => intro h; cases h
    | some r' => intro h; injection h with h; rw [h]
  refine ⟨dS, hagree, hrun, ?_⟩
  intro readable hdE hneE hdS hneS hf hk hn hv
  exact (plannerSelectStage env q).sound dS r (by
      show (match runSelectQueryBackendDataset env q (indexedDatasetBackend dS) with
        | some r => (.ok r : Except String SolutionSeq) | none => .error _) = .ok r
      rw [hrun]) keep readable gf.1.denote hdE hneE hdS hneS hagree hf hk hn hv

/-! ## The proof checker -/

open L4Factoidal.FPP0 in
/-- Accept implies the claim holds: an accepted bundle's conclusion
`rdfDerivable gd ad t` is `DerivesFull`-derivable (in some blank-node scope)
from the RDF 1.1 Semantics merge of the artifacts filed under `ad` and `gd`. -/
def CheckContract (b : Bundle) (c : Claim) : Prop :=
  c = b.conclusion ∧ ∀ gd ad t, c = Claim.rdfDerivable gd ad t →
    ∃ s : Scope, RDFS.DerivesFull (mergeOf b.artifacts.toList ad) (mergeOf b.artifacts.toList gd)
      (t.scoped s)

open L4Factoidal.FPP0 in
def proofCheckStage : Stage String Bundle Claim where
  run b := if (checkBundle b).foundationalOnly then .ok b.conclusion
    else .error "bundle refused or has an assumption frontier"
  contract := CheckContract
  sound := by
    intro b c h
    by_cases hf : (checkBundle b).foundationalOnly = true
    · simp only [hf, if_true] at h
      cases h
      exact ⟨rfl, fun gd ad t hc => checkBundle_merge hf hc⟩
    · simp only [hf] at h
      cases h

/-! ## RDFS closure -/

/-- The RDFS-regime closure, for a datatype list `D` and the container
membership IRIs `cmps`: the output is RDFS-entailed by the input. -/
def rdfsClosureStage (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) :
    Stage String Graph Graph :=
  Stage.ofFun (RDFS.fullClosure D cmps) (fun g g' => RdfsEntails (fun x => x ∈ D) g g')
    (fun g => fullClosure_entails D cmps hcmps g)

#print axioms fromUTF8?_toUTF8
#print axioms SetOf.den_eq
#print axioms inputDen_qsOf
#print axioms packContract_of
#print axioms decodeStage
#print axioms parseStage
#print axioms sbm11PackStage
#print axioms sbm11WhereStage
#print axioms documentToWhere_sound
#print axioms decodeParse_mediaType
#print axioms sbm11DecodeStage
#print axioms documentToSolutions_sound
#print axioms plannerSelectStage
#print axioms sbm11PlannerSelect_sound
#print axioms proofCheckStage
#print axioms rdfsClosureStage

end L4Factoidal.Dataflow
