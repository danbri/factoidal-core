/-
L4Factoidal.RDF.SourceTheorems — what the source layer proves about reading a
document in chunks.

`Source.Reader` reads a document chunk by chunk, and `Source.parseDocument`
reads the joined text at once. This file states the relations between them.

* `whole_readAll`, `jsonld_readAll`: the whole reader (JSON-LD) gives
  `parseDocument` of the joined text, folded through the consumer, for EVERY
  list of chunks. The reader keeps the chunks and parses their join, so the
  statement does not depend on the cuts.
* `rdfxml_readAll_of_notStreamed`: the RDF/XML chunk fold, when it ends in its
  prologue or fall-back phase, gives `parseDocument` of the joined text. In
  the children phase the equality is measured, not proved (row RX-1 of
  `tests/known-defects/run.sh`, https://github.com/danbri/factoidal/issues/936).
* `nquads11_readAll_eq_batch`: the N-Quads reader in RDF 1.1 mode, when it
  succeeds, gives the line walk of the joined text. It is
  `StrictFeed.LineFeed.run_quad11_eq_batch`, which is
  `NQuadsFold.streamConsume11_eq_batch` through the line walk.
* `nquads11_readAll_eq_parseNQuadsFast`: the same at the consumer that
  `parseNQuadsFast` uses, so a chunked read that succeeds gives the dataset of
  the batch parser.
* `turtleStep_collect`: the Turtle reader's consumer, with the consumer that
  collects triples newest first, is the accumulator step of `parseTurtle`
  (`Syntax.parseTurtle_eq_fold`). The shard packer for IBK2 and IBK3 folds with
  it.
* `prepass_chunks`: the pre-pass over any cut of the bytes gives the prefix of
  the whole text.

Not proved, each with an open issue and an expected-failure row in
`tests/known-defects/run.sh` (https://github.com/danbri/factoidal/issues/826,
rows SF-1 to SF-4): the Turtle chunk walk, N-Triples chunked against batch,
N-Quads in RDF 1.2 mode, and the decoding of UTF-8 in chunks. TriG chunked
against batch is https://github.com/danbri/factoidal/issues/836
(`tests/trig-pack/order_xfail.sh`). Turtle and TriG chunked against batch are
also measured, see `Source.lean`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.SourceJsonLd

namespace L4Factoidal.RDF.Source

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Syntax.NQuadsStreaming
open L4Factoidal.Syntax.StrictFeed

/-! ## The whole readers -/

theorem feed_whole {α : Type} (step : Step α) (parse : DocParser) (mode : Mode)
    (base : Option String) (acc : α) (bufRev : List String) (text : String) :
    (Reader.whole parse mode base acc bufRev).feed step text =
      .ok (Reader.whole parse mode base acc (text :: bufRev)) := rfl

/-- Feeding chunks to a whole reader keeps them, newest first. -/
theorem whole_foldlM {α : Type} (step : Step α) (parse : DocParser) (mode : Mode)
    (base : Option String) (acc : α) :
    ∀ (chunks bufRev : List String),
      chunks.foldlM (fun r c => r.feed step c) (Reader.whole parse mode base acc bufRev) =
        .ok (Reader.whole parse mode base acc (chunks.reverse ++ bufRev))
  | [], bufRev => rfl
  | c :: rest, bufRev => by
      rw [List.foldlM_cons, feed_whole]
      show List.foldlM _ _ rest = _
      rw [whole_foldlM step parse mode base acc rest (c :: bufRev)]
      simp

/-- **The whole readers.** A whole reader gives `parse` of the joined chunks,
folded through the consumer, whatever the chunks are. -/
theorem whole_readAll {α : Type} (step : Step α) (parse : DocParser) (mode : Mode)
    (base : Option String) (acc : α) (chunks : List String) :
    (Reader.whole parse mode base acc []).readAll step chunks =
      (parse mode base (String.join chunks)).map (foldDataset step acc) := by
  simp only [Reader.readAll]
  rw [whole_foldlM]
  simp [Reader.finish, Reader.finishD]

/-- RDF/XML, the fall-back: when the chunk fold (`RdfXmlChunkFold`) ends in
its prologue or fall-back phase, the reader that `init` gives reads
`parseDocument` of the joined chunks. When it reads item by item the equality
is measured (`l4rdfxml-chunk-diff`) and not proved: row RX-1 of
`tests/known-defects/run.sh`, https://github.com/danbri/factoidal/issues/936. -/
theorem rdfxml_readAll_of_notStreamed {α : Type} (extra : Extra) (mode : Mode)
    (base : Option String) (bnodePrefix : String) (acc : α) (step : Step α)
    (chunks : List String) (s : RdfXmlChunkFold.State α)
    (hf : chunks.foldlM (fun (s : RdfXmlChunkFold.State α) c => s.feed (fun a t => step a t none) c)
      (RdfXmlChunkFold.State.init base acc) = .ok s)
    (hn : s.notStreamed = true) :
    ∃ r, Reader.init extra .rdfxml mode base bnodePrefix acc = .ok r ∧
      r.readAll step chunks =
        (parseDocument extra .rdfxml mode base (String.join chunks)).map (foldDataset step acc) := by
  refine ⟨.rdfxml (RdfXmlChunkFold.State.init base acc), rfl, ?_⟩
  have hfeed : ∀ (cs : List String) (st : RdfXmlChunkFold.State α),
      cs.foldlM (fun (r : Reader α) c => r.feed step c) (Reader.rdfxml st) =
        (cs.foldlM (fun (s : RdfXmlChunkFold.State α) c => s.feed (fun a t => step a t none) c) st).map
          Reader.rdfxml := by
    intro cs
    induction cs with
    | nil => intro st; rfl
    | cons c rest ih =>
      intro st
      rw [List.foldlM_cons, List.foldlM_cons]
      simp only [Reader.feed, Reader.feedD]
      cases h : st.feed (fun a t => step a t none) c with
      | error e => rfl
      | ok s1 => exact ih s1
  have hw := RdfXmlChunkFold.readAll_eq_whole_of_notStreamed (fun a t => step a t none) base acc
    chunks s hf hn
  simp only [RdfXmlChunkFold.readAll, hf] at hw
  simp only [Reader.readAll, hfeed, hf, Except.map, Reader.finish, Reader.finishD]
  rw [hw]
  simp only [RdfXmlChunkFold.readWhole, parseDocument, rdfXmlParser]
  cases RdfXml.parseRdfXml (String.join chunks) base with
  | error e => rfl
  | ok g => rfl

/-- JSON-LD, the fall-back: when the caller linked a parser and the
generated-prefix argument is not `JsonLdChunkFold.streamPrefix` (the pre-pass
found the document not in streaming form, or the caller ran none), the reader
that `init` gives reads `parseDocument` of the joined chunks, for every list of
chunks. When the argument is `streamPrefix` the reader reads one top-level node
object at a time; the equality is measured (`l4jsonld-chunk-diff`) and not
proved: row JS-1 of `tests/known-defects/run.sh`,
https://github.com/danbri/factoidal/issues/946. -/
theorem jsonld_readAll_of_notStreamed {α : Type} (extra : Extra) (parse : DocParser)
    (hx : extra.jsonld = some parse) (mode : Mode) (base : Option String)
    (bnodePrefix : String) (hp : (bnodePrefix == JsonLdChunkFold.streamPrefix) = false)
    (acc : α) (step : Step α) (chunks : List String) :
    ∃ r, Reader.init extra .jsonld mode base bnodePrefix acc = .ok r ∧
      r.readAll step chunks =
        (parseDocument extra .jsonld mode base (String.join chunks)).map (foldDataset step acc) := by
  refine ⟨.whole parse mode base acc [], ?_, ?_⟩
  · simp only [Reader.init, hx, hp]
    cases extra.jsonldStream <;> simp
  · rw [whole_readAll]
    simp [parseDocument, hx]

/-- JSON-LD without the item reader linked: always the whole reader. -/
theorem jsonld_readAll {α : Type} (extra : Extra) (parse : DocParser)
    (hx : extra.jsonld = some parse) (hs : extra.jsonldStream = none) (mode : Mode)
    (base : Option String) (bnodePrefix : String) (acc : α) (step : Step α)
    (chunks : List String) :
    ∃ r, Reader.init extra .jsonld mode base bnodePrefix acc = .ok r ∧
      r.readAll step chunks =
        (parseDocument extra .jsonld mode base (String.join chunks)).map (foldDataset step acc) := by
  refine ⟨.whole parse mode base acc [], ?_, ?_⟩
  · simp [Reader.init, hx, hs]
  · rw [whole_readAll]
    simp [parseDocument, hx]

/-! ## N-Quads, RDF 1.1 -/

theorem feed_nquads {α : Type} (step : Step α) (mode : Mode) (s : LineFeed α) (text : String) :
    (Reader.nquads mode s).feed step text =
      (LineFeed.feed (quadReader mode) step s text.toList).map (Reader.nquads mode) := rfl

/-- The chunks of a document as the line walk takes them. -/
theorem nquads_foldlM {α : Type} (step : Step α) (mode : Mode) :
    ∀ (chunks : List String) (s : LineFeed α),
      chunks.foldlM (fun r c => r.feed step c) (Reader.nquads mode s) =
        ((chunks.map String.toList).foldlM (LineFeed.feed (quadReader mode) step) s).map
          (Reader.nquads mode)
  | [], s => rfl
  | c :: rest, s => by
      rw [List.foldlM_cons, feed_nquads, List.map_cons, List.foldlM_cons]
      cases hf : LineFeed.feed (quadReader mode) step s c.toList with
      | error e => rfl
      | ok s1 =>
          show List.foldlM _ _ rest = _
          exact nquads_foldlM step mode rest s1

/-- The N-Quads reader is `LineFeed.run` on the character lists of the chunks. -/
theorem nquads_readAll_eq_run {α : Type} (step : Step α) (mode : Mode) (init : α)
    (chunks : List String) :
    (Reader.nquads mode { acc := init }).readAll step chunks =
      LineFeed.run (quadReader mode) step init (chunks.map String.toList) := by
  simp only [Reader.readAll, LineFeed.run]
  rw [nquads_foldlM]
  cases (chunks.map String.toList).foldlM (LineFeed.feed (quadReader mode) step) { acc := init } with
  | error e => rfl
  | ok s => rfl

/-- The characters of the chunks are the characters of their join. -/
theorem flatten_toList_eq_join (chunks : List String) :
    (chunks.map String.toList).flatten = (String.join chunks).toList := by
  induction chunks with
  | nil => simp
  | cons c rest ih => simp [String.join_cons, String.toList_append, ih]

/-- **N-Quads, RDF 1.1.** A chunked read that succeeds gives what the line walk
of the whole text gives, for every consumer. -/
theorem nquads11_readAll_eq_batch {α : Type} (step : Step α) (init : α) (chunks : List String)
    (r : α) (h : (Reader.nquads .rdf11 { acc := init }).readAll step chunks = .ok r) :
    foldFrom .rdf11 step 0 (String.join chunks).toList init = .ok r := by
  rw [nquads_readAll_eq_run] at h
  rw [← flatten_toList_eq_join]
  exact LineFeed.run_quad11_eq_batch step init (chunks.map String.toList) r h

/-- **N-Quads, RDF 1.1, as a dataset.** With the consumer of `parseNQuadsFast`,
a chunked read that succeeds gives the dataset the batch parser gives for the
joined text. -/
theorem nquads11_readAll_eq_parseNQuadsFast (chunks : List String) (fd : FastDataset)
    (h : (Reader.nquads .rdf11 { acc := ({} : FastDataset) }).readAll addQuadFast chunks = .ok fd) :
    parseNQuadsFast (String.join chunks) .rdf11 = .ok fd.toDataset := by
  have hb := nquads11_readAll_eq_batch addQuadFast {} chunks fd h
  simp only [foldFrom] at hb
  simp only [parseNQuadsFast]
  rw [hb]
  rfl

/-! ## Turtle: the packer's accumulator -/

/-- **The Turtle reader's step with `collect` is the accumulator step of
`parseTurtle`** (`Syntax.parseTurtle_eq_fold`). The shard packer for IBK2 and
IBK3 folds statements with it and reverses once, so it commits the bytes a
`parseTurtle` run would commit, up to the chunk-boundary half that is measured
(`Source.lean`). -/
theorem turtleStep_collect : turtleStep collect = prependReverse := by
  funext acc ts
  simp only [turtleStep, collect, prependReverse]
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih => simp [List.foldl_cons, ih, List.reverse_cons]

/-! ## The pre-pass -/

/-- The underscore walk over decoded chunks is the walk over their join. -/
theorem underscores_chunks (chunks : List String) :
    ∀ p : UnderscoreRun, chunks.foldl (fun us c => us.feedChars c.toList) p =
      (String.join chunks).toList.foldl UnderscoreRun.feedChar p := by
  induction chunks with
  | nil => intro p; simp [String.join]
  | cons c rest ih =>
      intro p
      simp only [List.foldl_cons, String.join_cons, String.toList_append, List.foldl_append]
      rw [UnderscoreRun.feedChars_eq_foldl]
      exact ih _

/-- **The pre-pass.** The prefix computed from the decoded chunks, whatever the
cuts, is `freshBnodePrefix` of the joined text. `Prepass.feed` runs this walk
on each decoded chunk. -/
theorem prepass_chunks (chunks : List String) :
    freshBnodePrefixOfLongest
        (chunks.foldl (fun us c => us.feedChars c.toList) ({} : UnderscoreRun)).longest =
      freshBnodePrefix (String.join chunks) := by
  rw [underscores_chunks]
  simp only [freshBnodePrefix, maxUnderscoreRun, UnderscoreRun.feedChars_eq_foldl]

/-! ## Axiom audit -/

#print axioms whole_foldlM
#print axioms whole_readAll
#print axioms rdfxml_readAll_of_notStreamed
#print axioms jsonld_readAll
#print axioms jsonld_readAll_of_notStreamed
#print axioms nquads_foldlM
#print axioms nquads_readAll_eq_run
#print axioms flatten_toList_eq_join
#print axioms nquads11_readAll_eq_batch
#print axioms nquads11_readAll_eq_parseNQuadsFast
#print axioms turtleStep_collect
#print axioms underscores_chunks
#print axioms prepass_chunks

end L4Factoidal.RDF.Source
