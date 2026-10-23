/-
L4Factoidal.RDF.StreamSet — the streamed canonical N-Quads output of
`l4factoidal parse FILE --out nquads`, as a SET of triples.

RDF 1.1 Concepts and Abstract Syntax, section 3: "An RDF graph is a set of RDF
triples." The streamed reader (`Source.ByteReader`) hands each triple to a
consumer as soon as its statement is complete, and the command line wrote it
at once, so a document that states a triple two times wrote it two times,
while the count (`StrictFeed.countQuad`) and the whole-file output
(`Source.parseDocument`, which ends in `Dataset.toSet`) gave one.

`dedupStep` is the consumer that fixes this. It keeps the triples written so
far in a `FastGraph` (the hash-indexed accumulator of `parseNQuadsFast`) and
adds a triple to the list of the current chunk only when no triple already
there is `Triple.eqb`-equal to it (the language tags compare without case, as
in `Triple.eqb`). After a chunk the command line writes `fresh` and empties
it (`DedupAcc.drain`); the `FastGraph` stays.

Memory: the `FastGraph` holds every distinct triple written so far, so the
resident set grows with the number of distinct triples (one list cell and
one bucket entry for each), where the former consumer held one chunk. The
count path (`FastDataset`) already held the same. The measured resident
memory on QUDT is in the commit message of the change that added this module.

What is proved:

* `dedup_foldl`: the fold of `dedupStep` over triples is the fold of
  `Graph.add`: the seen graph is `graphAddAll` of the triples, and the
  triples written so far are a prefix of it.
* `runChunks_written`: over any cut of the triples into chunks, with `fresh`
  taken and emptied after each chunk, the triples written, in order, are
  `graphAddAll [] (chunks.flatten)`.
* `runChunks_eq_toSet`: they are the default graph of `Dataset.toSet` of the
  graph of all the triples, so the streamed output has the quads and the order
  of the whole-file output.
* `runChunks_keyNodup`: the written triples are a set (`Graph.KeyNodup`: no two
  have the same `Triple.key`, so no two are `Triple.eqb`-equal).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Source
import L4Factoidal.RDF.DatasetSet
import L4Factoidal.RDF.FastGraph
import L4Factoidal.Syntax.StrictFeed

namespace L4Factoidal.RDF

open L4Factoidal.Syntax
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## The seen graph -/

/-- Some triple of the graph is `Triple.eqb`-equal to `t`: the bucket scan of
`FastGraph.add`. -/
def FastGraph.contains (g : FastGraph) (t : Triple) : Bool :=
  (g.buckets.getD (tripleKey t) []).any (fun u => u.eqb t)

theorem FastGraph.contains_eq_mem {g : FastGraph} (t : Triple) (h : g.Inv) :
    g.contains t = Graph.mem t g.toGraph := by
  rw [FastGraph.contains, FastGraph.bucket_any t h, graphMem_eq_any]
  simp [FastGraph.toGraph, List.any_reverse]

theorem FastGraph.push_toGraph (t : Triple) (g : FastGraph) :
    (g.push t).toGraph = g.toGraph ++ [t] := by
  simp [FastGraph.push, FastGraph.toGraph]

/-! ## The consumer -/

/-- The seen triples, and the triples that are new since the last `drain`,
newest first. -/
structure DedupAcc where
  seen : FastGraph := {}
  fresh : List Triple := []

/-- Keep a triple when no `Triple.eqb`-equal triple was seen. The graph label
of a quad is not used (N-Triples and Turtle have none). -/
def dedupStep (st : DedupAcc) (t : Triple) (_ : Option Subject) : DedupAcc :=
  if st.seen.contains t then st
  else { seen := st.seen.push t, fresh := t :: st.fresh }

/-- Take the new triples out of the accumulator, keeping the seen graph. -/
def DedupAcc.drain (st : DedupAcc) : DedupAcc × List Triple :=
  ({ st with fresh := [] }, st.fresh)

/-! ## The set of triples written -/

/-- The seen graph is the triples `written` before, then the triples of
`fresh`, and its index is consistent. -/
def DedupAcc.Ok (st : DedupAcc) (written : Graph) : Prop :=
  st.seen.Inv ∧ st.seen.toGraph = written ++ st.fresh.reverse

/-- One step keeps the invariant and adds the triple to the seen graph as
`Graph.add` does. -/
theorem dedupStep_ok {st : DedupAcc} {B : Graph} (h : st.Ok B) (t : Triple) (g : Option Subject) :
    (dedupStep st t g).Ok B ∧
      (dedupStep st t g).seen.toGraph = Graph.add t st.seen.toGraph := by
  obtain ⟨hinv, hgraph⟩ := h
  unfold dedupStep
  by_cases hc : st.seen.contains t = true
  · rw [if_pos hc]
    have hm : Graph.mem t st.seen.toGraph = true := by
      rw [← FastGraph.contains_eq_mem t hinv]; exact hc
    refine ⟨⟨hinv, hgraph⟩, ?_⟩
    simp [Graph.add, hm]
  · rw [if_neg hc]
    have hm : Graph.mem t st.seen.toGraph = false := by
      rw [← FastGraph.contains_eq_mem t hinv]; simpa using hc
    refine ⟨⟨FastGraph.push_inv hinv, ?_⟩, ?_⟩
    · simp only [FastGraph.push_toGraph, hgraph, List.reverse_cons, List.append_assoc]
    · simp [Graph.add, hm, FastGraph.push_toGraph]

/-- The fold of `dedupStep` over triples is the fold of `Graph.add`. -/
theorem dedup_foldl (ts : List Triple) :
    ∀ (st : DedupAcc) (B : Graph), st.Ok B →
      (ts.foldl (fun s t => dedupStep s t none) st).Ok B ∧
      (ts.foldl (fun s t => dedupStep s t none) st).seen.toGraph =
        graphAddAll st.seen.toGraph ts := by
  induction ts with
  | nil => intro st B h; exact ⟨h, rfl⟩
  | cons t ts ih =>
    intro st B h
    obtain ⟨h1, h2⟩ := dedupStep_ok h t none
    obtain ⟨h3, h4⟩ := ih (dedupStep st t none) B h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2]
    rfl

theorem graphAddAll_append : ∀ (ts us : List Triple) (g : Graph),
    graphAddAll g (ts ++ us) = graphAddAll (graphAddAll g ts) us
  | [], _, _ => rfl
  | t :: ts, us, g => graphAddAll_append ts us (g.add t)

theorem graphAddAll_keyNodup : ∀ (ts : List Triple) (g : Graph),
    g.KeyNodup → (graphAddAll g ts).KeyNodup
  | [], _, h => h
  | t :: ts, g, h => graphAddAll_keyNodup ts (g.add t) (h.add t)

/-! ## Chunks -/

/-- One chunk of the command line's loop: add its triples, write `fresh`, empty
it. The pair is the accumulator and the triples written so far, in order. -/
def chunkStep (p : DedupAcc × Graph) (c : List Triple) : DedupAcc × Graph :=
  let st := c.foldl (fun s t => dedupStep s t none) p.1
  ({ st with fresh := [] }, p.2 ++ st.fresh.reverse)

/-- The loop over the chunks of triples the reader delivers. -/
def runChunks (chunks : List (List Triple)) : DedupAcc × Graph :=
  chunks.foldl chunkStep ({}, [])

theorem chunkStep_spec (p : DedupAcc × Graph) (c : List Triple) (h : p.1.Ok p.2)
    (hf : p.1.fresh = []) :
    (chunkStep p c).1.Ok (chunkStep p c).2 ∧ (chunkStep p c).1.fresh = [] ∧
      (chunkStep p c).2 = graphAddAll p.2 c := by
  obtain ⟨hok, hseen⟩ := dedup_foldl c p.1 p.2 h
  have hG : p.1.seen.toGraph = p.2 := by rw [h.2, hf]; simp
  unfold chunkStep
  generalize c.foldl (fun s t => dedupStep s t none) p.1 = st at hok hseen ⊢
  have hnew : st.seen.toGraph = p.2 ++ st.fresh.reverse := hok.2
  refine ⟨⟨hok.1, by simpa using hnew⟩, rfl, ?_⟩
  show p.2 ++ st.fresh.reverse = graphAddAll p.2 c
  rw [← hnew, hseen, hG]

theorem runChunks_aux : ∀ (chunks : List (List Triple)) (p : DedupAcc × Graph),
    p.1.Ok p.2 → p.1.fresh = [] →
    (chunks.foldl chunkStep p).1.Ok (chunks.foldl chunkStep p).2 ∧
      (chunks.foldl chunkStep p).1.fresh = [] ∧
      (chunks.foldl chunkStep p).2 = graphAddAll p.2 chunks.flatten := by
  intro chunks
  induction chunks with
  | nil => intro p h hf; exact ⟨h, hf, rfl⟩
  | cons c rest ih =>
    intro p h hf
    obtain ⟨s1, s2, s3⟩ := chunkStep_spec p c h hf
    obtain ⟨r1, r2, r3⟩ := ih (chunkStep p c) s1 s2
    refine ⟨r1, r2, ?_⟩
    rw [List.foldl_cons, r3, s3, List.flatten_cons, graphAddAll_append]

theorem runChunks_written (chunks : List (List Triple)) :
    (runChunks chunks).2 = graphAddAll [] chunks.flatten :=
  (runChunks_aux chunks ({}, []) ⟨FastGraph.inv_empty, rfl⟩ rfl).2.2

/-- The triples the streamed loop writes are a set. -/
theorem runChunks_keyNodup (chunks : List (List Triple)) : (runChunks chunks).2.KeyNodup := by
  rw [runChunks_written]
  exact graphAddAll_keyNodup _ _ Graph.keyNodup_nil

/-- The default graph of `Dataset.toSet` of a graph without named graphs. -/
theorem toSet_default (l : Graph) :
    (Dataset.toSet { default := l, named := [] }).default = graphAddAll [] l := by
  have key : ∀ (l : Graph) (d : Dataset),
      ((l.map (fun t => SetEvent.quad t none)).foldl SetEvent.apply d).default =
        graphAddAll d.default l := by
    intro l
    induction l with
    | nil => intro d; rfl
    | cons t ts ih => intro d; exact ih (addQuad d t none)
  unfold Dataset.toSet Dataset.events
  have h := key l Dataset.empty
  simp only [List.flatMap_nil, List.append_nil]
  exact h

/-- The triples the streamed loop writes are the default graph of the whole-file
parse of the graph of all the triples: same triples, same order. -/
theorem runChunks_eq_toSet (chunks : List (List Triple)) :
    (runChunks chunks).2 = (Dataset.toSet { default := chunks.flatten, named := [] }).default := by
  rw [runChunks_written, toSet_default]

#print axioms dedup_foldl
#print axioms runChunks_written
#print axioms runChunks_keyNodup
#print axioms runChunks_eq_toSet

/-! ## The streamed text, without a file

`streamedNQuads` is the loop of `l4factoidal parse FILE --out nquads` for
N-Triples and Turtle with the file replaced by its bytes in pieces of `chunk`
bytes: feed a chunk, write the new triples, empty `fresh`. The command line
(`Wasm/Cli.lean`) runs the same `dedupStep` and `DedupAcc.drain`. -/

/-- The bytes in pieces of `n` bytes (the last may be shorter). -/
def chunksOfBytes (n : Nat) (b : ByteArray) : List ByteArray :=
  (List.range ((b.size + n - 1) / n)).map fun i => b.extract (i * n) (i * n + n)

/-- The canonical N-Quads lines the streamed reader writes for `text` in pieces
of `chunk` bytes. -/
def streamedNQuads (fmt : RdfFormat) (mode : Mode) (bnodePrefix : String) (chunk : Nat)
    (text : String) : Except String String := do
  let rd0 ← Source.ByteReader.init {} fmt mode none bnodePrefix ({} : DedupAcc)
  let mut rd := rd0
  let mut out := ""
  for b in chunksOfBytes chunk text.toUTF8 do
    match rd.feed dedupStep b with
    | .error f => throw f.message
    | .ok rd' =>
      let (rd'', fresh) := rd'.withAcc DedupAcc.drain
      rd := rd''
      out := out ++ StrictFeed.chunkText fresh
  match rd.endBytes with
  | .error f => throw f.message
  | .ok reader =>
    match reader.finish dedupStep with
    | .error e => throw e.msg
    | .ok st => return out ++ StrictFeed.chunkText st.fresh

end L4Factoidal.RDF
