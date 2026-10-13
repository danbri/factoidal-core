/-
L4Factoidal.Syntax.StrictFeed — the byte-chunk driver of the STRICT parsers,
for `l4factoidal parse FILE [--out nquads]`
(https://github.com/danbri/factoidal/issues/813).

Before this module the strict `parse` read the whole file into one `String`,
turned it into a `List Char` (N-Triples, N-Quads; about 32 bytes of memory
per input character), built the whole dataset, and wrote the whole canonical
N-Quads text as one more `String`: 33 to 35 bytes of resident memory per
input byte. This module gives the command line the same answers from 64 KiB
byte chunks:

* N-Triples and N-Quads: `LineFeed`, the strict line walk `foldLines` (the
  five branches of `parseLinesAcc` and `foldQuadLinesAcc`, with the statement
  reader as a parameter) over the complete lines of each chunk
  (`splitCompleteLines`), carrying the partial last line and the absolute
  offset, so an error names its place in the document.
* Turtle: the scanner walk of `parseTurtleWalk` (`walkStep`, one character at
  a time), fed the decoded characters of each chunk in order, after a
  pre-pass (`TurtlePrepass`) that computes the generated blank-node prefix
  and `hasDoubleLt` of the whole document.

What is kept between chunks: the walk's own state (prefixes, base, the
unfinished line or statement candidate, the offset) and the consumer's state.
The command line's consumers are a list of the chunk's triples (written as
canonical N-Quads lines, then dropped) and, for the count and for N-Quads,
the indexed accumulator `FastDataset` (the set of distinct triples).

Theorems, in this file and in `TurtleChunkFold.lean`:

* `foldLines_quadReader`: `foldLines (quadReader mode)` IS
  `foldQuadLinesAcc mode`; `LineFeed.run_quad11_eq_batch` then states that a
  chunked N-Quads run that succeeds gives the whole-document fold's result,
  from `NQuadsFold.streamConsume11_eq_batch`.
* `parseLinesAcc_eq_foldLines`: the N-Triples reference `parseLinesAcc` is
  `foldLines (tripleReader mode)` with a list consumer.
* `turtleFeedChunks_eq`: feeding the decoded chunks of a text to `walkStep`
  is the walk of the whole text (`String.foldl` over a concatenation);
  `TurtleChunkFold.walk_drain` (in `TurtleChunkFold.lean`): a walk started
  with triples `a` already in its accumulator ends with the triples of the
  walk started empty, then `a`, so emptying the accumulator after each chunk
  loses and reorders nothing.
* `TurtlePrepass.finish_eq`: the pre-pass over chunks gives
  `freshBnodePrefixText` and `hasDoubleLt` of their concatenation.

Not proved: the N-Triples chunk boundary (`LineFeed` with `tripleReader`
against `parseLinesAcc` on the whole text) and the N-Quads RDF 1.2 one; the
N-Triples and N-Quads error text at a chunk boundary. The command line is
checked against the binary before this change on every file of the W3C
syntax suites (design record, section 3b).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.Utf8Stream
import L4Factoidal.Syntax.NQuadsLenient
import L4Factoidal.Syntax.TurtleChunkFold
import L4Factoidal.RDF.DatasetNormalize

namespace L4Factoidal.Syntax.StrictFeed

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## The strict line walk with the statement reader as a parameter -/

/-- `foldQuadLinesAcc` with the statement reader as a parameter: the same
five branches and the same fuel. With `quadReader mode` it is
`foldQuadLinesAcc mode` (`foldLines_quadReader`); with `tripleReader mode`
and a list consumer it is the N-Triples `parseLinesAcc`
(`parseLinesAcc_eq_foldLines`). -/
def foldLines (reader : LineReader) {α : Type} (consume : α → Triple → Option Subject → α) :
    Nat → Nat → List Char → α → Except ParseError α
  | 0, pos, _, _ =>
      .error ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
  | fuel' + 1, pos, cs, acc =>
      let (pos1, cs1) := skipWs pos cs
      match cs1 with
      | [] => .ok acc
      | '#' :: _ =>
          let (pos2, cs2) := skipComment pos1 cs1
          let (pos3, cs3) := skipEol pos2 cs2
          foldLines reader consume fuel' pos3 cs3 acc
      | '\n' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          foldLines reader consume fuel' pos2 cs2 acc
      | '\r' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          foldLines reader consume fuel' pos2 cs2 acc
      | _ =>
          match reader pos1 cs1 with
          | .error e => .error e
          | .ok (t, gopt, pos2, cs2) =>
              let acc' := consume acc t gopt
              let (pos3, cs3) := skipWs pos2 cs2
              let (pos4, cs4) := skipComment pos3 cs3
              let (pos5, cs5) := skipEol pos4 cs4
              foldLines reader consume fuel' pos5 cs5 acc'

theorem foldLines_quadReader (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) :
    ∀ (fuel pos : Nat) (cs : List Char) (acc : α),
      foldLines (quadReader mode) consume fuel pos cs acc =
        foldQuadLinesAcc mode consume fuel pos cs acc := by
  intro fuel
  induction fuel with
  | zero => intro pos cs acc; rfl
  | succ n ih =>
      intro pos cs acc
      simp only [foldLines, foldQuadLinesAcc, quadReader, ih]
      rfl

/-- The N-Triples reference walk is `foldLines` with a list consumer. -/
theorem parseLinesAcc_eq_foldLines (mode : Mode) :
    ∀ (fuel pos : Nat) (cs : List Char) (acc : List Triple),
      parseLinesAcc mode fuel pos cs acc =
        (foldLines (tripleReader mode) (fun a t _ => t :: a) fuel pos cs acc).map List.reverse := by
  intro fuel
  induction fuel with
  | zero => intro pos cs acc; rfl
  | succ n ih =>
      intro pos cs acc
      simp only [foldLines, parseLinesAcc, tripleReader, ih]
      generalize (skipWs pos cs).fst = pos1
      generalize (skipWs pos cs).snd = cs1
      split
      · rfl
      · rfl
      · rfl
      · rfl
      · rename_i x h1 h2 h3 h4
        symm
        split
        · exfalso; simp_all
        · exfalso; simp_all
        · exfalso; simp_all
        · exfalso; simp_all
        · symm
          cases mode
          · rcases readTriple11 pos1 cs1 with e | ⟨t, p, r⟩ <;> rfl
          · rcases readTriple12 pos1 cs1 with e | ⟨t, p, r⟩ <;> rfl

/-- `parseNTriples` through `foldLines`. -/
theorem parseNTriples_eq_foldLines (s : String) (mode : Mode) :
    parseNTriples s mode =
      (foldLines (tripleReader mode) (fun a t _ => t :: a) (s.toList.length + 1) 0 s.toList
        []).map List.reverse := by
  simp only [parseNTriples, parseLinesAcc_eq_foldLines]

/-! ## Chunked line walk -/

/-- What the chunked line walk keeps between chunks: the consumer's state,
the partial last line, and the absolute offset (in characters) of the
first character of `carry`. -/
structure LineFeed (α : Type) where
  acc : α
  carry : List Char := []
  pos : Nat := 0

/-- Feed one decoded chunk: walk the complete lines of `carry ++ chunk`,
keep the rest.

The state is taken apart before the walk, so the consumer's state is the only
reference to itself when the walk updates it. Reading `st.pos` after the walk
kept `st`, and through it the accumulator, alive: `addQuadFast` then copied
the whole hash map of a `FastDataset` at the first quad of every chunk, and
the count of 400,000 N-Triples took 9.16 s of CPU where 100,000 took 0.97 s
(2026-10-13, https://github.com/danbri/factoidal/issues/813). -/
def LineFeed.feed (reader : LineReader) {α : Type} (consume : α → Triple → Option Subject → α)
    (st : LineFeed α) (chunk : List Char) : Except ParseError (LineFeed α) :=
  match st with
  | { acc, carry, pos } =>
    let (complete, carry') := splitCompleteLines (carry ++ chunk)
    match foldLines reader consume (complete.length + 1) pos complete acc with
    | .ok acc' => .ok { acc := acc', carry := carry', pos := pos + complete.length }
    | .error e => .error e

/-- End of input: walk the partial last line. -/
def LineFeed.finish (reader : LineReader) {α : Type} (consume : α → Triple → Option Subject → α)
    (st : LineFeed α) : Except ParseError α :=
  foldLines reader consume (st.carry.length + 1) st.pos st.carry st.acc

/-- A whole chunked run, for the theorems and the guards. -/
def LineFeed.run (reader : LineReader) {α : Type} (consume : α → Triple → Option Subject → α)
    (init : α) (chunks : List (List Char)) : Except ParseError α :=
  match chunks.foldlM (LineFeed.feed reader consume) { acc := init } with
  | .error e => .error e
  | .ok st => LineFeed.finish reader consume st

/-- One chunk of `LineFeed` with the N-Quads RDF 1.1 reader is one chunk of
`feedChunkC`, on a state with no error. -/
theorem LineFeed.feed_quad11 {α : Type} (consume : α → Triple → Option Subject → α)
    (st : LineFeed α) (chunk : List Char) :
    feedChunkC .rdf11 consume { acc := st.acc, carry := st.carry, pos := st.pos, err := none }
        chunk =
      match LineFeed.feed (quadReader .rdf11) consume st chunk with
      | .ok st' => { acc := st'.acc, carry := st'.carry, pos := st'.pos, err := none }
      | .error e => { acc := st.acc, carry := (splitCompleteLines (st.carry ++ chunk)).2,
                      pos := st.pos + (splitCompleteLines (st.carry ++ chunk)).1.length,
                      err := some e } := by
  cases st with
  | mk acc carry pos =>
    simp only [feedChunkC, LineFeed.feed, foldFrom, foldLines_quadReader]
    cases foldQuadLinesAcc .rdf11 consume _ pos _ acc <;> rfl

private theorem foldlM_quad11 {α : Type} (consume : α → Triple → Option Subject → α) :
    ∀ (chunks : List (List Char)) (st st' : LineFeed α),
      chunks.foldlM (LineFeed.feed (quadReader .rdf11) consume) st = .ok st' →
      chunks.foldl (feedChunkC .rdf11 consume)
          { acc := st.acc, carry := st.carry, pos := st.pos, err := none } =
        { acc := st'.acc, carry := st'.carry, pos := st'.pos, err := none }
  | [], st, st', h => by
      simp only [List.foldlM_nil, pure, Except.pure] at h
      cases h
      rfl
  | c :: rest, st, st', h => by
      simp only [List.foldlM_cons, bind, Except.bind] at h
      simp only [List.foldl_cons]
      rw [LineFeed.feed_quad11]
      cases hf : LineFeed.feed (quadReader .rdf11) consume st c with
      | error e => rw [hf] at h; cases h
      | ok s1 =>
          rw [hf] at h
          exact foldlM_quad11 consume rest s1 st' h

/-- A chunked N-Quads (RDF 1.1) run that succeeds gives what the fold of the
whole document gives: `NQuadsFold.streamConsume11_eq_batch` through
`LineFeed.feed_quad11`. -/
theorem LineFeed.run_quad11_eq_batch {α : Type} (consume : α → Triple → Option Subject → α)
    (init : α) (chunks : List (List Char)) (r : α)
    (h : LineFeed.run (quadReader .rdf11) consume init chunks = .ok r) :
    foldFrom .rdf11 consume 0 chunks.flatten init = .ok r := by
  apply streamConsume11_eq_batch consume init chunks r
  simp only [LineFeed.run] at h
  cases hf : chunks.foldlM (LineFeed.feed (quadReader .rdf11) consume) { acc := init } with
  | error e => rw [hf] at h; cases h
  | ok st =>
      rw [hf] at h
      have hc := foldlM_quad11 consume chunks { acc := init } st hf
      simp only [streamConsume, initialStateC]
      rw [show ({ acc := init, carry := [], pos := 0, err := none } : StreamStateC α) =
            { acc := ({ acc := init } : LineFeed α).acc, carry := ({ acc := init } : LineFeed α).carry,
              pos := ({ acc := init } : LineFeed α).pos, err := none } from rfl, hc]
      simp only [finishC, foldFrom, ← foldLines_quadReader]
      exact h

/-! ## Turtle -/

/-- One character of the walk of `parseTurtleWalk`. -/
def walkStep {α : Type} (step : α → List Triple → α)
    (r : Except ParseError (TurtleChunkFoldState α)) (c : Char) :
    Except ParseError (TurtleChunkFoldState α) :=
  match r with
  | .error e => .error e
  | .ok state => state.feedChar step c

/-- Feed the characters of one decoded chunk to the walk. -/
def turtleFeed {α : Type} (step : α → List Triple → α)
    (r : Except ParseError (TurtleChunkFoldState α)) (chunk : String) :
    Except ParseError (TurtleChunkFoldState α) :=
  chunk.foldl (walkStep step) r

/-- Feeding chunks one after the other is feeding their concatenation. -/
theorem turtleFeedChunks_eq {α : Type} (step : α → List Triple → α) :
    ∀ (chunks : List String) (r : Except ParseError (TurtleChunkFoldState α)),
      chunks.foldl (turtleFeed step) r = (String.join chunks).foldl (walkStep step) r
  | [], r => by simp [String.foldl_eq_foldl_toList]
  | c :: rest, r => by
      rw [List.foldl_cons, turtleFeedChunks_eq step rest]
      simp only [turtleFeed, String.join_cons, String.foldl_eq_foldl_toList,
        String.toList_append, List.foldl_append]

/-- `TurtleChunkFold.walkChars` (the walk of `parseTurtleWalk`) is the fold of
`walkStep`. -/
theorem walkChars_eq_foldl {α : Type} (step : α → List Triple → α) :
    ∀ (cs : List Char) (r : Except ParseError (TurtleChunkFoldState α)),
      walkChars step cs r = cs.foldl (walkStep step) r
  | [], _ => rfl
  | c :: cs, r => by
      have h1 : walkChars step (c :: cs) r = walkChars step cs (walkStep step r c) := by
        cases r <;> rfl
      rw [h1, walkChars_eq_foldl step cs]
      rfl

/-- One decoded chunk through `turtleFeed` is `walkChars` over its characters. -/
theorem turtleFeed_eq_walkChars {α : Type} (step : α → List Triple → α)
    (r : Except ParseError (TurtleChunkFoldState α)) (chunk : String) :
    turtleFeed step r chunk = walkChars step chunk.toList r := by
  rw [walkChars_eq_foldl, turtleFeed, String.foldl_eq_foldl_toList]

/-- The walk over the characters `cs` from `s`, finished, with its triples in
document order: what `parseTurtleWalk` computes from its initial state. -/
def walkAll (s : TurtleChunkFoldState (List Triple)) (cs : List Char) :
    Except ParseError (List Triple) :=
  match walkChars prependReverse cs (.ok s) with
  | .error e => .error e
  | .ok st => (st.finish prependReverse).map List.reverse

/-- The chunked walk as the command line runs it (`streamStrictTurtle` in
`Wasm/Cli.lean`): after each chunk the triples in the accumulator are
written and the accumulator is emptied. The result lists the triples
written, in order. -/
def drainRun (s : TurtleChunkFoldState (List Triple)) : List String → Except ParseError (List Triple)
  | [] => (s.finish prependReverse).map List.reverse
  | c :: rest =>
      match turtleFeed prependReverse (.ok s) c with
      | .error e => .error e
      | .ok s' => (drainRun (s'.mapAcc (fun _ => [])) rest).map (s'.acc.reverse ++ ·)

theorem walkChars_error {α : Type} (step : α → List Triple → α) (e : ParseError) :
    ∀ cs : List Char, walkChars step cs (.error e) = .error e
  | [] => rfl
  | _ :: cs => walkChars_error step e cs

theorem walkChars_append {α : Type} (step : α → List Triple → α) (xs ys : List Char)
    (r : Except ParseError (TurtleChunkFoldState α)) :
    walkChars step (xs ++ ys) r = walkChars step ys (walkChars step xs r) := by
  simp only [walkChars, List.foldl_append]

/-- A walk from a state whose accumulator holds `a` writes the triples of the
walk from the emptied state after the triples of `a`. -/
theorem walkAll_drain (s : TurtleChunkFoldState (List Triple)) (a : List Triple)
    (cs : List Char) :
    walkAll (s.mapAcc (· ++ a)) cs = (walkAll s cs).map (a.reverse ++ ·) := by
  unfold walkAll
  rw [walk_drain]
  cases walkChars prependReverse cs (.ok s) with
  | error e => rfl
  | ok st =>
      simp only [Except.map]
      rw [finish_drain]
      cases st.finish prependReverse with
      | error e => rfl
      | ok x => simp [Except.map, List.reverse_append]

/-- Emptying the accumulator after every chunk and writing what it held writes
exactly the triples of the walk of the concatenated chunks, in order, and
fails exactly when that walk fails, with the same error. -/
theorem drainRun_eq (chunks : List String) :
    ∀ (s : TurtleChunkFoldState (List Triple)), s.acc = [] →
      drainRun s chunks = walkAll s (String.join chunks).toList := by
  induction chunks with
  | nil =>
      intro s _
      simp [drainRun, walkAll, walkChars]
  | cons c rest ih =>
      intro s hs
      simp only [drainRun, String.join_cons, String.toList_append]
      rw [turtleFeed_eq_walkChars]
      unfold walkAll
      rw [walkChars_append]
      cases h : walkChars prependReverse c.toList (.ok s) with
      | error e => simp [walkChars_error]
      | ok s' =>
          simp only
          rw [ih (s'.mapAcc (fun _ => [])) rfl]
          have hs' : s' = (s'.mapAcc (fun _ => [])).mapAcc (· ++ s'.acc) := by
            cases s'; simp
          conv => rhs; rw [hs']
          rw [← walkAll_drain]
          rfl

/-- The character step of `hasDoubleLt`. -/
def doubleLtStep (st : Nat) (c : Char) : Nat :=
  if st == 2 then 2 else if c == '<' then (if st == 1 then 2 else 1) else 0

theorem hasDoubleLt_eq (text : String) : hasDoubleLt text = (text.foldl doubleLtStep 0 == 2) := rfl

/-- The Turtle pre-pass over byte chunks: the longest run of `_` (for the
generated blank-node prefix) and the `<<` state. -/
structure TurtlePrepass where
  utf8 : Utf8Stream := Utf8Stream.init
  run : UnderscoreRun := {}
  lt : Nat := 0

/-- The pre-pass over one decoded chunk. -/
def TurtlePrepass.feedText (p : TurtlePrepass) (text : String) : TurtlePrepass :=
  { p with run := text.foldl UnderscoreRun.feedChar p.run, lt := text.foldl doubleLtStep p.lt }

def TurtlePrepass.feed (p : TurtlePrepass) (bytes : ByteArray) : Except String TurtlePrepass :=
  match p.utf8.feed bytes with
  | .error e => .error e
  | .ok (text, utf8) => .ok { (p.feedText text) with utf8 }

/-- The generated blank-node prefix and whether the document contains `<<`. -/
def TurtlePrepass.finish (p : TurtlePrepass) : Except String (String × Bool) :=
  match p.utf8.finish with
  | .error e => .error e
  | .ok () => .ok (freshBnodePrefixOfLongest p.run.longest, p.lt == 2)

/-- Over decoded chunks, the pre-pass computes the two whole-text values. -/
theorem TurtlePrepass.feedText_chunks (chunks : List String) :
    let p := chunks.foldl TurtlePrepass.feedText {}
    freshBnodePrefixOfLongest p.run.longest = freshBnodePrefixText (String.join chunks) ∧
      (p.lt == 2) = hasDoubleLt (String.join chunks) := by
  have key : ∀ (cs : List String) (p : TurtlePrepass),
      (cs.foldl TurtlePrepass.feedText p).run = (String.join cs).foldl UnderscoreRun.feedChar p.run ∧
      (cs.foldl TurtlePrepass.feedText p).lt = (String.join cs).foldl doubleLtStep p.lt := by
    intro cs
    induction cs with
    | nil => intro p; simp [String.foldl_eq_foldl_toList]
    | cons c rest ih =>
        intro p
        rw [List.foldl_cons]
        obtain ⟨h1, h2⟩ := ih (p.feedText c)
        rw [h1, h2]
        simp only [TurtlePrepass.feedText, String.join_cons, String.foldl_eq_foldl_toList,
          String.toList_append, List.foldl_append, and_self]
  obtain ⟨h1, h2⟩ := key chunks {}
  refine ⟨?_, ?_⟩
  · simp only [freshBnodePrefixText]
    rw [h1]
  · rw [hasDoubleLt_eq, h2]

/-! ## Consumers -/

/-- The count consumer: RDF 1.1 Concepts §3 (a graph is a set) and §3.3
(language tags in lower case), the step of `normalizeDataset`. -/
def countQuad (ds : FastDataset) (t : Triple) (g : Option Subject) : FastDataset :=
  addQuadFast ds t.lowerTags g

/-- The number of quads of an accumulated set, as `parse` prints it. -/
def FastDataset.quadCount (ds : FastDataset) : Nat :=
  let d := ds.toDataset
  d.default.length + (d.named.map (·.graph.length)).foldl (· + ·) 0

/-- `normalizeDataset` of a dataset with one default graph `g` is the count
consumer folded over `g`. -/
theorem normalizeDataset_default (g : Graph) :
    normalizeDataset { default := g, named := [] } =
      (g.foldl (fun ds t => countQuad ds t none) {}).toDataset := by
  simp [normalizeDataset, Dataset.quadList, List.foldl_map, countQuad]

/-- The canonical N-Quads lines of a chunk's triples (newest first in
`accRev`), in document order. -/
def linesOfRev (accRev : List Triple) : List String :=
  accRev.reverse.map Triple.toCanonicalNTriples

theorem toCanonicalNQuads_default (g : Graph) :
    Dataset.toCanonicalNQuads { default := g, named := [] } =
      String.join (g.map Triple.toCanonicalNTriples) := by
  simp [Dataset.toCanonicalNQuads, Graph.toCanonicalNTriples]


/-- The canonical N-Quads text of a chunk's triples (newest first in
`accRev`), built by appending to one string. -/
def chunkText (accRev : List Triple) : String :=
  accRev.reverse.foldl (fun s t => s ++ Triple.toCanonicalNTriples t) ""

theorem chunkText_eq (accRev : List Triple) :
    chunkText accRev = String.join (linesOfRev accRev) := by
  simp [chunkText, linesOfRev, String.join, List.foldr_map]

/-- Add a chunk's triples (newest first in `accRev`) to the count set, in
document order. -/
def countTriplesRev (fd : FastDataset) (accRev : List Triple) : FastDataset :=
  accRev.reverse.foldl (fun ds t => countQuad ds t none) fd

/-- The triples a walk from `s` read before it failed (all of them when it
did not fail), in document order. The command line compares them with the
reference graph when the walk refused a document `parseTurtle` accepts. -/
def walkPrefix (s : TurtleChunkFoldState (List Triple)) (text : String) : List Triple :=
  (text.foldl (fun (p : Option (TurtleChunkFoldState (List Triple)) × List Triple) c =>
     match p.1 with
     | none => p
     | some st =>
       match st.feedChar prependReverse c with
       | .ok st' => (some st', st'.acc)
       | .error _ => (none, p.2)) (some s, s.acc)).2.reverse

/-! ## Build-time checks -/

private def chunksOf (n : Nat) (cs : List Char) : List (List Char) :=
  (List.range ((cs.length + n - 1) / n)).map fun i => (cs.drop (i * n)).take n

private def ntDoc : String :=
  "<http://e/a> <http://e/p> \"café\" .\n# c\n\r\n<http://e/a> <http://e/p> <http://e/b> . # x\n" ++
  "_:b <http://e/p> \"x\"@EN .\n_:b <http://e/p> \"x\"@en ."

private def ntBad : String :=
  "<http://e/a> <http://e/p> <http://e/b> .\n<http://e/a> <http://e/p> .\n"

-- N-Triples: every chunk size gives the reference graph and the reference error.
#guard (List.range 14).all fun i =>
  ((LineFeed.run (tripleReader .rdf11) (fun a t _ => t :: a) [] (chunksOf (i + 1) ntDoc.toList)).map
      List.reverse).toOption == (parseNTriples ntDoc).toOption
#guard (parseNTriples ntDoc).toOption.map List.length == some 4
#guard (List.range 14).all fun i =>
  match LineFeed.run (tripleReader .rdf11) (fun a t _ => t :: a) [] (chunksOf (i + 1) ntBad.toList),
        parseNTriples ntBad with
  | .error e1, .error e2 => e1.msg == e2.msg && e1.pos == e2.pos
  | _, _ => false
#guard (parseNTriples ntBad).toOption.isNone

-- The count consumer counts the normalised set: 3 distinct triples of 4.
#guard ((LineFeed.run (tripleReader .rdf11) (fun ds t g => countQuad ds t g) {}
    (chunksOf 7 ntDoc.toList)).toOption.map FastDataset.quadCount) == some 3

private def ttlDoc : String :=
  "@prefix ex: <http://example.org/> .\nex:a ex:p \"é\", ex:b ;\n ex:q [ ex:r ( 1 2 ) ] .\n" ++
  "PREFIX f: <http://f/>\nf:x f:y f:z .\nex:a ex:p \"é\" ."

private def ttlChunks (n : Nat) (s : String) : List String :=
  (chunksOf n s.toList).map String.ofList

/-- The chunked walk with an accumulator emptied after every chunk, its
triples in document order. -/
private def drainedWalk (n : Nat) (s : String) : Except ParseError (List Triple) :=
  let init : TurtleChunkFoldState (List Triple) :=
    TurtleChunkFoldState.init (freshBnodePrefixText s) prependReverse [] none .rdf11
  let r := (ttlChunks n s).foldlM (m := Except ParseError)
      (fun (p : TurtleChunkFoldState (List Triple) × List Triple) c =>
        match turtleFeed prependReverse (.ok p.1) c with
        | .error e => .error e
        | .ok st => .ok ({ st with acc := [] }, p.2 ++ st.acc.reverse)) (init, [])
  match r with
  | .error e => .error e
  | .ok (st, out) =>
    match st.finish prependReverse with
    | .ok accRev => .ok (out ++ accRev.reverse)
    | .error e => .error e

#guard (List.range 12).all fun i => (drainedWalk (i + 1) ttlDoc).toOption == (parseTurtle ttlDoc).toOption
#guard (parseTurtle ttlDoc).toOption.map List.length == some 10

end L4Factoidal.Syntax.StrictFeed
