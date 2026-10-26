/-
L4Factoidal.Syntax.LenientFeed — the byte-chunk driver of the streaming
lenient walks, for `l4factoidal parse --lenient FILE`
(https://github.com/danbri/factoidal/issues/716).

A host reads a file in byte chunks and calls `LenientFeed.feed` per chunk.
The feed decodes UTF-8 with `Utf8Stream` (a code point split across two
reads is carried, at most three bytes), hands the decoded text to the
streaming lenient walk of the syntax (`LenientStreamT` for N-Triples and
N-Quads, which keeps the partial line as text, `TurtleChunkLenientState` for Turtle), and returns the diagnostics
and the output lines that chunk produced. Nothing is kept from one chunk to
the next except the walk's own state (the line or candidate not yet complete,
the Turtle prefixes and base, the line state, the error count) and a count of
the triples kept, so a host that writes each chunk's results before reading
the next holds memory bounded by the chunk size plus the longest statement.

Turtle needs the document's generated blank-node prefix before the first
statement (`freshBnodePrefix`): `LenientPrepass` computes it in a first pass
over the same chunks, as the shard packer's pre-pass does.

TriG has no streaming execution (design record, section 3); the CLI reads a
TriG file whole and runs `parseTriGLenient`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.Utf8Stream
import L4Factoidal.Syntax.NQuadsLenient
import L4Factoidal.Syntax.LenientFeedText
import L4Factoidal.Syntax.TurtleLenient

namespace L4Factoidal.Syntax

open L4Factoidal.RDF
open L4Factoidal.Syntax.LenientFeedText

/-! ## The consumer the CLI uses -/

/-- A count of the triples kept and, when `emit` is set, the canonical
N-Quads lines of the current chunk, newest first. -/
structure FeedSink where
  count : Nat := 0
  emit : Bool := false
  linesRev : List String := []

def FeedSink.addQuad (k : FeedSink) (t : Triple) (g : Option Subject) : FeedSink :=
  { k with count := k.count + 1,
           linesRev :=
             if k.emit then
               (match g with
                | none => Triple.toCanonicalNTriples t
                | some n => canonNamedLine n t) :: k.linesRev
             else k.linesRev }

def FeedSink.addTriples (k : FeedSink) (ts : List Triple) : FeedSink :=
  ts.foldl (fun k t => k.addQuad t none) k

/-! ## The feed -/

/-- The streaming walk of one syntax. -/
inductive LenientFeedWalk where
  /-- N-Triples (`quads = false`) or N-Quads: the partial line is text
  (`LenientStreamT`, https://github.com/danbri/factoidal/issues/949). -/
  | lines (quads : Bool) (mode : Mode) (st : LenientStreamT FeedSink (List Diagnostic))
  | turtle (st : TurtleChunkLenientState FeedSink (List Diagnostic))

structure LenientFeed where
  utf8 : Utf8Stream := Utf8Stream.init
  walk : LenientFeedWalk
  opts : LenientOptions

/-- What one chunk produced: its diagnostics and its output lines, in source
order. -/
structure FeedOut where
  diags : List Diagnostic := []
  lines : List String := []

/-- An N-Triples (`ntriples := true`) or N-Quads feed. -/
def LenientFeed.initLines (mode : Mode) (ntriples : Bool) (emit : Bool) (opts : LenientOptions) :
    LenientFeed :=
  { walk := .lines (!ntriples) mode (LenientStreamT.init { emit } []),
    opts }

/-- A Turtle feed, given the document's generated blank-node prefix. -/
def LenientFeed.initTurtle (bnodePrefix : String) (base : Option String) (mode : Mode)
    (emit : Bool) (opts : LenientOptions) : LenientFeed :=
  { walk := .turtle (TurtleChunkLenientState.init bnodePrefix { emit } [] base mode), opts }

private def drainLines (st : LenientStreamT FeedSink (List Diagnostic)) :
    FeedOut × LenientStreamT FeedSink (List Diagnostic) :=
  ({ diags := st.run.diags.reverse, lines := st.run.acc.linesRev.reverse },
   { st with run := { st.run with diags := [], acc := { st.run.acc with linesRev := [] } } })

private def drainTurtle (st : TurtleChunkLenientState FeedSink (List Diagnostic)) :
    FeedOut × TurtleChunkLenientState FeedSink (List Diagnostic) :=
  ({ diags := st.run.diags.reverse, lines := st.run.acc.linesRev.reverse },
   { st with run := { st.run with diags := [], acc := { st.run.acc with linesRev := [] } } })

/-- Feed one byte chunk. `.error` only for bytes that are not UTF-8. -/
def LenientFeed.feed (f : LenientFeed) (bytes : ByteArray) : Except String (LenientFeed × FeedOut) :=
  match f.utf8.feed bytes with
  | .error e => .error e
  | .ok (text, utf8) =>
      match f.walk with
      | .lines quads mode st =>
          let (out, st') := drainLines (st.feed quads mode FeedSink.addQuad pushDiag f.opts text)
          .ok ({ f with utf8, walk := .lines quads mode st' }, out)
      | .turtle st =>
          let (out, st') := drainTurtle (st.feed FeedSink.addTriples pushDiag f.opts text)
          .ok ({ f with utf8, walk := .turtle st' }, out)

/-- End of input: the last partial statement, the total count kept, and
whether `maxErrors` stopped the walk. -/
def LenientFeed.finish (f : LenientFeed) : Except String (FeedOut × Nat × Bool) :=
  match f.utf8.finish with
  | .error e => .error e
  | .ok () =>
      match f.walk with
      | .lines quads mode st =>
          let run := st.finish quads mode FeedSink.addQuad pushDiag f.opts
          .ok ({ diags := run.diags.reverse, lines := run.acc.linesRev.reverse },
               run.acc.count, run.stopped)
      | .turtle st =>
          let run := st.finish FeedSink.addTriples pushDiag f.opts
          .ok ({ diags := run.diags.reverse, lines := run.acc.linesRev.reverse },
               run.acc.count, run.stopped)

/-- `true` once `maxErrors` has stopped the walk: the host may stop reading. -/
def LenientFeed.stopped (f : LenientFeed) : Bool :=
  match f.walk with
  | .lines _ _ st => st.run.stopped
  | .turtle st => st.run.stopped

/-! ## The Turtle pre-pass -/

/-- The longest run of `_` in the decoded document, over byte chunks. -/
structure LenientPrepass where
  utf8 : Utf8Stream := Utf8Stream.init
  run : UnderscoreRun := {}

def LenientPrepass.feed (p : LenientPrepass) (bytes : ByteArray) : Except String LenientPrepass :=
  match p.utf8.feed bytes with
  | .error e => .error e
  | .ok (text, utf8) => .ok { utf8, run := p.run.feedChars text.toList }

/-- The generated blank-node prefix, as `freshBnodePrefix` of the whole text. -/
def LenientPrepass.finish (p : LenientPrepass) : Except String String :=
  match p.utf8.finish with
  | .error e => .error e
  | .ok () => .ok (freshBnodePrefixOfLongest p.run.longest)

/-! ## Build-time checks: byte chunks agree with the reference walks -/

private def byteChunks (n : Nat) (b : ByteArray) : List ByteArray :=
  (List.range ((b.size + n - 1) / n)).map fun i => b.extract (i * n) (min b.size ((i + 1) * n))

/-- Feed `doc` in `n`-byte chunks; the diagnostics, lines and count. -/
private def feedAll (f : LenientFeed) (n : Nat) (doc : String) :
    Except String (List Diagnostic × List String × Nat) := do
  let (f, outs) ← (byteChunks n doc.toUTF8).foldlM
    (fun (acc : LenientFeed × List FeedOut) bytes => do
      let (f', out) ← acc.1.feed bytes
      pure (f', out :: acc.2)) (f, [])
  let (last, count, _) ← f.finish
  let all := (last :: outs).reverse
  pure ((all.map (·.diags)).flatten, (all.map (·.lines)).flatten, count)

private def nqDoc : String :=
  "<http://e/a> <http://e/p> \"café\" <http://e/g> .\n" ++
  "<http://e/a> <http://e/p> .\n" ++
  "_:b <http://e/p> \"éé\"@fr .\n"

-- Every chunk size from 1 byte (which splits the two-byte é) gives the
-- reference diagnostics, the reference count and one line per kept quad.
#guard (List.range 12).all fun i =>
  match feedAll (LenientFeed.initLines .rdf11 false true {}) (i + 1) nqDoc with
  | .ok (ds, lines, count) =>
      ds == (parseNQuadsLenient nqDoc).2 && count == 2 && lines.length == 2
  | .error _ => false

private def ttlDoc : String :=
  "@prefix ex: <http://example.org/> .\nex:a ex:p \"é\" .\nex:b ex:p .\nex:c ex:p [ ex:q ex:r ] .\n"

#guard (List.range 12).all fun i =>
  match feedAll (LenientFeed.initTurtle (freshBnodePrefix ttlDoc) none .rdf11 true {}) (i + 1) ttlDoc with
  | .ok (ds, lines, count) =>
      ds == (parseTurtleLenient ttlDoc).2 && count == 3 &&
      lines == ((parseTurtleLenient ttlDoc).1.map Triple.toCanonicalNTriples)
  | .error _ => false

-- The pre-pass gives `freshBnodePrefix` of the whole text at every chunk size.
#guard (List.range 6).all fun i =>
  match (byteChunks (i + 1) ttlDoc.toUTF8).foldlM LenientPrepass.feed {} with
  | .ok p => (match p.finish with
              | .ok s => s == freshBnodePrefix ttlDoc
              | .error _ => false)
  | .error _ => false

-- Bytes that are not UTF-8 are an error, not a silent substitution.
#guard (match (LenientFeed.initLines .rdf11 false false {}).feed (ByteArray.mk #[0x3c, 0xff, 0x3e]) with
        | .error _ => true
        | .ok _ => false)

end L4Factoidal.Syntax
