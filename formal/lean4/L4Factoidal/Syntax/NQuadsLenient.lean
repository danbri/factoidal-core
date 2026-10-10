/-
L4Factoidal.Syntax.NQuadsLenient — lenient (recovery) mode for N-Triples and
N-Quads, reference and streaming (https://github.com/danbri/factoidal/issues/716).

The strict parsers (`parseNTriples`, `parseNQuads`, `parseNQuadsFast`, the
generic fold `NQuadsStreaming.foldQuadLinesAcc` and its chunked consumer
`feedChunkC`) are unchanged. The lenient walk below is a separate function
with the same five branches as `foldQuadLinesAcc`; it differs only in the
statement branch's error arm:

  * the error becomes a `Diagnostic` (class, message, offset, line, column)
    handed to the caller's `report`;
  * the walk skips to the end of the LINE on which the failing statement
    started (`skipToEol`, then `skipEol`) and continues. RDF 1.1 N-Triples
    and N-Quads (section "Grammar") put no raw line break inside any token,
    so the end of that line is the next place a statement can start;
  * `LenientOptions.maxErrors = some m`: the error after the `m`-th is
    reported as one `tooManyErrors` diagnostic and the walk stops.

One walk, `foldLinesLenient`, serves both syntaxes: it takes the statement
reader as a parameter (`quadReader` reads N-Quads statements, `tripleReader`
N-Triples triples with no graph label). It also takes the triple consumer
(`consume`, as `foldQuadLinesAcc` does) and the diagnostic consumer
(`report`), so a caller decides what is kept: the reference entry points keep
a dataset and a diagnostic list, the streaming CLI keeps a count and hands
each chunk's diagnostics out before the next chunk.

Line state. `LinePos` changes only at a LINE FEED. No N-Triples or N-Quads
token, white space run or comment holds a raw line break, so the walk
advances its `LinePos` only over the characters `skipEol` consumes, and the
cost of line tracking is constant per line. A diagnostic walks from the
start of the failing statement to the error offset (`Diagnostic.ofError`),
which is inside that line.

Theorems (`NQuadsLenientTheorems.lean`):
  * on input the strict parser accepts, the lenient walk gives the strict
    result and reports nothing, for every consumer;
  * the indexed accumulator (`addQuadFast`) and the reference one (`addQuad`)
    give the same lenient result;
  * `parseNTriplesLenient`, `parseNQuadsLenient`, `parseNQuadsFastLenient`:
    `parseX s = .ok d → parseXLenient s = (d, [])`;
  * the converse, `parseNTriples_ok_of_lenient_quiet` and
    `parseNQuads_ok_of_lenient_quiet`: a lenient parse that reports no
    diagnostic means the strict parser accepts. So a document the strict
    parser refuses always gets at least one diagnostic.

Streaming (`LenientStream`): the chunked execution cuts each buffer after its
last line feed (`NQuadsStreaming.splitCompleteLines`, whose three theorems
say nothing is lost and only whole lines are parsed) and runs the same walk
on the whole lines, carrying the absolute offset, the line state, the error
count and the consumer states. It retains the consumer states and at most one
partial line. Agreement with the reference lenient walk is checked by
`#guard`s at every two-way split and with one-character chunks, below.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.Diagnostics
import L4Factoidal.Syntax.NQuadsFast

namespace L4Factoidal.Syntax

open L4Factoidal.RDF
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## The run state -/

/-- What a lenient walk carries: the triple consumer's state, the diagnostic
consumer's state, the number of errors reported, whether `maxErrors` stopped
the walk, and the line state at the walk's current offset. -/
structure LenientRun (α β : Type) where
  acc : α
  diags : β
  errors : Nat := 0
  stopped : Bool := false
  linePos : LinePos := {}

/-- Record the error `e`, raised reading `cs` whose first character is at
`pos`. Returns the new run and `true` when the walk continues. -/
def LenientRun.recordError {α β : Type} (opts : LenientOptions)
    (report : β → Diagnostic → β) (run : LenientRun α β) (pos : Nat) (cs : List Char)
    (e : ParseError) : LenientRun α β × Bool :=
  let d := Diagnostic.ofError run.linePos pos cs e
  if opts.allows run.errors then
    ({ run with diags := report run.diags d, errors := run.errors + 1 }, true)
  else
    ({ run with diags := report run.diags (d.overLimit (opts.maxErrors.getD 0)),
                stopped := true }, false)

/-! ## Statement readers -/

/-- A statement reader: a triple, its graph label (`none` for the default
graph), and the offset and characters after it. -/
abbrev LineReader := Nat → List Char → Except ParseError (Triple × Option Subject × Nat × List Char)

/-- N-Quads `[2] statement`, the reader `foldQuadLinesAcc` calls. -/
def quadReader (mode : Mode) : LineReader := fun pos cs =>
  match mode with
  | .rdf11 => readNQuad11 pos cs
  | .rdf12 => readNQuad12 pos cs

/-- N-Triples `[2] triple`, the reader `parseLinesAcc` calls, with no graph
label. -/
def tripleReader (mode : Mode) : LineReader := fun pos cs =>
  match (match mode with
         | .rdf11 => readTriple11 pos cs
         | .rdf12 => readTriple12 pos cs) with
  | .error e => .error e
  | .ok (t, p, r) => .ok (t, none, p, r)

/-! ## The lenient walk -/

/-- `foldQuadLinesAcc` with recovery. The four non-statement branches are the
strict walk's; the statement branch reports an error and resumes at the next
line. `fuel` bounds the number of rounds: every round consumes at least one
character, so `cs.length + 1` never runs out first (the strict walk's bound).
Exhaustion is reported as an `internal` diagnostic. -/
def foldLinesLenient (reader : LineReader) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) :
    Nat → Nat → List Char → LenientRun α β → LenientRun α β
  | 0, pos, cs, run =>
      { (run.recordError opts report pos cs
          ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩).1 with
        stopped := true }
  | fuel' + 1, pos, cs, run =>
      let (pos1, cs1) := skipWs pos cs
      match cs1 with
      | [] => run
      | '#' :: _ =>
          let (pos2, cs2) := skipComment pos1 cs1
          let (pos3, cs3) := skipEol pos2 cs2
          foldLinesLenient reader consume report opts fuel' pos3 cs3
            { run with linePos := run.linePos.advance pos2 (pos3 - pos2) cs2 }
      | '\n' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          foldLinesLenient reader consume report opts fuel' pos2 cs2
            { run with linePos := run.linePos.advance pos1 (pos2 - pos1) cs1 }
      | '\r' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          foldLinesLenient reader consume report opts fuel' pos2 cs2
            { run with linePos := run.linePos.advance pos1 (pos2 - pos1) cs1 }
      | _ =>
          match reader pos1 cs1 with
          | .error e =>
              match run.recordError opts report pos1 cs1 e with
              | (run', false) => run'
              | (run', true) =>
                  let (pos2, cs2) := skipToEol pos1 cs1
                  let (pos3, cs3) := skipEol pos2 cs2
                  foldLinesLenient reader consume report opts fuel' pos3 cs3
                    { run' with linePos := run'.linePos.advance pos2 (pos3 - pos2) cs2 }
          | .ok (t, gopt, pos2, cs2) =>
              let acc' := consume run.acc t gopt
              let (pos3, cs3) := skipWs pos2 cs2
              let (pos4, cs4) := skipComment pos3 cs3
              let (pos5, cs5) := skipEol pos4 cs4
              foldLinesLenient reader consume report opts fuel' pos5 cs5
                { run with acc := acc', linePos := run.linePos.advance pos4 (pos5 - pos4) cs4 }

/-- Run the lenient walk over a whole document from offset 0. -/
def lenientLines (reader : LineReader) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (cs : List Char) (acc : α) (diags : β) : LenientRun α β :=
  foldLinesLenient reader consume report opts (cs.length + 1) 0 cs { acc, diags }

/-- Collect diagnostics newest first; the entry points reverse once. -/
def pushDiag (ds : List Diagnostic) (d : Diagnostic) : List Diagnostic := d :: ds

/-! ## Reference entry points -/

/-- Lenient `parseNTriples`: the triples of every statement that parses, in
source order, and one diagnostic per skipped statement, in source order. -/
def parseNTriplesLenient (s : String) (mode : Mode := .rdf11) (opts : LenientOptions := {}) :
    Graph × List Diagnostic :=
  let out := lenientLines (tripleReader mode) (fun acc t _ => t :: acc) pushDiag opts
    s.toList [] []
  (out.acc.reverse, out.diags.reverse)

/-- Lenient `parseNQuads` (the reference accumulator `addQuad`). -/
def parseNQuadsLenient (s : String) (mode : Mode := .rdf11) (opts : LenientOptions := {}) :
    Dataset × List Diagnostic :=
  let out := lenientLines (quadReader mode) (fun ds t gopt => addQuad ds t gopt) pushDiag opts
    s.toList Dataset.empty []
  (out.acc, out.diags.reverse)

/-- Lenient `parseNQuadsFast` (the indexed accumulator `addQuadFast`). Equal
to `parseNQuadsLenient` (`parseNQuadsFastLenient_eq`). -/
def parseNQuadsFastLenient (s : String) (mode : Mode := .rdf11) (opts : LenientOptions := {}) :
    Dataset × List Diagnostic :=
  let out := lenientLines (quadReader mode) addQuadFast pushDiag opts s.toList {} []
  (out.acc.toDataset, out.diags.reverse)

/-! ## Streaming -/

/-- A chunked lenient walk: the run state, the partial line not yet parsed,
and the absolute offset at which that partial line starts. -/
structure LenientStream (α β : Type) where
  run : LenientRun α β
  carry : List Char := []
  pos : Nat := 0

def LenientStream.init {α β : Type} (acc : α) (diags : β) : LenientStream α β :=
  { run := { acc, diags } }

/-- Take one chunk: every whole line of `carry ++ chunk` is walked now, the
rest waits. After `maxErrors` stopped the walk, chunks are ignored. -/
def LenientStream.feed (reader : LineReader) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (st : LenientStream α β) (chunk : List Char) :
    LenientStream α β :=
  if st.run.stopped then st
  else
    let (complete, carry) := splitCompleteLines (st.carry ++ chunk)
    { run := foldLinesLenient reader consume report opts (complete.length + 1) st.pos complete
               st.run,
      carry := carry,
      pos := st.pos + complete.length }

/-- End of input: walk the last partial line. -/
def LenientStream.finish (reader : LineReader) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (st : LenientStream α β) : LenientRun α β :=
  if st.run.stopped then st.run
  else foldLinesLenient reader consume report opts (st.carry.length + 1) st.pos st.carry st.run

/-- Hand the diagnostics collected so far to the caller and clear them, so a
streaming caller retains at most one chunk's diagnostics. -/
def LenientStream.takeDiags {α : Type} (st : LenientStream α (List Diagnostic)) :
    List Diagnostic × LenientStream α (List Diagnostic) :=
  (st.run.diags.reverse, { st with run := { st.run with diags := [] } })

/-- Fold a list of chunks, then finish. -/
def lenientStreamLines (reader : LineReader) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (chunks : List (List Char)) (acc : α) (diags : β) :
    LenientRun α β :=
  LenientStream.finish reader consume report opts
    (chunks.foldl (LenientStream.feed reader consume report opts) (LenientStream.init acc diags))

/-! ## Build-time checks -/

private def ex (n : Nat) : String := s!"<http://e/{n}>"

/-- Three good statements around three bad ones, one per line, plus a
comment, a blank line, a CR LF line end and a statement after a good one on
the same line. -/
private def docMixed : String :=
  "# header\n" ++
  ex 1 ++ " " ++ ex 2 ++ " " ++ ex 3 ++ " .\n" ++          -- line 2, good
  ex 1 ++ " " ++ ex 2 ++ " .\n" ++                        -- line 3, missing object
  "\n" ++
  "\"lit\" " ++ ex 2 ++ " " ++ ex 3 ++ " .\r\n" ++        -- line 5, literal subject
  ex 4 ++ " " ++ ex 5 ++ " \"bad \\q\" .\n" ++            -- line 6, bad escape
  ex 4 ++ " " ++ ex 5 ++ " \"ok\"@en . " ++ ex 6 ++ " .\n" ++  -- line 7, good then bad
  ex 7 ++ " " ++ ex 8 ++ " " ++ ex 9 ++ " .\n"            -- line 8, good

private def tripleCount (r : Graph × List Diagnostic) : Nat := r.1.length
private def lines (r : Graph × List Diagnostic) : List Nat := r.2.map (·.line)
private def classes (r : Graph × List Diagnostic) : List DiagnosticClass := r.2.map (·.cls)

-- N-Triples: three good triples kept, four errors reported in source order.
#guard tripleCount (parseNTriplesLenient docMixed) == 3
#guard lines (parseNTriplesLenient docMixed) == [3, 5, 6, 7]
#guard classes (parseNTriplesLenient docMixed)
        == [.unexpectedToken, .unexpectedToken, .badEscape, .unexpectedToken]
-- Every line and column agrees with the offset recomputed from the start.
#guard (parseNTriplesLenient docMixed).2.all fun d =>
        d == Diagnostic.ofError {} 0 docMixed.toList ⟨d.message, d.offset⟩
-- The first diagnostic is the strict parser's error.
#guard (match parseNTriples docMixed with
        | .error e => (parseNTriplesLenient docMixed).2.head?.map (fun d => (d.message, d.offset))
                        == some (e.msg, e.pos)
        | .ok _ => false)
-- No errors: the strict graph and no diagnostics.
private def docGood : String := ex 1 ++ " " ++ ex 2 ++ " " ++ ex 3 ++ " .\n# c\n" ++
  "_:b " ++ ex 2 ++ " \"x\"@en .\r\n"
#guard (match parseNTriples docGood with
        | .ok g => parseNTriplesLenient docGood == (g, [])
        | .error _ => false)
-- An empty document.
#guard parseNTriplesLenient "" == ([], [])

-- maxErrors: two errors reported, then one tooManyErrors at the third, and
-- the walk stops (line 8's triple is not read).
#guard classes (parseNTriplesLenient docMixed .rdf11 { maxErrors := some 2 })
        == [.unexpectedToken, .unexpectedToken, .tooManyErrors]
#guard tripleCount (parseNTriplesLenient docMixed .rdf11 { maxErrors := some 2 }) == 1
#guard (parseNTriplesLenient docMixed .rdf11 { maxErrors := some 2 }).2.getLast?.map (·.line)
        == some 6
-- maxErrors = 0 stops at the first error.
#guard classes (parseNTriplesLenient docMixed .rdf11 { maxErrors := some 0 }) == [.tooManyErrors]
-- A bound that is never reached changes nothing.
#guard parseNTriplesLenient docMixed .rdf11 { maxErrors := some 4 } == parseNTriplesLenient docMixed

-- N-Quads: the same document, plus graph labels.
private def docQuads : String :=
  ex 1 ++ " " ++ ex 2 ++ " " ++ ex 3 ++ " " ++ ex 10 ++ " .\n" ++
  ex 1 ++ " " ++ ex 2 ++ " \"x\" \"g\" .\n" ++             -- literal graph label
  ex 1 ++ " " ++ ex 2 ++ " " ++ ex 3 ++ " .\n" ++
  ex 1 ++ " " ++ ex 2 ++ " " ++ ex 4 ++ " _:g .\n" ++
  ex 1 ++ " " ++ ex 2 ++ " " ++ ex 4 ++ " " ++ ex 11 ++ " " ++ ex 12 ++ " .\n"  -- extra term

private def shape (r : Dataset × List Diagnostic) :
    (Graph × List (Subject × Graph)) × List (Nat × DiagnosticClass) :=
  ((r.1.default, r.1.named.map fun ng => (ng.name, ng.graph)), r.2.map fun d => (d.line, d.cls))

#guard (shape (parseNQuadsLenient docQuads)).2 == [(2, .badGraphName), (5, .unexpectedToken)]
#guard (parseNQuadsLenient docQuads).1.default.length == 1
#guard (parseNQuadsLenient docQuads).1.named.length == 2
-- The indexed accumulator agrees (the theorem is `parseNQuadsFastLenient_eq`).
#guard shape (parseNQuadsFastLenient docQuads) == shape (parseNQuadsLenient docQuads)
#guard shape (parseNQuadsFastLenient docMixed) == shape (parseNQuadsLenient docMixed)
-- An N-Triples document is an N-Quads document: the same diagnostics.
#guard (parseNQuadsLenient docMixed).2 == (parseNTriplesLenient docMixed).2

/-! ### Streaming agrees with the reference walk

Every two-way split of each document, and one-character chunks. The consumer
counts triples; the diagnostics are compared whole (class, message, offset,
line, column). -/

private def countC : Nat → Triple → Option Subject → Nat := fun n _ _ => n + 1

private def refRun (reader : LineReader) (opts : LenientOptions) (doc : String) :
    Nat × List Diagnostic :=
  let out := lenientLines reader countC pushDiag opts doc.toList 0 []
  (out.acc, out.diags)

private def streamRun (reader : LineReader) (opts : LenientOptions) (chunks : List (List Char)) :
    Nat × List Diagnostic :=
  let out := lenientStreamLines reader countC pushDiag opts chunks 0 []
  (out.acc, out.diags)

/-- `true` when every two-way split and the one-character chunking agree with
the reference walk. -/
private def splitsAgree (reader : LineReader) (opts : LenientOptions) (doc : String) : Bool :=
  let cs := doc.toList
  let r := refRun reader opts doc
  (List.range (cs.length + 1)).all (fun k => streamRun reader opts [cs.take k, cs.drop k] == r) &&
  streamRun reader opts (cs.map fun c => [c]) == r

#guard splitsAgree (quadReader .rdf11) {} docMixed
#guard splitsAgree (quadReader .rdf11) {} docQuads
#guard splitsAgree (tripleReader .rdf11) {} docMixed
#guard splitsAgree (quadReader .rdf11) { maxErrors := some 1 } docMixed
#guard splitsAgree (quadReader .rdf12) {} docQuads
-- A document with no final line feed, and one that is only a bad line.
#guard splitsAgree (quadReader .rdf11) {} (ex 1 ++ " " ++ ex 2 ++ " .\n" ++ ex 1 ++ " " ++ ex 2 ++ " " ++ ex 3 ++ " .")
#guard splitsAgree (quadReader .rdf11) {} "<a> ."
-- The reference walk itself, through the stream entry with one chunk.
#guard streamRun (quadReader .rdf11) {} [docMixed.toList] == refRun (quadReader .rdf11) {} docMixed
-- takeDiags hands out the diagnostics in source order and clears them.
#guard (let st := LenientStream.feed (quadReader .rdf11) countC pushDiag {}
          (LenientStream.init 0 []) docMixed.toList
        let (ds, st') := st.takeDiags
        ds.map (·.line) == [3, 5, 6, 7] && st'.run.diags.isEmpty)

end L4Factoidal.Syntax
