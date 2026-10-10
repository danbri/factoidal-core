/-
L4Factoidal.Syntax.TurtleLenient — lenient (recovery) mode for Turtle and
TriG, reference and streaming (https://github.com/danbri/factoidal/issues/716).

The strict parsers (`parseTurtle`, `parseTurtleFold`, `parseTriG`, the chunk
fold `TurtleChunkFold`) are unchanged. The lenient walks are separate
functions.

## Turtle

`parseStatementsLenient` has the shape of `parseStatementsFold`: skip white
space and comments, read one `[2] statement` with `readStatement`, fold its
triples, carry the `TurtleState`. Only the error arm differs:

  * the error becomes a `Diagnostic`. When the statement starts with a
    directive keyword (`@prefix`, `@base`, `@version`, or `PREFIX`, `BASE`,
    `VERSION` not followed by a name character), the diagnostic carries the
    directive reader's own error (`directiveError`): `readStatement` tries
    the directives first and, when they fail, reports what the triples
    reader says about the keyword ("expected subject"), which tells a
    validator user nothing. A `VERSION` directive in an RDF 1.1 document is
    reported as RDF 1.2 syntax;
  * the walk resumes at the next statement boundary that
    `TurtleStatementScan` defines, at or after the error offset
    (`turtleResync`): a fresh scanner runs from the start of the failing
    statement (where the lexical mode is known to be normal) and the walk
    resumes at the first character before which the scanner cuts a
    candidate — after a `.` in normal mode followed by white space or `#`,
    or at the line end of a `PREFIX`/`BASE`/`VERSION` line — whose offset is
    not less than the error offset. With no such cut, the walk ends;
  * the `TurtleState` is the one before the failing statement. So after a
    bad `@prefix`, the prefix stays undefined and each later use of it gets
    its own `undefinedPrefix` diagnostic.

On input `parseTurtle` accepts, the walk gives the strict graph and reports
nothing (`TurtleLenientTheorems.parseTurtleLenient_of_ok`).

## Streaming Turtle

`TurtleChunkLenientState` is `TurtleChunkFoldState` with the lenient walk:
the scanner (`TurtleStatementScan`) proposes candidates as decoded chunks
arrive, and each candidate is walked by `parseStatementsLenient` with fuel
from that candidate, carrying the absolute offset, the line state, the
`TurtleState` and the consumer states. A resynchronisation inside a candidate
stops at the end of the candidate. It retains the consumer states, the
current unfinished candidate and that candidate's scanner state.

Agreement with the reference walk is the differential check named in the
design record (`docs/designissues/2026-09-03-rdf-parsing-strategy.md`
section 3a): `#guard`s below, at every two-way split and with one-character
chunks, comparing triples and diagnostics whole. There is no theorem: the
chunk-boundary half of the strict Turtle streaming agreement is not proved
either (record, section 2.3).

## TriG

`parseTriGStatementsLenient` runs the strict top-level reader
`readTriGStatement` (the linear reader over the `FastDataset` accumulator,
2026-10-10) first. When it succeeds, the walk is the strict walk.
When it fails on a graph block (`{ … }`, `GRAPH label { … }` or
`label { … }`), the block is read again by `readTriGBlockRecover`, which
recovers inside the block: each failing statement is reported and the body
resumes at the next scanner cut at or after the error, or at a `}` in normal
mode at or after the error, whichever is first; the good statements stay in
the block's graph. Any other failure is reported at the top level, which
resumes as Turtle does. A recovered block that reports nothing (the recovery
reader accepted what the strict reader refused) is not used: the strict
error is reported instead, so a document `parseTriG` refuses always gets at
least one diagnostic.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.Diagnostics
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.TurtleStatementScan
import L4Factoidal.Syntax.NQuadsLenient

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Synchronisation -/

/-- `turtleResync`'s loop: feed characters to the statement scanner; stop
before the first character at which it cuts a candidate, if that character is
at or after `errPos`. -/
def turtleResyncLoop (errPos : Nat) : StatementScan → Nat → List Char → Nat × List Char
  | _, pos, [] => (pos, [])
  | scan, pos, c :: rest =>
      let next := scan.feedChar c
      if !next.completedRev.isEmpty && errPos ≤ pos then (pos, c :: rest)
      else turtleResyncLoop errPos { next with completedRev := [] } (pos + 1) rest

/-- The next statement boundary of `TurtleStatementScan` at or after
`errPos`, scanning from `pos`, the start of the failing statement. -/
def turtleResync (pos : Nat) (cs : List Char) (errPos : Nat) : Nat × List Char :=
  turtleResyncLoop errPos StatementScan.init pos cs

/-- The TriG graph-body form of `turtleResync`: also stop at a `}` in normal
mode at or after `errPos`, so the body can close its block. -/
def trigBodyResyncLoop (errPos : Nat) : StatementScan → Nat → List Char → Nat × List Char
  | _, pos, [] => (pos, [])
  | scan, pos, c :: rest =>
      if c == '}' && scan.mode == .normal && errPos ≤ pos then (pos, c :: rest)
      else
        let next := scan.feedChar c
        if !next.completedRev.isEmpty && errPos ≤ pos then (pos, c :: rest)
        else trigBodyResyncLoop errPos { next with completedRev := [] } (pos + 1) rest

def trigBodyResync (pos : Nat) (cs : List Char) (errPos : Nat) : Nat × List Char :=
  trigBodyResyncLoop errPos StatementScan.init pos cs

/-! ## Directive diagnostics -/

/-- `kw` (any case) is the token here: what follows cannot continue a name. -/
def keywordCiAt (kw : String) (cs : List Char) : Bool :=
  match matchKeyword true kw.toList cs with
  | none => false
  | some [] => true
  | some (c :: _) => !(isPnChars c || c == ':')

/-- The error to report for a failing statement at `pos`: the directive
reader's own error when the statement starts with a directive keyword, the
grammar's error `e` otherwise. -/
def directiveError (st : TurtleState) (pos : Nat) (cs : List Char) (e : ParseError) : ParseError :=
  if (matchKeyword false "@prefix".toList cs).isSome || keywordCiAt "PREFIX" cs then
    match readPrefixDirective st pos cs with
    | .error e' => e'
    | .ok _ => e
  else if (matchKeyword false "@base".toList cs).isSome || keywordCiAt "BASE" cs then
    match readBaseDirective st pos cs with
    | .error e' => e'
    | .ok _ => e
  else if (matchKeyword false "@version".toList cs).isSome || keywordCiAt "VERSION" cs then
    if st.mode == .rdf12 then
      match readVersionDirective pos cs with
      | .error e' => e'
      | .ok _ => e
    else ⟨"a version directive requires RDF 1.2 mode", pos⟩
  else e

/-! ## The run state -/

/-- What a lenient Turtle or TriG walk carries: the triple consumer's state,
the diagnostic consumer's state, the Turtle parser state (prefixes, base,
blank-node counter, mode), the error count, the stop flag, and the line
state at the walk's current offset. -/
structure TurtleLenientRun (α β : Type) where
  acc : α
  diags : β
  turtle : TurtleState
  errors : Nat := 0
  stopped : Bool := false
  linePos : LinePos := {}

/-- `LenientRun.recordError` for this run type. -/
def TurtleLenientRun.recordError {α β : Type} (opts : LenientOptions)
    (report : β → Diagnostic → β) (run : TurtleLenientRun α β) (pos : Nat) (cs : List Char)
    (e : ParseError) : TurtleLenientRun α β × Bool :=
  let d := Diagnostic.ofError run.linePos pos cs e
  if opts.allows run.errors then
    ({ run with diags := report run.diags d, errors := run.errors + 1 }, true)
  else
    ({ run with diags := report run.diags (d.overLimit (opts.maxErrors.getD 0)),
                stopped := true }, false)

/-! ## Turtle -/

/-- `parseStatementsFold` with recovery (module header). -/
def parseStatementsLenient {α β : Type} (step : α → List Triple → α)
    (report : β → Diagnostic → β) (opts : LenientOptions) :
    Nat → Nat → List Char → TurtleLenientRun α β → TurtleLenientRun α β
  | 0, _, _, run => run
  | fuel + 1, pos, cs, run =>
      let (p1, r1) := tws pos cs
      let lp1 := run.linePos.advance pos (p1 - pos) cs
      match r1 with
      | [] => { run with linePos := lp1 }
      | _ =>
          match readStatement fuel run.turtle p1 r1 with
          | .error e =>
              let e' := directiveError run.turtle p1 r1 e
              match ({ run with linePos := lp1 }).recordError opts report p1 r1 e' with
              | (run', false) => run'
              | (run', true) =>
                  let (p2, r2) := turtleResync p1 r1 e'.pos
                  parseStatementsLenient step report opts fuel p2 r2
                    { run' with linePos := lp1.advance p1 (p2 - p1) r1 }
          | .ok (ts, st', p2, r2) =>
              let acc' := step run.acc ts
              if p2 ≤ p1 then { run with acc := acc', turtle := st', linePos := lp1 }
              else parseStatementsLenient step report opts fuel p2 r2
                     { run with acc := acc', turtle := st', linePos := lp1.advance p1 (p2 - p1) r1 }

/-- The run a whole-document Turtle walk starts from. -/
def TurtleLenientRun.init {α β : Type} (acc : α) (diags : β) (st : TurtleState) :
    TurtleLenientRun α β :=
  { acc, diags, turtle := st }

/-- Lenient `parseTurtle`: the triples of every statement that parses, in
source order, the diagnostics in source order, and the prefixes in force at
the end (most recent first, as `parseTurtleWithPrefixes`). -/
def parseTurtleLenientWithPrefixes (text : String) (base : Option String := none)
    (mode : Mode := .rdf11) (opts : LenientOptions := {}) :
    Graph × List Diagnostic × List (String × String) :=
  let cs := text.toList
  let out := parseStatementsLenient prependReverse pushDiag opts (cs.length + 2) 0 cs
    (TurtleLenientRun.init [] [] (TurtleState.initChars cs base mode))
  (out.acc.reverse, out.diags.reverse, out.turtle.prefixes)

def parseTurtleLenient (text : String) (base : Option String := none)
    (mode : Mode := .rdf11) (opts : LenientOptions := {}) : Graph × List Diagnostic :=
  let r := parseTurtleLenientWithPrefixes text base mode opts
  (r.1, r.2.1)

/-! ## Streaming Turtle -/

/-- `TurtleChunkFoldState` with the lenient walk. -/
structure TurtleChunkLenientState (α β : Type) where
  run : TurtleLenientRun α β
  pos : Nat := 0
  scanner : StatementScan := StatementScan.init

/-- Walk every completed candidate, each with its own fuel. -/
def consumeCandidatesLenient {α β : Type} (step : α → List Triple → α)
    (report : β → Diagnostic → β) (opts : LenientOptions) :
    List String → TurtleLenientRun α β → Nat → TurtleLenientRun α β × Nat
  | [], run, pos => (run, pos)
  | text :: texts, run, pos =>
      if run.stopped then (run, pos)
      else
        let cs := text.toList
        consumeCandidatesLenient step report opts texts
          (parseStatementsLenient step report opts (cs.length + 2) pos cs run) (pos + cs.length)

/-- Begin a lenient chunk walk after a pre-pass has supplied the generated
blank-node prefix (as `TurtleChunkFoldState.init`). -/
def TurtleChunkLenientState.init {α β : Type} (bnodePrefix : String) (acc : α) (diags : β)
    (base : Option String := none) (mode : Mode := .rdf11) : TurtleChunkLenientState α β :=
  { run := TurtleLenientRun.init acc diags (TurtleState.initWithBnodePrefix bnodePrefix base mode) }

/-- Feed one decoded chunk. After `maxErrors` stopped the walk, chunks are
ignored. -/
def TurtleChunkLenientState.feed {α β : Type} (step : α → List Triple → α)
    (report : β → Diagnostic → β) (opts : LenientOptions)
    (state : TurtleChunkLenientState α β) (chunk : String) : TurtleChunkLenientState α β :=
  if state.run.stopped then state
  else
    let (candidates, scanner) := (state.scanner.feed chunk).drain
    let (run, pos) := consumeCandidatesLenient step report opts candidates state.run state.pos
    { run, pos, scanner }

/-- End of input: walk the last unfinished candidate. -/
def TurtleChunkLenientState.finish {α β : Type} (step : α → List Triple → α)
    (report : β → Diagnostic → β) (opts : LenientOptions)
    (state : TurtleChunkLenientState α β) : TurtleLenientRun α β :=
  if state.run.stopped then state.run
  else
    let cs := state.scanner.remainder.toList
    parseStatementsLenient step report opts (cs.length + 2) state.pos cs state.run

/-- Hand the diagnostics collected so far to the caller and clear them. -/
def TurtleChunkLenientState.takeDiags {α : Type} (st : TurtleChunkLenientState α (List Diagnostic)) :
    List Diagnostic × TurtleChunkLenientState α (List Diagnostic) :=
  (st.run.diags.reverse, { st with run := { st.run with diags := [] } })

/-- Fold a list of decoded chunks, then finish. -/
def parseTurtleChunksLenient {α β : Type} (bnodePrefix : String) (step : α → List Triple → α)
    (report : β → Diagnostic → β) (opts : LenientOptions) (acc : α) (diags : β)
    (chunks : List String) (base : Option String := none) (mode : Mode := .rdf11) :
    TurtleLenientRun α β :=
  (chunks.foldl (TurtleChunkLenientState.feed step report opts)
    (TurtleChunkLenientState.init bnodePrefix acc diags base mode)).finish step report opts

/-! ## TriG -/

/-- A graph block's body with recovery: `readGraphBody`, except that a
failing statement is reported and the body resumes at `trigBodyResync`, and
the end of input inside the block is reported and closes the block.
`pos`/`cs` start just after the `{`; `accRev` holds the block's triples newest
first and the result is in source order, as in `readGraphBody`. The run's
`acc` is not touched. `.error` only when `maxErrors` stops the walk (the run
then says `stopped`). -/
def readGraphBodyRecover {α β : Type} (report : β → Diagnostic → β) (opts : LenientOptions) :
    Nat → TurtleState → Nat → List Char → List Triple → TurtleLenientRun α β →
      Except ParseError (List Triple × TurtleState × Nat × List Char) × TurtleLenientRun α β
  | 0, st, pos, cs, accRev, run => (.ok (accRev.reverse, st, pos, cs), run)
  | fuel + 1, st, pos, cs, accRev, run =>
      let (p1, r1) := tws pos cs
      let lp1 := run.linePos.advance pos (p1 - pos) cs
      match r1 with
      | [] =>
          -- End of input inside the block: report it and close the block,
          -- keeping the statements read so far.
          let e : ParseError := ⟨"unterminated graph block (expected '}')", p1⟩
          match ({ run with linePos := lp1 }).recordError opts report p1 r1 e with
          | (run', false) => (.error e, run')
          | (run', true) => (.ok (accRev.reverse, st, p1, []), run')
      | '}' :: r2 => (.ok (accRev.reverse, st, p1 + 1, r2), { run with linePos := lp1 })
      | _ =>
          let stmt : Except ParseError (List Triple × TurtleState × Nat × List Char) :=
            if isDirectiveAt r1 then .error ⟨"directives are not allowed inside a graph block", p1⟩
            else if isGraphKeyword r1 then
              .error ⟨"nested GRAPH is not allowed inside a graph block", p1⟩
            else readStatement fuel st p1 r1
          match stmt with
          | .error e =>
              match ({ run with linePos := lp1 }).recordError opts report p1 r1 e with
              | (run', false) => (.error e, run')
              | (run', true) =>
                  let (p2, r2) := trigBodyResync p1 r1 e.pos
                  readGraphBodyRecover report opts fuel st p2 r2 accRev
                    { run' with linePos := lp1.advance p1 (p2 - p1) r1 }
          | .ok (ts, st', p2, r2) =>
              let nextAcc := ts.reverse ++ accRev
              if p2 ≤ p1 then (.ok (nextAcc.reverse, st', p2, r2), { run with linePos := lp1 })
              else readGraphBodyRecover report opts fuel st' p2 r2 nextAcc
                     { run with linePos := lp1.advance p1 (p2 - p1) r1 }

/-- A top-level TriG graph block read with recovery inside its body. `none`
when the statement is not a graph block or its header does not parse; the
caller then reports the strict error. `fuel` is the caller's statement budget,
as for `readTriGStatement`. The run's line state is at `pos` on entry. -/
def readTriGBlockRecover {α β : Type} (report : β → Diagnostic → β) (opts : LenientOptions)
    (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) (run : TurtleLenientRun α β) :
    Option (Except ParseError ((Option Subject × List Triple) × TurtleState × Nat × List Char) ×
      TurtleLenientRun α β) :=
  let body (g : Option Subject) (st' : TurtleState) (p : Nat) (r : List Char) :=
    -- `p`, `r`: just after the `{`.
    let run' := { run with linePos := run.linePos.advance pos (p - pos) cs }
    match readGraphBodyRecover report opts fuel st' p r [] run' with
    | (.error e, run'') => some (.error e, run'')
    | (.ok (ts, st'', p', r'), run'') => some (.ok ((g, ts), st'', p', r'), run'')
  match cs with
  | '{' :: r2 => body none st (pos + 1) r2
  | _ =>
      if isGraphKeyword cs then
        let (p2, r2) := tws (pos + 5) (cs.drop 5)
        match readLabelOrSubject st p2 r2 with
        | .error _ => none
        | .ok (g, st2, p3, r3) =>
            let (p4, r4) := tws p3 r3
            match r4 with
            | '{' :: r5 => body (some g) st2 (p4 + 1) r5
            | _ => none
      else
        match readLabelOrSubject st pos cs with
        | .error _ => none
        | .ok (g, st2, p2, r2) =>
            let (p3, r3) := tws p2 r2
            match r3 with
            | '{' :: r4 => body (some g) st2 (p3 + 1) r4
            | _ => none

/-- `parseTriGStatements` with recovery (module header). The accumulator is
the strict walk's `FastDataset`. -/
def parseTriGStatementsLenient {β : Type} (report : β → Diagnostic → β) (opts : LenientOptions) :
    Nat → Nat → List Char → TurtleLenientRun FastDataset β → TurtleLenientRun FastDataset β
  | 0, _, _, run => run
  | fuel + 1, pos, cs, run =>
      let (p1, r1) := tws pos cs
      let lp1 := run.linePos.advance pos (p1 - pos) cs
      match r1 with
      | [] => { run with linePos := lp1 }
      | _ =>
          match readTriGStatement fuel run.turtle p1 r1 with
          | .ok ((gname, ts), st', p2, r2) =>
              let ds' := addTriplesToFast run.acc gname ts
              if p2 ≤ p1 then { run with acc := ds', turtle := st', linePos := lp1 }
              else parseTriGStatementsLenient report opts fuel p2 r2
                     { run with acc := ds', turtle := st', linePos := lp1.advance p1 (p2 - p1) r1 }
          | .error e =>
              let run1 := { run with linePos := lp1 }
              -- A graph block: recover inside it, if that reports something.
              let recovered :=
                match readTriGBlockRecover report opts fuel run.turtle p1 r1 run1 with
                | some (.ok ((gname, ts), st', p2, r2), run2) =>
                    if run2.errors > run.errors || run2.stopped then
                      some (gname, ts, st', p2, r2, run2)
                    else none
                | some (.error _, run2) =>
                    if run2.stopped then some (none, [], run.turtle, p1, r1, run2) else none
                | none => none
              match recovered with
              | some (gname, ts, st', p2, r2, run2) =>
                  let run3 := { run2 with acc := addTriplesToFast run.acc gname ts, turtle := st',
                                          linePos := lp1.advance p1 (p2 - p1) r1 }
                  if run2.stopped || p2 ≤ p1 then run3
                  else parseTriGStatementsLenient report opts fuel p2 r2 run3
              | none =>
                  let e' := directiveError run.turtle p1 r1 e
                  match run1.recordError opts report p1 r1 e' with
                  | (run', false) => run'
                  | (run', true) =>
                      let (p2, r2) := turtleResync p1 r1 e'.pos
                      parseTriGStatementsLenient report opts fuel p2 r2
                        { run' with linePos := lp1.advance p1 (p2 - p1) r1 }

/-- Lenient `parseTriG`, with the prefixes in force at the end. -/
def parseTriGLenientWithPrefixes (text : String) (base : Option String := none)
    (mode : Mode := .rdf11) (opts : LenientOptions := {}) :
    Dataset × List Diagnostic × List (String × String) :=
  let cs := text.toList
  let out := parseTriGStatementsLenient pushDiag opts (cs.length + 2) 0 cs
    (TurtleLenientRun.init ({} : FastDataset) [] (TurtleState.init text base mode))
  (out.acc.toDataset, out.diags.reverse, out.turtle.prefixes)

def parseTriGLenient (text : String) (base : Option String := none)
    (mode : Mode := .rdf11) (opts : LenientOptions := {}) : Dataset × List Diagnostic :=
  let r := parseTriGLenientWithPrefixes text base mode opts
  (r.1, r.2.1)

/-! ## Build-time checks: Turtle -/

private def lineCls (ds : List Diagnostic) : List (Nat × DiagnosticClass) :=
  ds.map fun d => (d.line, d.cls)

/-- Positions recomputed from the start of the document agree. -/
private def positionsAgree (doc : String) (ds : List Diagnostic) : Bool :=
  ds.all fun d => d == Diagnostic.ofError {} 0 doc.toList ⟨d.message, d.offset⟩

private def ttlMixed : String :=
  "@prefix ex: <http://example.org/> .\n" ++     -- 1
  "ex:a ex:p ex:o1 .\n" ++                       -- 2 good
  "ex:b ex:p .\n" ++                             -- 3 missing object
  "ex:c ex:p \"bad \\q\" ;\n" ++                 -- 4 bad escape, statement spans 2 lines
  "     ex:q ex:o2 .\n" ++                       -- 5
  "ex:d ex:p ex:o3 , ex:o4 .\n" ++               -- 6 good (2 triples)
  "nope:x ex:p ex:o5 .\n" ++                     -- 7 undefined prefix
  "ex:e ex:p \"\"\"long\n. string\"\"\" .\n" ++  -- 8-9 good (dot inside a long string)
  "ex:f ex:p ex:o6 .\n"                          -- 10 good

#guard (parseTurtleLenient ttlMixed).1.length == 5
#guard lineCls (parseTurtleLenient ttlMixed).2
        == [(3, .unexpectedToken), (4, .badEscape), (7, .undefinedPrefix)]
#guard positionsAgree ttlMixed (parseTurtleLenient ttlMixed).2
-- The first diagnostic is the strict parser's error (not a directive here).
#guard (match parseTurtle ttlMixed with
        | .error e => (parseTurtleLenient ttlMixed).2.head?.map (fun d => (d.message, d.offset))
                        == some (e.msg, e.pos)
        | .ok _ => false)
-- No errors: the strict graph and no diagnostics.
private def ttlGood : String :=
  "PREFIX ex: <http://example.org/>\nex:a ex:p [ ex:q 1.5 ] , ( 1 2 ) .\n# c\nex:b ex:p \"x\"@en .\n"
#guard (match parseTurtle ttlGood with
        | .ok g => parseTurtleLenient ttlGood == (g, [])
        | .error _ => false)

-- A bad @prefix: reported with the directive reader's error; the prefix
-- stays undefined, so each later use is its own diagnostic.
private def ttlBadPrefix : String :=
  "@prefix ex <http://example.org/> .\nex:a ex:p ex:o .\nex:b ex:p ex:o .\n<http://x/s> <http://x/p> <http://x/o> .\n"
#guard lineCls (parseTurtleLenient ttlBadPrefix).2
        == [(1, .badPrefixedName), (2, .undefinedPrefix), (3, .undefinedPrefix)]
#guard (parseTurtleLenient ttlBadPrefix).1.length == 1
-- SPARQL-style PREFIX without a dot: resynchronised at the line end.
#guard lineCls (parseTurtleLenient "PREFIX ex <http://example.org/>\n<http://x/s> <http://x/p> <http://x/o> .\n").2
        == [(1, .badPrefixedName)]
#guard (parseTurtleLenient "PREFIX ex <http://example.org/>\n<http://x/s> <http://x/p> <http://x/o> .\n").1.length == 1
-- VERSION in RDF 1.1.
#guard lineCls (parseTurtleLenient "VERSION \"1.2\"\n<http://x/s> <http://x/p> <http://x/o> .\n").2
        == [(1, .rdf12Syntax)]
-- A bad @base: relative IRIs after it fail on their own.
#guard (parseTurtleLenient "@base <http://b/> \n<s> <p> <o> .\n").2.length ≥ 1

-- maxErrors.
#guard lineCls (parseTurtleLenient ttlMixed none .rdf11 { maxErrors := some 1 }).2
        == [(3, .unexpectedToken), (4, .tooManyErrors)]
#guard (parseTurtleLenient ttlMixed none .rdf11 { maxErrors := some 1 }).1.length == 1

-- Resynchronisation does not stop at a dot inside a string, an IRI or a
-- comment: the bad statement below ends at line 2's final dot.
private def ttlDots : String :=
  "<http://x/s> <http://x/p> \"a. b\" <http://x/a.b> # c. d\n  \"x\" .\n<http://x/s> <http://x/p> <http://x/o> .\n"
#guard lineCls (parseTurtleLenient ttlDots).2 == [(1, .unexpectedToken)]
#guard (parseTurtleLenient ttlDots).1.length == 1

/-! ### Streaming Turtle agrees with the reference walk -/

private def ttlRef (opts : LenientOptions) (doc : String) : Graph × List Diagnostic :=
  parseTurtleLenient doc none .rdf11 opts

private def ttlStream (opts : LenientOptions) (doc : String) (chunks : List String) :
    Graph × List Diagnostic :=
  let out := parseTurtleChunksLenient (freshBnodePrefix doc) prependReverse pushDiag opts [] []
    chunks
  (out.acc.reverse, out.diags.reverse)

private def ttlSplitsAgree (opts : LenientOptions) (doc : String) : Bool :=
  let cs := doc.toList
  let r := ttlRef opts doc
  (List.range (cs.length + 1)).all (fun k =>
    ttlStream opts doc [String.ofList (cs.take k), String.ofList (cs.drop k)] == r) &&
  ttlStream opts doc (cs.map String.singleton) == r

#guard ttlSplitsAgree {} ttlMixed
#guard ttlSplitsAgree {} ttlBadPrefix
#guard ttlSplitsAgree {} ttlDots
#guard ttlSplitsAgree {} ttlGood
#guard ttlSplitsAgree { maxErrors := some 1 } ttlMixed
#guard ttlSplitsAgree {} "PREFIX ex <http://example.org/>\n<http://x/s> <http://x/p> <http://x/o> .\n"
#guard ttlSplitsAgree {} "<http://x/s> <http://x/p> . <http://x/s> <http://x/p> <http://x/o> ."

/-! ## Build-time checks: TriG -/

private def trigMixed : String :=
  "@prefix ex: <http://example.org/> .\n" ++     -- 1
  "ex:g1 {\n" ++                                 -- 2
  "  ex:a ex:p ex:o1 .\n" ++                     -- 3 good
  "  ex:b ex:p .\n" ++                           -- 4 missing object
  "  ex:c ex:p ex:o2\n" ++                       -- 5 good, last statement without a dot
  "}\n" ++                                       -- 6
  "ex:d ex:p ex:o3 .\n" ++                       -- 7 good, default graph
  "GRAPH ex:g2 { ex:e ex:p \"bad \\q\" }\n" ++   -- 8 bad escape before '}'
  "nope:f ex:p ex:o4 .\n" ++                     -- 9 undefined prefix
  "{ ex:h ex:p ex:o5 }\n"                        -- 10 good, default graph

private def trigShape (r : Dataset × List Diagnostic) :
    (Nat × List (Subject × Nat)) × List (Nat × DiagnosticClass) :=
  ((r.1.default.length, r.1.named.map fun ng => (ng.name, ng.graph.length)), lineCls r.2)

#guard (trigShape (parseTriGLenient trigMixed)).2
        == [(4, .unexpectedToken), (8, .badEscape), (9, .undefinedPrefix)]
-- The good statements stay in their graphs: ex:g1 keeps two triples.
#guard (trigShape (parseTriGLenient trigMixed)).1.1 == 2
#guard ((trigShape (parseTriGLenient trigMixed)).1.2.map Prod.snd) == [2]
#guard positionsAgree trigMixed (parseTriGLenient trigMixed).2
-- No errors: the strict dataset and no diagnostics.
private def trigGood : String :=
  "@prefix ex: <http://example.org/> .\nex:g { ex:a ex:p ex:o . ex:b ex:p ex:o }\n{ ex:c ex:p ex:o }\nex:d ex:p ex:o .\n"
#guard (match parseTriG trigGood with
        | .ok ds => trigShape (parseTriGLenient trigGood) == trigShape (ds, [])
        | .error _ => false)
-- An unterminated block: one diagnostic, the block's good triple kept.
#guard (trigShape (parseTriGLenient "<http://g/> { <http://x/s> <http://x/p> <http://x/o> .\n")).2
        == [(2, .unclosedGroup)]
#guard (parseTriGLenient "<http://g/> { <http://x/s> <http://x/p> <http://x/o> .\n").1.named.length == 1
-- A directive inside a block.
#guard (trigShape (parseTriGLenient "<http://g/> {\n@prefix ex: <http://e/> .\n<http://x/s> <http://x/p> <http://x/o> . }\n")).2
        == [(2, .badDirective)]
#guard (parseTriGLenient "<http://g/> {\n@prefix ex: <http://e/> .\n<http://x/s> <http://x/p> <http://x/o> . }\n").1.named.length == 1
-- maxErrors inside a block stops the whole walk.
#guard (trigShape (parseTriGLenient trigMixed none .rdf11 { maxErrors := some 0 })).2
        == [(4, .tooManyErrors)]

end L4Factoidal.Syntax
