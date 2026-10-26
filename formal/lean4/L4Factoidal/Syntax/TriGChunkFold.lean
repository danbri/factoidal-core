/-
L4Factoidal.Syntax.TriGChunkFold — TriG read over decoded input chunks,
one lexical unit at a time (https://github.com/danbri/factoidal/issues/769).

`parseTriG` takes the whole document as a `String` and starts with
`text.toList`. The shard packer therefore read the whole TriG source and held
about twenty-four bytes of character list per source byte. This module gives
TriG the walk that `Syntax.TurtleChunkFold` gives Turtle.

The scanner is `TurtleStatementScan`'s, with two additions that TriG needs.
In the normal lexical mode (outside IRIREFs, comments and strings) a `{` at
block depth 0 ends the block HEADER (`label`, `GRAPH label`, or nothing) and
opens a block; a `}` at depth 1 ends the last statement of the block, which
may have no dot, and closes it. Inside a block the scanner offers dot
candidates exactly as for Turtle.

RDF 1.2 TriG has a second use of the two braces: an annotation block
`{| ... |}` after an object (RDF 1.2 TriG, section 3). It belongs to its
statement, so it must not open or close a graph block. The scanner holds back a
`{` read at depth 0 until the next character: `{|` is part of the statement, and
any other `{` opens a graph block. Inside a graph block a `{` is part of the
statement. A `}` read right after a `|` closes an annotation, and not the graph
block (`|` occurs nowhere else in the TriG grammar outside IRIREFs, strings and
comments, where the scanner is not in the normal mode). At the end of the input a
held `{` opens a graph block (`closeInput`). Without these rules every TriG 1.2
document with an annotation block was cut at the wrong brace
(https://github.com/danbri/factoidal/issues/837, item 5).

A block of a named graph is handed to the step once with no triple when it
opens (`step acc (some g) []`), so a consumer sees the graph of an empty block
(`<g> { }`; RDF 1.1 Concepts section 4: a named graph can be empty). A consumer
that folds the triples (`ts.foldl`) sees nothing new.

Every candidate is read by the landed grammar functions, not by new ones:
a top-level candidate by `readTriGStatement`; a header by `readLabelOrSubject`
after the directives `readTriGStatement` also accepts; a statement inside a
block by `readStatement`, with the same two refusals as `readGraphBody`
(directive, nested `GRAPH`). Blank-node state, prefixes and base are one
`TurtleState` threaded through all of them in source order, so the triples
and their graph labels are those of `parseTriG`.

Not proved: that the walk returns `parseTriG`'s dataset whenever it succeeds
(the same open half as `parseTurtleText`). Stand-ins are `#guard`s at the end
of this file and the byte comparisons recorded in
`docs/designissues/2026-09-03-rdf-parsing-strategy.md`.

Differences from `parseTriG` on REJECTED input only: an error carries the
position within its candidate, and a stray `}` or a no-progress statement is
an error here where `parseTriG` stops reading and accepts the prefix.
-/
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.TurtleStatementScan

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-- One lexical unit of a TriG document. -/
inductive TriGEvent where
  /-- A candidate ended by a dot (or a no-dot directive line), outside a
      block or inside one. -/
  | stmt (text : String)
  /-- The text before a `{` that opened a block. -/
  | blockOpen (header : String)
  /-- The text before the `}` that closed a block (a final statement with no
      dot, or only whitespace). -/
  | blockClose (rest : String)

/-- The Turtle statement scanner plus the block depth. -/
structure TriGScan where
  inner : StatementScan := {}
  inBlock : Bool := false
  /-- The last character was a `\\` in the normal mode: a local-name escape
      (`ex:a\\'b`), whose next character is part of the name and opens no
      string, comment, IRIREF or block. -/
  escaped : Bool := false
  /-- A `{` read outside a block, in the normal mode, is held back until the next
      character: `{|` opens an annotation block of RDF 1.2 (`:s :p :o {| :q :r |}`,
      RDF 1.2 TriG section 3), which belongs to the statement; any other `{` opens
      a graph block. Only a `{` outside a block is held, so a held `{` and
      `inBlock` are never both set. -/
  heldOpen : Bool := false
  /-- The last character was a `|` in the normal mode: a `}` right after it closes an
      annotation block (`|}`) and not the graph block. `|` occurs nowhere else in the
      TriG grammar outside IRIREFs, strings and comments. -/
  afterBar : Bool := false
  /-- Completed units, newest first. -/
  eventsRev : List TriGEvent := []

/-- Move the inner scanner's completed candidates into the event list. -/
def TriGScan.flushInner (s : TriGScan) : TriGScan :=
  { s with
    inner := { s.inner with completedRev := [] }
    eventsRev := s.inner.completedRev.map TriGEvent.stmt ++ s.eventsRev }

/-- The held `{` opens a graph block: the text before it is the header. -/
def TriGScan.openHeld (s : TriGScan) : TriGScan :=
  let flushed := s.flushInner
  let text := String.ofList flushed.inner.currentRev.reverse
  { inner := {}
    inBlock := true
    escaped := false
    heldOpen := false
    afterBar := false
    eventsRev := TriGEvent.blockOpen text :: flushed.eventsRev }

/-- The character belongs to the statement text and ends no unit. -/
def TriGScan.plainChar (s : TriGScan) (c : Char) : TriGScan :=
  { s with
    inner := s.inner.feedChar c
    escaped := s.inner.mode == ScanMode.normal && c == '\\'
    afterBar := s.inner.mode == ScanMode.normal && c == '|' }

/-- One character when no `{` is held back. -/
def TriGScan.stepChar (s : TriGScan) (c : Char) : TriGScan :=
  if s.escaped then
    let next := s.inner.feedChar c
    { s with inner := { next with mode := ScanMode.normal, pendingDot := false }, escaped := false,
             afterBar := false }
  else if s.inner.mode == ScanMode.normal && c == '{' && !s.inBlock then
    { s with heldOpen := true, afterBar := false }
  else if s.inner.mode == ScanMode.normal && c == '}' && s.inBlock && !s.afterBar then
    let flushed := s.flushInner
    let text := String.ofList flushed.inner.currentRev.reverse
    { inner := {}
      inBlock := false
      escaped := false
      heldOpen := false
      afterBar := false
      eventsRev := TriGEvent.blockClose text :: flushed.eventsRev }
  else s.plainChar c

/-- The scanner when nothing follows the held `{`: it opens a graph block. -/
def TriGScan.closeInput (s : TriGScan) : TriGScan :=
  if s.heldOpen then s.openHeld else s

/-- One character. A held `{` is an annotation opening when `|` follows (both
    characters belong to the statement) and a graph block opening otherwise. -/
def TriGScan.feedChar (s : TriGScan) (c : Char) : TriGScan :=
  if s.heldOpen && c == '|' then { (s.plainChar '{').plainChar '|' with heldOpen := false }
  else s.closeInput.stepChar c

def TriGScan.feedChars (s : TriGScan) : List Char → TriGScan
  | [] => s
  | c :: cs => TriGScan.feedChars (s.feedChar c) cs

/-- Feed a decoded string chunk. -/
def TriGScan.feed (s : TriGScan) (chunk : String) : TriGScan := s.feedChars chunk.toList

/-- The completed units in source order, and the scanner with them cleared. -/
def TriGScan.drain (s : TriGScan) : List TriGEvent × TriGScan :=
  let flushed := s.flushInner
  (flushed.eventsRev.reverse, { flushed with eventsRev := [] })

/-- The uncommitted text after the last unit. -/
def TriGScan.remainder (s : TriGScan) : String := s.inner.remainder

/-- State of a TriG chunk fold. `block` is `none` outside a graph block and
    `some g` inside the block of graph `g` (`g = none` is the default graph). -/
structure TriGChunkFoldState (α : Type) where
  turtle : TurtleState
  acc : α
  pos : Nat := 0
  block : Option (Option Subject) := none
  scanner : TriGScan := {}

/-- Top-level statements of `chars`, each read by `readTriGStatement`. -/
def consumeTop (step : α → Option Subject → List Triple → α) :
    Nat → TurtleState → α → Nat → List Char → Except ParseError (TurtleState × α × Nat)
  | 0, _st, _acc, pos, _ => .error ⟨"TriG statement fuel exhausted", pos⟩
  | fuel + 1, st, acc, pos, chars =>
      let (p1, r1) := tws pos chars
      match r1 with
      | [] => .ok (st, acc, p1)
      | _ =>
          match readTriGStatement (r1.length + 2) st p1 r1 with
          | .error e => .error e
          | .ok ((g, ts), st', p2, r2) =>
              if p2 ≤ p1 then .error ⟨"TriG statement made no progress", p1⟩
              else consumeTop step fuel st' (step acc g ts) p2 r2

/-- Statements inside the block of graph `g`: the loop of `readGraphBody`. -/
def consumeBlock (step : α → Option Subject → List Triple → α) (g : Option Subject) :
    Nat → TurtleState → α → Nat → List Char → Except ParseError (TurtleState × α × Nat)
  | 0, _st, _acc, pos, _ => .error ⟨"TriG statement fuel exhausted", pos⟩
  | fuel + 1, st, acc, pos, chars =>
      let (p1, r1) := tws pos chars
      match r1 with
      | [] => .ok (st, acc, p1)
      | '}' :: _ => .ok (st, acc, p1)
      | _ =>
          if isDirectiveAt r1 then
            .error ⟨"directives are not allowed inside a graph block", p1⟩
          else if isGraphKeyword r1 then
            .error ⟨"nested GRAPH is not allowed inside a graph block", p1⟩
          else
            match readStatement (r1.length + 2) st p1 r1 with
            | .error e => .error e
            | .ok (ts, st', p2, r2) =>
                if p2 ≤ p1 then .error ⟨"TriG statement made no progress", p1⟩
                else consumeBlock step g fuel st' (step acc g ts) p2 r2

/-- The text before a `{`: any directives, then the graph label (with or
    without `GRAPH`), or nothing for a block of the default graph. The
    directives are those `readTriGStatement` reads one by one. -/
def readBlockHeader : Nat → TurtleState → Nat → List Char →
    Except ParseError (Option Subject × TurtleState)
  | 0, _st, pos, _ => .error ⟨"TriG header fuel exhausted", pos⟩
  | fuel + 1, st, pos, cs =>
      let (p1, r1) := tws pos cs
      match r1 with
      | [] => .ok (none, st)
      | _ =>
        match readPrefixDirective st p1 r1 with
        | .ok ((pfx, iri), p2, r2) =>
            readBlockHeader fuel (st.bindPrefix pfx iri) p2 r2
        | .error _ =>
          match readBaseDirective st p1 r1 with
          | .ok (b, p2, r2) => readBlockHeader fuel { st with baseIri := b } p2 r2
          | .error _ =>
            match (if st.mode == .rdf12 then readVersionDirective p1 r1
                   else .error ⟨"not RDF 1.2", p1⟩) with
            | .ok (p2, r2) => readBlockHeader fuel st p2 r2
            | .error _ =>
              let keyword := isGraphKeyword r1
              let (p2, r2) := if keyword then tws (p1 + 5) (r1.drop 5) else (p1, r1)
              match readLabelOrSubject st p2 r2 with
              | .error e =>
                  .error (if keyword then ⟨"expected a graph name after GRAPH", p2⟩ else e)
              | .ok (g, st2, p3, r3) =>
                  let (p4, r4) := tws p3 r3
                  match r4 with
                  | [] => .ok (some g, st2)
                  | _ => .error ⟨"expected '{' after graph name", p4⟩

def applyEvent (step : α → Option Subject → List Triple → α)
    (state : TriGChunkFoldState α) : TriGEvent → Except ParseError (TriGChunkFoldState α)
  | .stmt text =>
      let cs := text.toList
      match state.block with
      | none =>
          match consumeTop step (cs.length + 2) state.turtle state.acc state.pos cs with
          | .error e => .error e
          | .ok (turtle, acc, pos) => .ok { state with turtle, acc, pos }
      | some g =>
          match consumeBlock step g (cs.length + 2) state.turtle state.acc state.pos cs with
          | .error e => .error e
          | .ok (turtle, acc, pos) => .ok { state with turtle, acc, pos }
  | .blockOpen header =>
      let cs := header.toList
      match readBlockHeader (cs.length + 2) state.turtle state.pos cs with
      | .error e => .error e
      | .ok (g, turtle) =>
          -- a block of a named graph declares the graph, also when it holds no triple
          -- (`<g> { }`): the step gets the graph with no triple (`Source.trigStep`)
          let acc := match g with
            | some _ => step state.acc g []
            | none => state.acc
          .ok { state with turtle, acc, block := some g }
  | .blockClose rest =>
      match state.block with
      | none => .error ⟨"unexpected '}' outside a graph block", state.pos⟩
      | some g =>
          let cs := (rest ++ "}").toList
          match consumeBlock step g (cs.length + 2) state.turtle state.acc state.pos cs with
          | .error e => .error e
          | .ok (turtle, acc, pos) => .ok { state with turtle, acc, pos, block := none }

def applyEvents (step : α → Option Subject → List Triple → α) :
    TriGChunkFoldState α → List TriGEvent → Except ParseError (TriGChunkFoldState α)
  | state, [] => .ok state
  | state, ev :: evs =>
      match applyEvent step state ev with
      | .error e => .error e
      | .ok next => applyEvents step next evs

/-- Begin a chunk fold after a pre-pass has supplied the generated blank-node
    prefix. -/
def TriGChunkFoldState.init (bnodePrefix : String) (acc : α)
    (base : Option String := none) (mode : Mode := .rdf11) : TriGChunkFoldState α :=
  { turtle := TurtleState.initWithBnodePrefix bnodePrefix base mode, acc }

/-- Feed one decoded UTF-8 chunk; every unit it completes is read at once. -/
def TriGChunkFoldState.feed (step : α → Option Subject → List Triple → α)
    (state : TriGChunkFoldState α) (chunk : String) :
    Except ParseError (TriGChunkFoldState α) :=
  let (events, scanner) := (state.scanner.feed chunk).drain
  applyEvents step { state with scanner } events

/-- End of input: the units still pending, then the unfinished suffix as a
    top-level statement (a final dot with no whitespace after it, or a
    SPARQL-style directive). An open block is an error. -/
def TriGChunkFoldState.finish (step : α → Option Subject → List Triple → α)
    (state : TriGChunkFoldState α) : Except ParseError α :=
  let (events, scanner) := state.scanner.closeInput.drain
  match applyEvents step { state with scanner } events with
  | .error e => .error e
  | .ok s =>
      match s.block with
      | some _ => .error ⟨"unterminated graph block (expected '}')", s.pos⟩
      | none =>
          let cs := s.scanner.remainder.toList
          match consumeTop step (cs.length + 2) s.turtle s.acc s.pos cs with
          | .error e => .error e
          | .ok (_, acc, _) => .ok acc

/-! ## Starting and ending inside a document

A reader of one byte range of a TriG document starts at a dot boundary at the
top level or inside a graph block (`SplitScan.Split`), and can end inside a
graph block (https://github.com/danbri/factoidal/issues/842). -/

/-- Read `prelude` for its directives only (a step that keeps nothing, so no
    triple and no declaration reaches the accumulator), then start the
    scanner and the position again. With `header`, the reader starts inside
    the graph block that the header names (`readBlockHeader`); the header has
    no `[` and no directive (`SplitScan`), so it changes no state. -/
def TriGChunkFoldState.resume (state : TriGChunkFoldState α) (prelude : String)
    (header : Option String) (counter : Option Nat := none) : Except ParseError (TriGChunkFoldState α) :=
  let keep : α → Option Subject → List Triple → α := fun a _ _ => a
  match state.feed keep prelude with
  | .error e => .error e
  | .ok st =>
    let (events, scanner) := st.scanner.closeInput.drain
    match applyEvents keep { st with scanner } events with
    | .error e => .error e
    | .ok s =>
      match s.block with
      | some _ => .error ⟨"a directive unit left a graph block open", s.pos⟩
      | none =>
        let cs := s.scanner.remainder.toList
        match consumeTop keep (cs.length + 2) s.turtle s.acc s.pos cs with
        | .error e => .error e
        | .ok (turtle, acc, _) =>
          let turtle := match counter with
            | some c => { turtle with bnodeCounter := c }
            | none => turtle
          match header with
          | none => .ok { turtle, acc, pos := 0, block := none, scanner := {} }
          | some h =>
            let hs := h.toList
            match readBlockHeader (hs.length + 2) turtle 0 hs with
            | .error e => .error e
            | .ok (g, turtle) =>
              .ok { turtle, acc, pos := 0, block := some g, scanner := { inBlock := true } }

/-- `finish` for a range that may end inside a graph block: the rest of the
    text is read as statements of that block. Also gives the generated
    blank-node counter at the end, which the reader of a range checks against
    the count of `SplitScan` at the next split. -/
def TriGChunkFoldState.finishOpenCount (step : α → Option Subject → List Triple → α)
    (state : TriGChunkFoldState α) : Except ParseError (α × Nat) :=
  let (events, scanner) := state.scanner.closeInput.drain
  match applyEvents step { state with scanner } events with
  | .error e => .error e
  | .ok s =>
      let cs := s.scanner.remainder.toList
      match s.block with
      | some g =>
          match consumeBlock step g (cs.length + 2) s.turtle s.acc s.pos cs with
          | .error e => .error e
          | .ok (turtle, acc, _) => .ok (acc, turtle.bnodeCounter)
      | none =>
          match consumeTop step (cs.length + 2) s.turtle s.acc s.pos cs with
          | .error e => .error e
          | .ok (turtle, acc, _) => .ok (acc, turtle.bnodeCounter)

/-- `finishOpenCount` without the counter. -/
def TriGChunkFoldState.finishOpen (step : α → Option Subject → List Triple → α)
    (state : TriGChunkFoldState α) : Except ParseError α :=
  (state.finishOpenCount step).map (·.1)

/-- Fold complete decoded chunks into a dataset in source order, as the
    packer does: the accumulator is the dataset's quads, newest first. -/
def parseTriGChunksQuads (bnodePrefix : String) (chunks : List String)
    (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError (List (Triple × Option Subject)) :=
  let step := fun (acc : List (Triple × Option Subject)) (g : Option Subject)
      (ts : List Triple) => ts.foldl (fun a t => (t, g) :: a) acc
  let initial : Except ParseError (TriGChunkFoldState (List (Triple × Option Subject))) :=
    .ok (TriGChunkFoldState.init bnodePrefix [] base mode)
  match chunks.foldl (fun r chunk => match r with
      | .error e => .error e
      | .ok st => st.feed step chunk) initial with
  | .error e => .error e
  | .ok st => (st.finish step).map List.reverse

/-! ## Build-time checks against `parseTriG`

Each document is cut at every character position; the walk must accept it and
count as many quads as `parseTriG`, and refuse what `parseTriG` refuses. This
is a check, not a proof (https://github.com/danbri/factoidal/issues/836). -/

private def walkDocs : List String :=
  [ "<http://e/a> <http://e/p> <http://e/b> .",
    "{ <http://e/a> <http://e/p> <http://e/b> . <http://e/a> <http://e/p> <http://e/c> }",
    "<http://e/g> { <http://e/a> <http://e/p> <http://e/b> . <http://e/c> <http://e/p> <http://e/d> . }",
    "GRAPH <http://e/g> { <http://e/a> <http://e/p> <http://e/b> }",
    "@prefix e: <http://e/> . e:g { e:a e:p e:b ; e:q \"x\"@en , \"y\" . } e:h { e:c e:p e:d }",
    "@prefix e: <http://e/> . _:g { e:a e:p e:b } [] { e:a e:p e:c } e:a e:p e:b .",
    "@prefix e: <http://e/> . e:a e:p [ e:q e:r ] . e:g { e:b e:p ( 1 2 3 ) }",
    "BASE <http://e/> PREFIX e: <http://e/> GRAPH e:g { <a> e:p <b> }",
    "@prefix e: <http://e/> . e:g { e:a e:p \"a}b{c.\" . # { } .\n e:b e:p e:c }",
    "@prefix e: <http://e/> . e:g { e:a e:p e:a\\'b . }",
    "{ }", "<http://e/g> { }",
    "@prefix e: <http://e/> . e:g { @prefix f: <http://f/> . }",
    "@prefix e: <http://e/> . e:g { GRAPH e:h { e:a e:p e:b } }",
    "@prefix e: <http://e/> . e:g { e:a e:p e:b",
    "@prefix e: <http://e/> . GRAPH { e:a e:p e:b }" ]

private def quadCount (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (fun ng => ng.graph.length)).foldl (· + ·) 0

private def walkCount (d : String) (cut : Nat) : Option Nat :=
  let cs := d.toList
  let a := String.ofList (cs.take cut)
  let b := String.ofList (cs.drop cut)
  match parseTriGChunksQuads "anon__" [a, b] none .rdf11 with
  | .ok qs => some qs.length
  | .error _ => none

private def walkAgrees (d : String) : Bool :=
  let want := (parseTriG d none .rdf11).toOption.map quadCount
  (List.range (d.length + 1)).all (fun cut => walkCount d cut == want)

#guard walkDocs.all walkAgrees
#guard (walkDocs.filter (fun d => (parseTriG d none .rdf11).toOption.isSome)).length ≥ 8
#guard (walkDocs.filter (fun d => (parseTriG d none .rdf11).toOption.isNone)).length ≥ 4

/-! RDF 1.2: annotation blocks, in and out of a graph block, with a reifier, with a
`|}` inside a string, nested, and with no space after `{|`. -/

private def walkDocs12 : List String :=
  [ "<http://e/a> <http://e/p> <http://e/b> {| <http://e/q> <http://e/r> |} .",
    "<http://e/g> { <http://e/a> <http://e/p> <http://e/b> {| <http://e/q> <http://e/r> |} . }",
    "<http://e/g> { <http://e/a> <http://e/p> <http://e/b> {| <http://e/q> <http://e/r> |} }",
    "GRAPH <http://e/g> { <http://e/a> <http://e/p> <http://e/b> ~ <http://e/t> {| <http://e/q> <http://e/r> |} . }",
    "<http://e/a> <http://e/p> <http://e/b> {|<http://e/q> <http://e/r>|} .",
    "<http://e/a> <http://e/p> <http://e/b> {| <http://e/q> <http://e/r> ; <http://e/s> \"|}\" |} .",
    "{ <http://e/a> <http://e/p> <http://e/b> {| <http://e/q> <http://e/r> |} }",
    "<http://e/a> <http://e/p> <http://e/b> {| <http://e/q> <http://e/r> {| <http://e/s> <http://e/t> |} |} .",
    "<http://e/a> <http://e/p> <http://e/b> {| <http://e/q> <http://e/r> |} . <http://e/g> { <http://e/c> <http://e/p> <http://e/d> }" ]

private def walkCount12 (d : String) (cut : Nat) : Option Nat :=
  let cs := d.toList
  let a := String.ofList (cs.take cut)
  let b := String.ofList (cs.drop cut)
  match parseTriGChunksQuads "anon__" [a, b] none .rdf12 with
  | .ok qs => some qs.length
  | .error _ => none

private def walkAgrees12 (d : String) : Bool :=
  let want := (parseTriG d none .rdf12).toOption.map quadCount
  want.isSome && (List.range (d.length + 1)).all (fun cut => walkCount12 d cut == want)

#guard walkDocs12.all walkAgrees12

/-! The graph names a walk sees, at every cut, are the named graphs of `parseTriG`,
in the same order: an empty graph block declares its graph (RDF 1.1 Concepts
section 4; https://github.com/danbri/factoidal/issues/855). -/

private def walkNames (d : String) (cut : Nat) : Option (List Subject) :=
  let cs := d.toList
  let step := fun (acc : List Subject) (g : Option Subject) (_ : List Triple) =>
    match g with
    | some n => if acc.contains n then acc else n :: acc
    | none => acc
  let chunks := [String.ofList (cs.take cut), String.ofList (cs.drop cut)]
  let initial : Except ParseError (TriGChunkFoldState (List Subject)) :=
    .ok (TriGChunkFoldState.init (freshBnodePrefix d) [] none .rdf11)
  match chunks.foldl (fun r chunk => match r with
      | .error e => .error e
      | .ok st => st.feed step chunk) initial with
  | .error _ => none
  | .ok st => (st.finish step).toOption.map List.reverse

private def namesAgree (d : String) : Bool :=
  let want := (parseTriG d none .rdf11).toOption.map fun ds => ds.named.map (·.name)
  want.isSome && (List.range (d.length + 1)).all (fun cut => walkNames d cut == want)

private def emptyBlockDocs : List String :=
  [ "<http://e/g> { }",
    "{ } <http://e/g> { } GRAPH _:b { <http://e/a> <http://e/p> <http://e/b> }",
    "@prefix e: <http://e/> . e:g { } e:h { e:a e:p e:b } e:g { e:c e:p e:d } GRAPH e:k { }",
    "@prefix e: <http://e/> . [] { } e:a e:p e:b ." ]

#guard emptyBlockDocs.all namesAgree
-- an empty block is a named graph with no triple in the dataset
#guard (parseTriG "<http://e/g> { }" none .rdf11).toOption.map (fun ds => (ds.named.length, quadCount ds)) == some (1, 0)
#guard (parseTriG "{ }" none .rdf11).toOption.map (fun ds => ds.named.length) == some 0

end L4Factoidal.Syntax
