/-
L4Factoidal.Syntax.TurtleChunkFold — grammar-validated Turtle event folding
over decoded input chunks.

`TurtleStatementScan` supplies only lexical candidate boundaries. Every
candidate is then parsed by the landed `readStatement` implementation, so
prefix/base state, RDF version and generated blank-node state stay identical
to the ordinary Turtle parser. The caller supplies the already-established
collision-free blank-node prefix; a file loader obtains it during its bounded
pre-pass.
-/
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TurtleStatementScan

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-- State retained by a decoded-chunk Turtle fold. Completed statements are
    folded immediately; `scanner` holds only the current unfinished lexical
    segment. -/
structure TurtleChunkFoldState (α : Type) where
  turtle : TurtleState
  acc : α
  pos : Nat := 0
  scanner : StatementScan := StatementScan.init

private def consumeText (step : α → List RDF.Triple → α) :
    Nat → TurtleState → α → Nat → List Char → Except ParseError (TurtleState × α × Nat)
  | 0, _turtle, _acc, pos, _ => .error ⟨"Turtle statement fuel exhausted", pos⟩
  | fuel + 1, turtle, acc, pos, chars =>
      let (p1, r1) := tws pos chars
      match r1 with
      | [] => .ok (turtle, acc, p1)
      | _ =>
          match readStatement (r1.length + 2) turtle p1 r1 with
          | .error error => .error error
          | .ok (triples, nextTurtle, p2, r2) =>
              if p2 ≤ p1 then .error ⟨"Turtle statement made no progress", p1⟩
              else consumeText step fuel nextTurtle (step acc triples) p2 r2

private def consumeCandidates (step : α → List RDF.Triple → α) :
    TurtleState → α → Nat → List String → Except ParseError (TurtleState × α × Nat)
  | turtle, acc, pos, [] => .ok (turtle, acc, pos)
  | turtle, acc, pos, text :: texts =>
      match consumeText step (text.toList.length + 2) turtle acc pos text.toList with
      | .error error => .error error
      | .ok (nextTurtle, nextAcc, nextPos) =>
          consumeCandidates step nextTurtle nextAcc nextPos texts

/-- Begin a chunk fold after a pre-pass has supplied the generated blank-node
    prefix. -/
def TurtleChunkFoldState.init (bnodePrefix : String) (_step : α → List RDF.Triple → α) (acc : α)
    (base : Option String := none) (mode : Mode := .rdf11) : TurtleChunkFoldState α :=
  { turtle := TurtleState.initWithBnodePrefix bnodePrefix base mode, acc }

/-- Feed one decoded UTF-8 chunk. Candidates are drained and grammar-validated
    immediately rather than retained for the whole document. -/
def TurtleChunkFoldState.feed (step : α → List RDF.Triple → α) (state : TurtleChunkFoldState α)
    (chunk : String) : Except ParseError (TurtleChunkFoldState α) :=
  let scanned := state.scanner.feed chunk
  let (candidates, scanner) := scanned.drain
  match consumeCandidates step state.turtle state.acc state.pos candidates with
  | .error error => .error error
  | .ok (turtle, acc, pos) => .ok { turtle, acc, pos, scanner }

/-- Finish a chunk fold. The final suffix is submitted to the same grammar
    path, covering a terminal dot with no trailing whitespace and a final
    no-dot SPARQL-style directive. -/
def TurtleChunkFoldState.finish (step : α → List RDF.Triple → α) (state : TurtleChunkFoldState α) :
    Except ParseError α :=
  match consumeText step (state.scanner.remainder.toList.length + 2)
      state.turtle state.acc state.pos state.scanner.remainder.toList with
  | .error error => .error error
  | .ok (_, acc, _) => .ok acc

/-- Fold complete decoded chunks using an externally precomputed blank-node
    prefix. The result is independent of chunk boundaries for valid Turtle
    whose statement candidates the scanner exposes. -/
def parseTurtleChunksFold (bnodePrefix : String) (step : α → List RDF.Triple → α) (init : α)
    (chunks : List String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError α :=
  let initial : Except ParseError (TurtleChunkFoldState α) :=
    .ok (TurtleChunkFoldState.init bnodePrefix step init base mode)
  match chunks.foldl (fun result chunk => do
      let state ← result
      TurtleChunkFoldState.feed step state chunk) initial with
  | .error error => .error error
  | .ok state => state.finish step

/-! ## The whole document as a `String`, one statement candidate at a time

`parseTurtle` turns the whole document into a `List Char` before it reads the
first statement. A cons cell is 24 bytes and one allocation per character, so
the list costs about 34 bytes of resident memory per input byte, and it is the
peak of `l4factoidal query` and `parse` on a Turtle file: 256 MB for 6.76 MB
of `gene.ttl` (https://github.com/danbri/factoidal/issues/729). The F* engine
needs 28 MB for the same query.

`parseTurtleText` reads the characters of the `String` in place
(`String.foldl`), gives them to the statement scanner one at a time, and
hands each completed candidate to `readStatement` as above, so only the
current candidate is a character list. -/

/-- Feed one decoded character, then submit the candidates it completed. -/
def TurtleChunkFoldState.feedChar (step : α → List RDF.Triple → α)
    (state : TurtleChunkFoldState α) (c : Char) : Except ParseError (TurtleChunkFoldState α) :=
  match state with
  | { turtle, acc, pos, scanner } =>
    let scanner := scanner.feedChar c
    match scanner.completedRev with
    | [] => .ok { turtle, acc, pos, scanner }
    | _ =>
      let (candidates, scanner) := scanner.drain
      match consumeCandidates step turtle acc pos candidates with
      | .error error => .error error
      | .ok (turtle, acc, pos) => .ok { turtle, acc, pos, scanner }

/-- The generated blank-node prefix of `text` (`freshBnodePrefix`), read
    without a character list. -/
def freshBnodePrefixText (text : String) : String :=
  freshBnodePrefixOfLongest (text.foldl UnderscoreRun.feedChar {}).longest

theorem UnderscoreRun.feedChars_eq_foldl (s : UnderscoreRun) (cs : List Char) :
    s.feedChars cs = cs.foldl UnderscoreRun.feedChar s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih (s.feedChar c)

theorem freshBnodePrefixText_eq (text : String) :
    freshBnodePrefixText text = freshBnodePrefix text := by
  simp only [freshBnodePrefixText, freshBnodePrefix, maxUnderscoreRun,
    String.foldl_eq_foldl_toList, UnderscoreRun.feedChars_eq_foldl]

/-- Whether `text` contains `<<`, the opening of an RDF 1.2 triple term or
    reified triple. The scanner reads `<` as the start of an IRIREF and ends
    it at the first `>`, so inside `<< ... >>` its lexical mode can differ
    from the grammar's (a `>` inside a string literal of the triple term);
    such a document is read by `parseTurtle`. -/
def hasDoubleLt (text : String) : Bool :=
  text.foldl (fun (st : Nat) c =>
    if st == 2 then 2 else if c == '<' then (if st == 1 then 2 else 1) else 0) 0 == 2

/-- The scanner walk of `parseTurtleText` alone: the characters of `text`
    fed one at a time, each completed candidate read by `readStatement`, the
    triples collected newest first and reversed once. No fallback. -/
def parseTurtleWalk (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError Graph :=
  let init : TurtleChunkFoldState (List RDF.Triple) :=
    TurtleChunkFoldState.init (freshBnodePrefixText text) prependReverse [] base mode
  let walked := text.foldl (fun (r : Except ParseError (TurtleChunkFoldState (List RDF.Triple))) c =>
    match r with
    | .error e => .error e
    | .ok state => state.feedChar prependReverse c) (.ok init)
  match walked with
  | .error e => .error e
  | .ok state =>
    match state.finish prependReverse with
    | .ok accRev => .ok accRev.reverse
    | .error e => .error e

/-- `parseTurtle` without the whole-document character list.

* A document that contains `<<` is read by `parseTurtle` (`hasDoubleLt`).
* Otherwise the scanner and `readStatement` read it one candidate at a time,
  with the generated blank-node prefix of the whole document
  (`freshBnodePrefixText_eq`) and the accumulator of `parseStatements`
  (`prependReverse`, `TurtleTheorems.parseTurtle_eq_fold`).
* When that walk fails, the document is read again by `parseTurtle`, so every
  error, message and offset is the reference parser's.

**Not proved:** that the walk returns `parseTurtle`'s graph whenever it
succeeds (the chunk-boundary half of
`docs/designissues/2026-09-03-rdf-parsing-strategy.md` §2.3). Stand-ins: the
`#guard`s in `TurtleChunkFoldTests.lean` (the walk alone against
`parseTurtle` on 23 documents in both modes; `parseTurtleText` against
`parseTurtle`, errors included, on those and 7 refused documents);
`l4query-phases --walk-check` (the walk alone against `parseTurtle` on every
`.ttl` and `.nt` file of the W3C RDF 1.1 and 1.2 suites: 3,104 of 3,104
accepted cases the same, 2026-10-10); and byte comparison of `l4factoidal`
`parse`, `parse --out nquads` and `query` against the binary before on the
same files (`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`
§10). -/
def parseTurtleText (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError Graph :=
  if hasDoubleLt text then parseTurtle text base mode
  else
    match parseTurtleWalk text base mode with
    | .ok g => .ok g
    | .error _ => parseTurtle text base mode

/-- Every error `parseTurtleText` reports is the one `parseTurtle` reports. -/
theorem parseTurtleText_error {text : String} {base : Option String} {mode : Mode}
    {e : ParseError} (h : parseTurtleText text base mode = .error e) :
    parseTurtle text base mode = .error e := by
  unfold parseTurtleText at h
  split at h
  · exact h
  · split at h
    · cases h
    · exact h

/-- On a document where the walk gives `parseTurtle`'s answer,
    `parseTurtleText` gives it too. -/
theorem parseTurtleText_eq_of_walk {text : String} {base : Option String} {mode : Mode}
    (h : parseTurtleWalk text base mode = parseTurtle text base mode) :
    parseTurtleText text base mode = parseTurtle text base mode := by
  unfold parseTurtleText
  split
  · rfl
  · split
    · rename_i g hg
      rw [← h, hg]
    · rfl

end L4Factoidal.Syntax
