/-
L4Factoidal.Syntax.LenientFeedText — the lenient (recovery) N-Triples and N-Quads walk
over text, for a line longer than one chunk
(https://github.com/danbri/factoidal/issues/949).

`LenientStream` (`Syntax/NQuadsLenient.lean`) holds the partial last line as a
`List Char` and walks each completed buffer as a `List Char`, about 33 bytes of resident
memory per character (design record, section 3b.9). `LenientStreamT` below keeps the
partial line as a `String` and walks a buffer that completes a partial line at a cursor
(`String.Pos`), with the native statement readers of `Syntax/StrictFeedText.lean`.

* `advanceS_eq`: the line state at a cursor is `LinePos.advance` over `rest p`.
* `foldLinesLenientS_eq`: the walk at a cursor is `foldLinesLenient` over `rest p`. A
  round whose statement the native reader declines (an error, an escape inside an
  IRIREF) runs `foldLinesLenient` from the start of that round on `rest p`.
* `LenientStreamT.feed_eq`, `LenientStreamT.finish_eq`: one chunk and the end of input
  equal `LenientStream.feed` and `LenientStream.finish` on the characters, through
  `toLS` and `ofLS`, so `LenientStream.feed_eq_feedSpec` and the theorems of
  `NQuadsLenientTheorems` apply.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.StrictFeedText
import L4Factoidal.Syntax.NQuadsLenient

namespace L4Factoidal.Syntax.LenientFeedText

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Syntax.NQuadsStreaming
open L4Factoidal.Syntax.StrictFeed
open L4Factoidal.Syntax.StrictFeedText

/-! ## The line state at a cursor -/

/-- `LinePos.advance` over the next `n` characters from `p`. -/
def advanceS {s : String} : LinePos → Nat → Nat → s.Pos → LinePos
  | lp, _, 0, _ => lp
  | lp, off, n + 1, p =>
    if h : p = s.endPos then lp
    else
      advanceS (if p.get h == '\n' then { line := lp.line + 1, lineStart := off + 1 } else lp)
        (off + 1) n (p.next h)

theorem advanceS_eq {s : String} :
    ∀ (lp : LinePos) (off n : Nat) (p : s.Pos), advanceS lp off n p = lp.advance off n (rest p)
  | lp, off, 0, p => by simp [advanceS, LinePos.advance]
  | lp, off, n + 1, p => by
    by_cases h : p = s.endPos
    · rw [advanceS, dif_pos h, rest_eq_nil p h]; simp [LinePos.advance]
    · rw [advanceS, dif_neg h, rest_next p h, advanceS_eq]
      simp [LinePos.advance]

/-! ## The lenient walk at a cursor -/

/-- `foldLinesLenient` at a cursor, with the native statement reader of `quads` and `mode`.
A round whose statement the native reader declines runs `foldLinesLenient` from the start
of that round on `rest p`. -/
def foldLinesLenientS {s : String} (quads : Bool) (mode : Mode) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) :
    Nat → Nat → s.Pos → LenientRun α β → LenientRun α β
  | 0, pos, p, run =>
      { (run.recordError opts report pos (rest p)
          ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩).1 with
        stopped := true }
  | fuel' + 1, pos, p, run =>
      match skipWsS pos p with
      | (pos1, p1) =>
        if h : p1 = s.endPos then run
        else if p1.get h = '#' then
          match skipCommentS pos1 p1 with
          | (pos2, p2) =>
            match skipEolS pos2 p2 with
            | (pos3, p3) =>
              foldLinesLenientS quads mode consume report opts fuel' pos3 p3
                { run with linePos := advanceS run.linePos pos2 (pos3 - pos2) p2 }
        else if p1.get h = '\n' then
          match skipEolS pos1 p1 with
          | (pos2, p2) =>
            foldLinesLenientS quads mode consume report opts fuel' pos2 p2
              { run with linePos := advanceS run.linePos pos1 (pos2 - pos1) p1 }
        else if p1.get h = '\r' then
          match skipEolS pos1 p1 with
          | (pos2, p2) =>
            foldLinesLenientS quads mode consume report opts fuel' pos2 p2
              { run with linePos := advanceS run.linePos pos1 (pos2 - pos1) p1 }
        else
          match stmtS quads mode pos1 p1 with
          | none =>
            foldLinesLenient (modeReader quads mode) consume report opts (fuel' + 1) pos (rest p) run
          | some (t, gopt, pos2, p2) =>
            match skipWsS pos2 p2 with
            | (pos3, p3) =>
              match skipCommentS pos3 p3 with
              | (pos4, p4) =>
                match skipEolS pos4 p4 with
                | (pos5, p5) =>
                  foldLinesLenientS quads mode consume report opts fuel' pos5 p5
                    { run with acc := consume run.acc t gopt,
                               linePos := advanceS run.linePos pos4 (pos5 - pos4) p4 }

theorem foldLinesLenientS_eq {s : String} (quads : Bool) (mode : Mode) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) :
    ∀ (fuel pos : Nat) (p : s.Pos) (run : LenientRun α β),
      foldLinesLenientS quads mode consume report opts fuel pos p run =
        foldLinesLenient (modeReader quads mode) consume report opts fuel pos (rest p) run := by
  intro fuel
  induction fuel with
  | zero => intro pos p run; rfl
  | succ n ih =>
    intro pos p run
    have e1 := skipWsS_eq pos p
    rcases hw : skipWsS pos p with ⟨pos1, p1⟩
    rw [hw] at e1
    simp only [] at e1
    simp only [foldLinesLenientS, hw]
    rw [foldLinesLenient, ← e1]
    simp only []
    by_cases h : p1 = s.endPos
    · rw [dif_pos h, rest_eq_nil p1 h]
    rw [dif_neg h]
    have hr := rest_next p1 h
    by_cases h1 : p1.get h = '#'
    · rw [if_pos h1]
      have e2 := skipCommentS_eq pos1 p1
      rcases hc : skipCommentS pos1 p1 with ⟨pos2, p2⟩
      rw [hc] at e2
      simp only [] at e2 ⊢
      have e3 := skipEolS_eq pos2 p2
      rcases he : skipEolS pos2 p2 with ⟨pos3, p3⟩
      rw [he] at e3
      simp only [] at e3 ⊢
      rw [ih, advanceS_eq]
      rw [hr, h1] at e2 ⊢
      rw [← e2]
      simp only []
      rw [← e3]
    rw [if_neg h1]
    by_cases h2 : p1.get h = '\n'
    · rw [if_pos h2]
      have e3 := skipEolS_eq pos1 p1
      rcases he : skipEolS pos1 p1 with ⟨pos3, p3⟩
      rw [he] at e3
      simp only [] at e3 ⊢
      rw [ih, advanceS_eq]
      rw [hr, h2] at e3 ⊢
      rw [← e3]
      rfl
    rw [if_neg h2]
    by_cases h3 : p1.get h = '\r'
    · rw [if_pos h3]
      have e3 := skipEolS_eq pos1 p1
      rcases he : skipEolS pos1 p1 with ⟨pos3, p3⟩
      rw [he] at e3
      simp only [] at e3 ⊢
      rw [ih, advanceS_eq]
      rw [hr, h3] at e3 ⊢
      rw [← e3]
      rfl
    rw [if_neg h3]
    rcases hs : stmtS quads mode pos1 p1 with _ | ⟨t, gopt, pos2, p2⟩
    · simp only []
    · simp only []
      have hsound := stmtS_sound _ _ _ _ _ _ _ _ hs
      have e5 := skipWsS_eq pos2 p2
      rcases hw2 : skipWsS pos2 p2 with ⟨pos3, p3⟩
      rw [hw2] at e5
      simp only [] at e5 ⊢
      have e6 := skipCommentS_eq pos3 p3
      rcases hc : skipCommentS pos3 p3 with ⟨pos4, p4⟩
      rw [hc] at e6
      simp only [] at e6 ⊢
      have e7 := skipEolS_eq pos4 p4
      rcases he : skipEolS pos4 p4 with ⟨pos5, p5⟩
      rw [he] at e7
      simp only [] at e7 ⊢
      rw [ih, advanceS_eq]
      rw [hr] at hsound ⊢
      split
      · simp_all
      · simp_all
      · simp_all
      · simp_all
      · rw [hsound]
        simp only []
        rw [← e5]
        simp only []
        rw [← e6]
        simp only []
        rw [← e7]

/-! ## The chunked lenient walk over text -/

/-- A chunked lenient walk with the partial last line as text (it holds no line break), and
the absolute offset in characters of its first character. -/
structure LenientStreamT (α β : Type) where
  run : LenientRun α β
  carryText : String := ""
  pos : Nat := 0

/-- The `LenientStream` state with the same partial line. -/
def LenientStreamT.toLS {α β : Type} (st : LenientStreamT α β) : LenientStream α β :=
  { run := st.run, carryRev := st.carryText.toList.reverse, pos := st.pos }

/-- The `LenientStreamT` state with the same partial line. -/
def LenientStreamT.ofLS {α β : Type} (st : LenientStream α β) : LenientStreamT α β :=
  { run := st.run, carryText := String.ofList st.carryRev.reverse, pos := st.pos }

theorem LenientStreamT.ofLS_toLS {α β : Type} (st : LenientStreamT α β) :
    LenientStreamT.ofLS st.toLS = st := by
  cases st; simp [LenientStreamT.toLS, LenientStreamT.ofLS, String.ofList_toList]

theorem LenientStreamT.toLS_ofLS {α β : Type} (st : LenientStream α β) :
    (LenientStreamT.ofLS st).toLS = st := by
  cases st; simp [LenientStreamT.toLS, LenientStreamT.ofLS, String.toList_ofList]

def LenientStreamT.init {α β : Type} (acc : α) (diags : β) : LenientStreamT α β :=
  { run := { acc, diags } }

/-- Take one chunk of text. A line that completes a partial line is read at a cursor; the
lines of a chunk that follows no partial line are read as `LenientStream` reads them. -/
def LenientStreamT.feed (quads : Bool) (mode : Mode) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (st : LenientStreamT α β) (text : String) : LenientStreamT α β :=
  if st.run.stopped then st
  else
    match splitCompleteLines text.toList with
    | ([], _) => { st with carryText := st.carryText ++ text }
    | (cut, rest) =>
      if st.carryText.isEmpty then
        { run := foldLinesLenient (modeReader quads mode) consume report opts (cut.length + 1)
                   st.pos cut st.run,
          carryText := String.ofList rest,
          pos := st.pos + cut.length }
      else
        let complete := st.carryText ++ String.ofList cut
        { run := foldLinesLenientS quads mode consume report opts (complete.length + 1) st.pos
                   complete.startPos st.run,
          carryText := String.ofList rest,
          pos := st.pos + complete.length }

theorem LenientStreamT.feed_eq (quads : Bool) (mode : Mode) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (st : LenientStreamT α β) (text : String) :
    LenientStreamT.feed quads mode consume report opts st text =
      LenientStreamT.ofLS
        (LenientStream.feed (modeReader quads mode) consume report opts st.toLS text.toList) := by
  cases st with
  | mk run carryText pos =>
  by_cases hs : run.stopped = true
  · simp [LenientStreamT.feed, LenientStream.feed, LenientStreamT.toLS, hs,
      LenientStreamT.ofLS, String.ofList_toList]
  simp only [LenientStreamT.feed, LenientStream.feed, LenientStreamT.toLS, hs,
    Bool.false_eq_true, if_false]
  rcases hsp : splitCompleteLines text.toList with ⟨cut, rest'⟩
  cases cut with
  | nil =>
    simp only [LenientStreamT.ofLS, List.reverseAux_eq, List.reverse_append,
      List.reverse_reverse, String.ofList_append, String.ofList_toList]
  | cons x xs =>
    simp only [List.reverseAux_eq, List.reverse_reverse]
    by_cases he : carryText.isEmpty = true
    · have h0 : carryText = "" := by simpa using he
      subst h0
      simp [LenientStreamT.ofLS]
    · rw [if_neg he]
      have ht : (carryText ++ String.ofList (x :: xs)).toList = carryText.toList ++ x :: xs := by
        simp [String.toList_append, String.toList_ofList]
      have hl : (carryText ++ String.ofList (x :: xs)).length =
          (carryText.toList ++ x :: xs).length := by
        rw [← String.length_toList, ht]
      rw [foldLinesLenientS_eq, rest_startPos, hl, ht]
      simp [LenientStreamT.ofLS]

/-- End of input: walk the last partial line. -/
def LenientStreamT.finish (quads : Bool) (mode : Mode) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (st : LenientStreamT α β) : LenientRun α β :=
  if st.run.stopped then st.run
  else
    foldLinesLenientS quads mode consume report opts (st.carryText.length + 1) st.pos
      st.carryText.startPos st.run

theorem LenientStreamT.finish_eq (quads : Bool) (mode : Mode) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) (st : LenientStreamT α β) :
    LenientStreamT.finish quads mode consume report opts st =
      LenientStream.finish (modeReader quads mode) consume report opts st.toLS := by
  by_cases hs : st.run.stopped = true
  · simp [LenientStreamT.finish, LenientStream.finish, LenientStreamT.toLS, hs]
  · simp only [LenientStreamT.finish, LenientStream.finish, LenientStream.carry,
      LenientStreamT.toLS, hs, Bool.false_eq_true, if_false, List.reverse_reverse]
    rw [foldLinesLenientS_eq, rest_startPos, String.length_toList]

/-! ## Guards

The text walk against the list walk on documents cut into pieces of 1 to 4096 characters,
accepted and refused, RDF 1.1 and RDF 1.2: the triples with their graph labels, the
diagnostics with their offsets, lines and columns, and the stop flag. -/

private def collect (a : List (Triple × Option Subject)) (t : Triple) (g : Option Subject) :
    List (Triple × Option Subject) := (t, g) :: a

private def runT (quads : Bool) (mode : Mode) (opts : LenientOptions) (chunks : List String) :
    LenientRun (List (Triple × Option Subject)) (List Diagnostic) :=
  (chunks.foldl (fun st c => st.feed quads mode collect pushDiag opts c)
    (LenientStreamT.init [] [])).finish quads mode collect pushDiag opts

private def runL (quads : Bool) (mode : Mode) (opts : LenientOptions) (chunks : List String) :
    LenientRun (List (Triple × Option Subject)) (List Diagnostic) :=
  (chunks.foldl (fun st c => st.feed (modeReader quads mode) collect pushDiag opts c.toList)
    (LenientStream.init [] [])).finish (modeReader quads mode) collect pushDiag opts

private def sameRun (quads : Bool) (mode : Mode) (opts : LenientOptions) (doc : String) : Bool :=
  [1, 2, 3, 5, 7, 16, 89, 4096].all fun n =>
    let a := runT quads mode opts (piecesOf n doc)
    let b := runL quads mode opts (piecesOf n doc)
    a.acc == b.acc && a.diags == b.diags && a.errors == b.errors && a.stopped == b.stopped

private def docs : List String :=
  [ "<urn:s> <urn:p> <urn:o> .\n<urn:s> <urn:p> .\n_:b <urn:p> \"é\"@fr .\n",
    "# c\n<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 300 'x') ++ "\\u0041\" .\r\n" ++
      "<s> <urn:p> <urn:o> .\n<urn:s> <urn:p> _:b.\n",
    "<urn:s> <urn:p> <urn:o> <urn:g> .\n<urn:s> <urn:p> \"x\" \"y\" .\n\n<urn:a> <urn:b> <urn:c> .",
    "<urn:s> <urn:p> <<( <urn:a> <urn:b> \"c\"@en--rtl )>> .\n<urn:s> <urn:p> << <urn:a> >> .\n" ++
      "<urn:s> <urn:p> \"Alice\" @en .\n",
    "bad line\nbad line 2\n<urn:s> <urn:p> <urn:o> .\nbad line 3\n" ]

#guard docs.all fun d => sameRun true .rdf11 {} d
#guard docs.all fun d => sameRun false .rdf11 {} d
#guard docs.all fun d => sameRun true .rdf12 {} d
#guard docs.all fun d => sameRun false .rdf12 {} d
#guard docs.all fun d => sameRun false .rdf11 { maxErrors := some 1 } d

#print axioms advanceS_eq
#print axioms foldLinesLenientS_eq
#print axioms LenientStreamT.feed_eq
#print axioms LenientStreamT.finish_eq

end L4Factoidal.Syntax.LenientFeedText
