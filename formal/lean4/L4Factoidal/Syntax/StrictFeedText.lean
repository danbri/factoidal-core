/-
L4Factoidal.Syntax.StrictFeedText — the strict N-Triples and N-Quads line walk over
text, for a line longer than one chunk
(https://github.com/danbri/factoidal/issues/874).

`StrictFeed.LineFeed` holds the partial last line as a `List Char` and reads each
completed line as a `List Char`. A `List Char` costs about 33 bytes of resident memory
per character in this runtime (design record section 3b.9), so one line of 8,000,000
bytes peaked at 272 MB. This module reads the line as a `String` at a cursor
(`String.Pos`) and keeps the partial line as a `String`.

* The cursor: `rest p` is the characters from `p` to the end of the string. Every reader
  below takes a cursor and gives a cursor, and its theorem says that the list reader
  of the same name, applied to `rest p`, gives the same value and `rest` of the new
  cursor.
* A native reader may DECLINE (`none`) where the list reader reads a form that is rare in
  a long line (an escape `\u` or `\U`, a label that ends in a dot, an error). The walk
  then runs the list reader from the start of that round on `rest p`: the same answer by
  definition, with the memory cost of the list for the rest of the buffer.
* `foldLinesS_eq`: the walk over a string is the walk `StrictFeed.foldLines` over its
  characters.
* `TextFeed.feed_eq`: one chunk of the text walk is one chunk of `LineFeed.feed` on the
  characters (the bridge `toLF`, `ofLF`), so the theorems of `StrictFeed` and
  `SourceTheorems` apply.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.StrictFeed

namespace L4Factoidal.Syntax.StrictFeedText

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Syntax.NQuadsStreaming
open L4Factoidal.Syntax.StrictFeed

/-! ## The cursor -/

/-- The characters from `p` to the end of the string. -/
def rest {s : String} (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

theorem rest_endPos (s : String) : rest s.endPos = [] := by
  have h := String.splits_endPos s
  have := h.eq_right (String.Pos.splits s.endPos)
  simp [rest, ← this]

theorem rest_next {s : String} (p : s.Pos) (hp : p ≠ s.endPos) :
    rest p = p.get hp :: rest (p.next hp) := by
  have h := p.splits_next_right hp
  have := h.eq_right (String.Pos.splits p)
  simp [rest, ← this]

theorem rest_startPos (s : String) : rest s.startPos = s.toList := by
  have h := String.splits_startPos s
  have := h.eq_right (String.Pos.splits s.startPos)
  simp [rest]

theorem rest_eq_nil {s : String} (p : s.Pos) (h : p = s.endPos) : rest p = [] := by
  subst h; exact rest_endPos s

theorem rest_ne_endPos {s : String} (p : s.Pos) (h : p ≠ s.endPos) : rest p ≠ [] := by
  rw [rest_next p h]; simp

/-! ## White space, comments, line ends -/

theorem skipWs_nil (n : Nat) : skipWs n [] = (n, []) := by
  simp [skipWs, List.span, List.span.loop]

theorem skipWs_ws (n : Nat) {c : Char} (t : List Char) (h : isNtWs c = true) :
    skipWs n (c :: t) = skipWs (n + 1) t := by
  have key : ∀ (acc : List Char) (cs : List Char),
      List.span.loop isNtWs cs acc = ((List.span.loop isNtWs cs []).1 |> fun w => (acc.reverse ++ w, (List.span.loop isNtWs cs []).2)) := by
    intro acc cs
    induction cs generalizing acc with
    | nil => simp [List.span.loop]
    | cons x xs ih =>
      by_cases hx : isNtWs x = true
      · simp only [List.span.loop, hx]
        rw [ih (x :: acc), ih [x]]
        simp
      · simp only [List.span.loop, hx]
        simp
  simp only [skipWs, List.span]
  simp only [List.span.loop, h]
  rw [key [c] t]
  simp [Nat.add_assoc, Nat.add_comm]

theorem skipWs_nows (n : Nat) {c : Char} (t : List Char) (h : isNtWs c = false) :
    skipWs n (c :: t) = (n, c :: t) := by
  simp [skipWs, List.span, List.span.loop, h]

/-- A run of space and tab. -/
def skipWsS {s : String} (n : Nat) (p : s.Pos) : Nat × s.Pos :=
  if h : p = s.endPos then (n, p)
  else if isNtWs (p.get h) then skipWsS (n + 1) (p.next h)
  else (n, p)
termination_by p.remainingBytes
decreasing_by simp [← String.Pos.lt_iff_remainingBytes_lt]

theorem skipWsS_eq {s : String} (n : Nat) (p : s.Pos) :
    ((skipWsS n p).1, rest (skipWsS n p).2) = skipWs n (rest p) := by
  induction n, p using skipWsS.induct with
  | case1 n =>
    rw [skipWsS, dif_pos rfl, rest_endPos, skipWs_nil]
  | case2 n p h hw ih =>
    rw [skipWsS, dif_neg h, if_pos hw, ih, rest_next p h, skipWs_ws n _ hw]
  | case3 n p h hw =>
    rw [skipWsS, dif_neg h, if_neg hw, rest_next p h, skipWs_nows n _ (by simpa using hw)]

/-- To the next line break or the end of the text. -/
def skipToEolS {s : String} (n : Nat) (p : s.Pos) : Nat × s.Pos :=
  if h : p = s.endPos then (n, p)
  else if (p.get h = '\n' || p.get h = '\r') then (n, p)
  else skipToEolS (n + 1) (p.next h)
termination_by p.remainingBytes
decreasing_by simp [← String.Pos.lt_iff_remainingBytes_lt]

theorem skipToEolS_eq {s : String} (n : Nat) (p : s.Pos) :
    ((skipToEolS n p).1, rest (skipToEolS n p).2) = skipToEol n (rest p) := by
  induction n, p using skipToEolS.induct with
  | case1 n =>
    rw [skipToEolS, dif_pos rfl, rest_endPos]; simp [skipToEol]
  | case2 n p h hc =>
    rw [skipToEolS, dif_neg h, if_pos hc, rest_next p h]
    simp only [skipToEol, hc, if_true]
  | case3 n p h hc ih =>
    have hc' : ¬(p.get h = '\n' ∨ p.get h = '\r') := by simpa using hc
    rw [skipToEolS, dif_neg h, if_neg hc, ih, rest_next p h]
    simp [skipToEol, hc']

def skipCommentS {s : String} (n : Nat) (p : s.Pos) : Nat × s.Pos :=
  if h : p = s.endPos then (n, p)
  else if p.get h = '#' then skipToEolS (n + 1) (p.next h)
  else (n, p)

theorem skipCommentS_eq {s : String} (n : Nat) (p : s.Pos) :
    ((skipCommentS n p).1, rest (skipCommentS n p).2) = skipComment n (rest p) := by
  unfold skipCommentS
  by_cases h : p = s.endPos
  · rw [dif_pos h, rest_eq_nil p h]; simp [skipComment]
  · rw [dif_neg h]
    by_cases hc : p.get h = '#'
    · rw [if_pos hc, skipToEolS_eq, rest_next p h, hc]; simp [skipComment]
    · rw [if_neg hc, rest_next p h]
      generalize p.get h = c at hc ⊢
      generalize rest (p.next h) = t
      cases c with
      | mk v hv => simp_all [skipComment]

def skipEolS {s : String} (n : Nat) (p : s.Pos) : Nat × s.Pos :=
  if h : p = s.endPos then (n, p)
  else if p.get h = '\r' then
    let q := p.next h
    if hq : q = s.endPos then (n + 1, q)
    else if q.get hq = '\n' then (n + 2, q.next hq)
    else (n + 1, q)
  else if p.get h = '\n' then (n + 1, p.next h)
  else (n, p)

theorem skipEolS_eq {s : String} (n : Nat) (p : s.Pos) :
    ((skipEolS n p).1, rest (skipEolS n p).2) = skipEol n (rest p) := by
  unfold skipEolS
  by_cases h : p = s.endPos
  · rw [dif_pos h, rest_eq_nil p h]; simp [skipEol]
  · rw [dif_neg h]
    by_cases hr : p.get h = '\r'
    · rw [if_pos hr, rest_next p h, hr]
      by_cases hq : p.next h = s.endPos
      · simp only [dif_pos hq, rest_eq_nil _ hq, skipEol]
      · simp only [dif_neg hq]
        by_cases hn : (p.next h).get hq = '\n'
        · rw [if_pos hn]
          simp only []
          rw [rest_next (p.next h) hq, hn]
          simp [skipEol]
        · rw [if_neg hn]
          simp only []
          rw [rest_next (p.next h) hq]
          generalize (p.next h).get hq = c at hn
          generalize rest ((p.next h).next hq) = t
          cases c with
          | mk v hv => simp_all [skipEol, Char.ext_iff]
    · rw [if_neg hr]
      by_cases hn : p.get h = '\n'
      · rw [if_pos hn, rest_next p h, hn]; simp [skipEol]
      · rw [if_neg hn]
        simp only []
        rw [rest_next p h]
        generalize p.get h = c at hr hn ⊢
        generalize rest (p.next h) = t
        cases c with
        | mk v hv => simp_all [skipEol, Char.ext_iff]

/-! ## IRIREF -/

def iriPlain (c : Char) : Bool := !(decide (c.toNat ≤ 0x20) || isIriForbiddenCodepoint c.toNat)

theorem iriPlain_ne_gt {c : Char} (h : iriPlain c = true) : c ≠ '>' := by
  intro hc; subst hc; simp [iriPlain, isIriForbiddenCodepoint] at h

theorem iriPlain_ne_bs {c : Char} (h : iriPlain c = true) : c ≠ '\\' := by
  intro hc; subst hc; simp [iriPlain, isIriForbiddenCodepoint] at h

theorem iriNextStep_plain (pos : Nat) {c : Char} (t : List Char) (h : iriPlain c = true) :
    iriNextStep pos (c :: t) = .emit c 1 t := by
  have h1 := iriPlain_ne_gt h
  have h2 := iriPlain_ne_bs h
  unfold iriNextStep
  split <;> simp_all [iriPlain]

theorem readIriRefBodyGo_close (pos : Nat) (acc : String) (cs rest : List Char)
    (h : iriNextStep pos cs = .close rest) :
    readIriRefBodyGo pos acc cs = .ok (acc, pos + 1, rest) := by
  rw [readIriRefBodyGo]; split <;> simp_all

theorem readIriRefBodyGo_emit (pos : Nat) (acc : String) (cs r : List Char) (c : Char) (w : Nat)
    (h : iriNextStep pos cs = .emit c w r) :
    readIriRefBodyGo pos acc cs = readIriRefBodyGo (pos + w) (acc.push c) r := by
  rw [readIriRefBodyGo]; split <;> simp_all

/-- The IRIREF body from `p`: plain characters up to `>`. Declines on an escape or on a
character the list reader refuses. -/
def iriBodyS {s : String} (pos : Nat) (acc : String) (p : s.Pos) :
    Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '>' then some (acc, pos + 1, p.next h)
  else if iriPlain (p.get h) then iriBodyS (pos + 1) (acc.push (p.get h)) (p.next h)
  else none
termination_by p.remainingBytes
decreasing_by simp [← String.Pos.lt_iff_remainingBytes_lt]

theorem iriBodyS_sound {s : String} (pos : Nat) (acc : String) (p : s.Pos)
    (str : String) (pos' : Nat) (q : s.Pos) (hq : iriBodyS pos acc p = some (str, pos', q)) :
    readIriRefBodyGo pos acc (rest p) = .ok (str, pos', rest q) := by
  induction pos, acc, p using iriBodyS.induct generalizing str pos' q with
  | case1 pos acc => rw [iriBodyS, dif_pos rfl] at hq; cases hq
  | case2 pos acc p h hg =>
    rw [iriBodyS, dif_neg h, if_pos hg] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    rw [rest_next p h]
    exact readIriRefBodyGo_close _ _ _ _ (by rw [hg]; rfl)
  | case3 pos acc p h hg hp ih =>
    rw [iriBodyS, dif_neg h, if_neg hg, if_pos hp] at hq
    rw [rest_next p h, readIriRefBodyGo_emit _ _ _ _ _ _ (iriNextStep_plain _ _ hp)]
    exact ih str pos' q hq
  | case4 pos acc p h hg hp => rw [iriBodyS, dif_neg h, if_neg hg, if_neg hp] at hq; cases hq

theorem readIriRefBody_of_go {pos : Nat} {cs : List Char} {str : String} {n : Nat}
    {r : List Char} (h : readIriRefBodyGo pos "" cs = .ok (str, n, r)) :
    readIriRefBody pos cs = .ok (str, n, r) := by
  rw [readIriRefBodyGo_eq] at h
  cases hb : readIriRefBody pos cs with
  | error e => rw [hb] at h; simp [Except.map] at h
  | ok v =>
    obtain ⟨s', p', r'⟩ := v
    rw [hb] at h
    simp [Except.map] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/-- IRIREF at `p`: `<`, the body, `>`. -/
def iriRefS {s : String} (pos : Nat) (p : s.Pos) : Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '<' then iriBodyS (pos + 1) "" (p.next h)
  else none

theorem iriRefS_sound {s : String} (pos : Nat) (p : s.Pos)
    (str : String) (pos' : Nat) (q : s.Pos) (hq : iriRefS pos p = some (str, pos', q)) :
    readIriRef pos (rest p) = .ok (str, pos', rest q) := by
  unfold iriRefS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  · rw [dif_neg h] at hq
    by_cases hl : p.get h = '<'
    · rw [if_pos hl] at hq
      have := readIriRefBody_of_go (iriBodyS_sound _ _ _ _ _ _ hq)
      rw [rest_next p h, hl]
      exact this
    · rw [if_neg hl] at hq; cases hq

/-! ## STRING_LITERAL_QUOTED -/

/-- A character that stands for itself in a literal body. -/
def litPlain (c : Char) : Bool := c != '"' && c != '\\' && c != '\n' && c != '\r'

/-- The character of a two-character escape (ECHAR); `\u` and `\U` are not here. -/
def echar? : Char → Option Char
  | 't' => some '\t'
  | 'b' => some (Char.ofNat 0x08)
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 'f' => some (Char.ofNat 0x0C)
  | '"' => some '"'
  | '\'' => some '\''
  | '\\' => some '\\'
  | _ => none

theorem strLitNextStep_plain (pos : Nat) {c : Char} (t : List Char) (h : litPlain c = true) :
    strLitNextStep pos (c :: t) = .emit c 1 t := by
  simp only [litPlain, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold strLitNextStep
  split <;> simp_all

theorem strLitNextStep_echar (pos : Nat) {x d : Char} (t : List Char) (h : echar? x = some d) :
    strLitNextStep pos ('\\' :: x :: t) = .emit d 2 t := by
  unfold echar? at h
  split at h <;> simp at h <;> subst h <;> rfl

theorem strLitNextStep_close (pos : Nat) (t : List Char) :
    strLitNextStep pos ('"' :: t) = .close t := rfl

theorem readStringLiteralBodyGo_close (pos : Nat) (acc : String) (cs rest : List Char)
    (h : strLitNextStep pos cs = .close rest) :
    readStringLiteralBodyGo pos acc cs = .ok (acc, pos + 1, rest) := by
  rw [readStringLiteralBodyGo]; split <;> simp_all

theorem readStringLiteralBodyGo_emit (pos : Nat) (acc : String) (cs r : List Char) (c : Char)
    (w : Nat) (h : strLitNextStep pos cs = .emit c w r) :
    readStringLiteralBodyGo pos acc cs = readStringLiteralBodyGo (pos + w) (acc.push c) r := by
  rw [readStringLiteralBodyGo]; split <;> simp_all

/-- The literal body from `p`: plain characters and two-character escapes up to `"`.
Declines on `\u`, `\U`, and what the list reader refuses. -/
def litBodyS {s : String} (pos : Nat) (acc : String) (p : s.Pos) :
    Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '"' then some (acc, pos + 1, p.next h)
  else if litPlain (p.get h) then litBodyS (pos + 1) (acc.push (p.get h)) (p.next h)
  else if p.get h = '\\' then
    if hq : p.next h = s.endPos then none
    else
      match hd : echar? ((p.next h).get hq) with
      | some d => litBodyS (pos + 2) (acc.push d) ((p.next h).next hq)
      | none => none
  else none
termination_by p.remainingBytes
decreasing_by
  all_goals simp [← String.Pos.lt_iff_remainingBytes_lt]

theorem litBodyS_sound {s : String} (pos : Nat) (acc : String) (p : s.Pos)
    (str : String) (pos' : Nat) (q : s.Pos) (hq : litBodyS pos acc p = some (str, pos', q)) :
    readStringLiteralBodyGo pos acc (rest p) = .ok (str, pos', rest q) := by
  induction pos, acc, p using litBodyS.induct generalizing str pos' q with
  | case1 pos acc => rw [litBodyS, dif_pos rfl] at hq; cases hq
  | case2 pos acc p h hg =>
    rw [litBodyS, dif_neg h, if_pos hg] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    rw [rest_next p h]
    exact readStringLiteralBodyGo_close _ _ _ _ (by rw [hg]; rfl)
  | case3 pos acc p h hg hp ih =>
    rw [litBodyS, dif_neg h, if_neg hg, if_pos hp] at hq
    rw [rest_next p h, readStringLiteralBodyGo_emit _ _ _ _ _ _ (strLitNextStep_plain _ _ hp)]
    exact ih str pos' q hq
  | case4 pos acc p h hg hp hb hq2 =>
    rw [litBodyS, dif_neg h, if_neg hg, if_neg hp, if_pos hb, dif_pos hq2] at hq; cases hq
  | case5 pos acc p h hg hp hb hq2 d hd ih =>
    rw [litBodyS, dif_neg h, if_neg hg, if_neg hp, if_pos hb, dif_neg hq2] at hq
    split at hq
    · rename_i d' hd'
      have hdd : d' = d := by rw [hd] at hd'; exact (Option.some.inj hd').symm
      subst hdd
      rw [rest_next p h, rest_next (p.next h) hq2, hb,
        readStringLiteralBodyGo_emit _ _ _ _ _ _ (strLitNextStep_echar _ _ hd)]
      exact ih str pos' q hq
    · rename_i hd'; rw [hd] at hd'; cases hd'
  | case6 pos acc p h hg hp hb hq2 hd =>
    rw [litBodyS, dif_neg h, if_neg hg, if_neg hp, if_pos hb, dif_neg hq2] at hq
    split at hq
    · rename_i d' hd'; rw [hd] at hd'; cases hd'
    · cases hq
  | case7 pos acc p h hg hp hb =>
    rw [litBodyS, dif_neg h, if_neg hg, if_neg hp, if_neg hb] at hq; cases hq

theorem readStringLiteralBody_of_go {pos : Nat} {cs : List Char} {str : String} {n : Nat}
    {r : List Char} (h : readStringLiteralBodyGo pos "" cs = .ok (str, n, r)) :
    readStringLiteralBody pos cs = .ok (str, n, r) := by
  rw [readStringLiteralBodyGo_eq] at h
  cases hb : readStringLiteralBody pos cs with
  | error e => rw [hb] at h; simp [Except.map] at h
  | ok v =>
    obtain ⟨s', p', r'⟩ := v
    rw [hb] at h
    simp [Except.map] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/-- STRING_LITERAL_QUOTED at `p`. -/
def litQuotedS {s : String} (pos : Nat) (p : s.Pos) : Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '"' then litBodyS (pos + 1) "" (p.next h)
  else none

theorem litQuotedS_sound {s : String} (pos : Nat) (p : s.Pos)
    (str : String) (pos' : Nat) (q : s.Pos) (hq : litQuotedS pos p = some (str, pos', q)) :
    readStringLiteralQuoted pos (rest p) = .ok (str, pos', rest q) := by
  unfold litQuotedS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  · rw [dif_neg h] at hq
    by_cases hl : p.get h = '"'
    · rw [if_pos hl] at hq
      have := readStringLiteralBody_of_go (litBodyS_sound _ _ _ _ _ _ hq)
      rw [rest_next p h, hl]
      exact this
    · rw [if_neg hl] at hq; cases hq

/-! ## A run of characters -/

/-- The characters from `p` while `f` holds: their count added to `n`, the text pushed onto
`acc`, and the cursor after them. -/
def runS {s : String} (f : Char → Bool) (n : Nat) (acc : String) (p : s.Pos) :
    Nat × String × s.Pos :=
  if h : p = s.endPos then (n, acc, p)
  else if f (p.get h) then runS f (n + 1) (acc.push (p.get h)) (p.next h)
  else (n, acc, p)
termination_by p.remainingBytes
decreasing_by simp [← String.Pos.lt_iff_remainingBytes_lt]

theorem span_nil (f : Char → Bool) : List.span f [] = ([], []) := by
  simp [List.span, List.span.loop]

theorem span_cons_pos (f : Char → Bool) {c : Char} (t : List Char) (h : f c = true) :
    List.span f (c :: t) = (c :: (List.span f t).1, (List.span f t).2) := by
  have key : ∀ (acc : List Char) (cs : List Char),
      List.span.loop f cs acc =
        (acc.reverse ++ (List.span.loop f cs []).1, (List.span.loop f cs []).2) := by
    intro acc cs
    induction cs generalizing acc with
    | nil => simp [List.span.loop]
    | cons x xs ih =>
      by_cases hx : f x = true
      · simp only [List.span.loop, hx]
        rw [ih (x :: acc), ih [x]]
        simp
      · simp only [List.span.loop, hx]
        simp
  simp only [List.span]
  simp only [List.span.loop, h]
  rw [key [c] t]
  simp

theorem span_cons_neg (f : Char → Bool) {c : Char} (t : List Char) (h : f c = false) :
    List.span f (c :: t) = ([], c :: t) := by
  simp [List.span, List.span.loop, h]

theorem runS_pos {s : String} (f : Char → Bool) (n : Nat) (acc : String) (p : s.Pos)
    (h : p ≠ s.endPos) (hf : f (p.get h) = true) :
    runS f n acc p = runS f (n + 1) (acc.push (p.get h)) (p.next h) := by
  rw [runS, dif_neg h, if_pos hf]

theorem runS_neg {s : String} (f : Char → Bool) (n : Nat) (acc : String) (p : s.Pos)
    (h : p ≠ s.endPos) (hf : f (p.get h) = false) :
    runS f n acc p = (n, acc, p) := by
  rw [runS, dif_neg h, if_neg (by simp [hf])]

theorem runS_end {s : String} (f : Char → Bool) (n : Nat) (acc : String) :
    runS f n acc s.endPos = (n, acc, s.endPos) := by
  rw [runS, dif_pos rfl]

theorem runS_eq {s : String} (f : Char → Bool) (n : Nat) (acc : String) (p : s.Pos) :
    ∃ run : List Char, (rest p).span f = (run, rest (runS f n acc p).2.2) ∧
      (runS f n acc p).1 = n + run.length ∧ (runS f n acc p).2.1.toList = acc.toList ++ run := by
  induction n, acc, p using runS.induct (f := f) with
  | case1 n acc =>
    refine ⟨[], ?_, ?_, ?_⟩ <;> simp [runS_end, rest_endPos, span_nil]
  | case2 n acc p h hf ih =>
    obtain ⟨run, h1, h2, h3⟩ := ih
    rw [runS_pos f n acc p h hf]
    refine ⟨p.get h :: run, ?_, ?_, ?_⟩
    · rw [rest_next p h, span_cons_pos f _ hf, h1]
    · rw [h2]; simp; omega
    · rw [h3]; simp
  | case3 n acc p h hf =>
    rw [runS_neg f n acc p h (by simpa using hf)]
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [rest_next p h, span_cons_neg f _ (by simpa using hf)]
    · simp
    · simp

/-! ## BLANK_NODE_LABEL, LANGTAG, datatype -/

/-- The label from its first character `c0` and the run after it. Declines when the label
ends in a dot (the list reader gives the dot back to the input). -/
def bnodeFinish (pos : Nat) (c0 : Char) (body : String) {s : String} (e : s.Pos) :
    Option (String × Nat × s.Pos) :=
  match (c0 :: body.toList).getLast? with
  | some '.' => none
  | _ => some (String.ofList (c0 :: body.toList), pos + 2 + (c0 :: body.toList).length, e)

/-- `_:` label, when the label does not end in a dot. Declines otherwise. -/
def bnodeS {s : String} (pos : Nat) (p : s.Pos) : Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '_' then
    if hq : p.next h = s.endPos then none
    else if (p.next h).get hq = ':' then
      if hr : (p.next h).next hq = s.endPos then none
      else if isBnodeStartChar (((p.next h).next hq).get hr) then
        bnodeFinish pos (((p.next h).next hq).get hr)
          (runS isBnodeChar 0 "" (((p.next h).next hq).next hr)).2.1
          (runS isBnodeChar 0 "" (((p.next h).next hq).next hr)).2.2
      else none
    else none
  else none

theorem bnodeS_sound {s : String} (pos : Nat) (p : s.Pos)
    (str : String) (pos' : Nat) (q : s.Pos) (hq : bnodeS pos p = some (str, pos', q)) :
    (∃ t, rest p = '_' :: ':' :: t) ∧ readBlankNodeLabel pos (rest p) = .ok (str, pos', rest q) := by
  unfold bnodeS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  rw [dif_neg h] at hq
  by_cases h1 : p.get h = '_'
  case neg => rw [if_neg h1] at hq; cases hq
  rw [if_pos h1] at hq
  by_cases hq1 : p.next h = s.endPos
  · rw [dif_pos hq1] at hq; cases hq
  rw [dif_neg hq1] at hq
  by_cases h2 : (p.next h).get hq1 = ':'
  case neg => rw [if_neg h2] at hq; cases hq
  rw [if_pos h2] at hq
  by_cases hr : (p.next h).next hq1 = s.endPos
  · rw [dif_pos hr] at hq; cases hq
  rw [dif_neg hr] at hq
  by_cases h3 : isBnodeStartChar (((p.next h).next hq1).get hr) = true
  case neg => rw [if_neg h3] at hq; cases hq
  rw [if_pos h3] at hq
  obtain ⟨run, hspan, hn, hs⟩ := runS_eq isBnodeChar 0 "" (((p.next h).next hq1).next hr)
  have hrest : rest p = '_' :: ':' :: ((((p.next h).next hq1).get hr) :: rest (((p.next h).next hq1).next hr)) := by
    rw [rest_next p h, rest_next (p.next h) hq1, rest_next ((p.next h).next hq1) hr, h1, h2]
  refine ⟨⟨_, hrest⟩, ?_⟩
  rw [hrest]
  unfold bnodeFinish at hq
  simp only [hs, String.toList_empty, List.nil_append] at hq
  simp only [readBlankNodeLabel, h3, Bool.not_true, Bool.false_eq_true, if_false, hspan]
  split at hq
  · cases hq
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    split
    · rename_i hl'; exact absurd hl' (by simpa using hl)
    · rfl

/-- `@` and a LANGTAG, RDF 1.1. -/
def langS {s : String} (pos : Nat) (p : s.Pos) : Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '@' then
    if hq : p.next h = s.endPos then none
    else if isLangStart ((p.next h).get hq) then
      some ((runS isLangChar 0 "" (p.next h)).2.1, pos + 1 + (runS isLangChar 0 "" (p.next h)).1,
            (runS isLangChar 0 "" (p.next h)).2.2)
    else none
  else none

theorem langS_sound {s : String} (pos : Nat) (p : s.Pos)
    (str : String) (pos' : Nat) (q : s.Pos) (hq : langS pos p = some (str, pos', q)) :
    (∃ t, rest p = '@' :: t) ∧ readLangTag pos (rest p) = .ok (str, pos', rest q) := by
  unfold langS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  rw [dif_neg h] at hq
  by_cases h1 : p.get h = '@'
  case neg => rw [if_neg h1] at hq; cases hq
  rw [if_pos h1] at hq
  by_cases hq1 : p.next h = s.endPos
  · rw [dif_pos hq1] at hq; cases hq
  rw [dif_neg hq1] at hq
  by_cases h2 : isLangStart ((p.next h).get hq1) = true
  case neg => rw [if_neg h2] at hq; cases hq
  rw [if_pos h2] at hq
  obtain ⟨run, hspan, hn, hs⟩ := runS_eq isLangChar 0 "" (p.next h)
  have hrest : rest p = '@' :: ((p.next h).get hq1 :: rest ((p.next h).next hq1)) := by
    rw [rest_next p h, rest_next (p.next h) hq1, h1]
  refine ⟨⟨_, hrest⟩, ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl⟩ := hq
  have hrest' := rest_next (p.next h) hq1
  rw [hrest]
  simp only [readLangTag, h2, Bool.not_true, Bool.false_eq_true, if_false]
  rw [← hrest']
  simp only [readLangTagRun, hspan, hn, Nat.zero_add]
  simp [Nat.add_assoc]
  have hs' : (runS isLangChar 0 "" (p.next h)).snd.fst.toList = run := by simpa using hs
  rw [← hs', String.ofList_toList]


/-- `^^` and an IRIREF, RDF 1.1. -/
def datatypeS {s : String} (pos : Nat) (p : s.Pos) : Option (WfIri × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '^' then
    if hq : p.next h = s.endPos then none
    else if (p.next h).get hq = '^' then
      match iriRefS (pos + 2) ((p.next h).next hq) with
      | none => none
      | some (str, pos', q) =>
          match mkIri pos str with
          | .error _ => none
          | .ok wi => some (wi, pos', q)
    else none
  else none

theorem datatypeS_sound {s : String} (pos : Nat) (p : s.Pos)
    (wi : WfIri) (pos' : Nat) (q : s.Pos) (hq : datatypeS pos p = some (wi, pos', q)) :
    (∃ t, rest p = '^' :: '^' :: t) ∧ readDatatype pos (rest p) = .ok (wi, pos', rest q) := by
  unfold datatypeS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  rw [dif_neg h] at hq
  by_cases h1 : p.get h = '^'
  case neg => rw [if_neg h1] at hq; cases hq
  rw [if_pos h1] at hq
  by_cases hq1 : p.next h = s.endPos
  · rw [dif_pos hq1] at hq; cases hq
  rw [dif_neg hq1] at hq
  by_cases h2 : (p.next h).get hq1 = '^'
  case neg => rw [if_neg h2] at hq; cases hq
  rw [if_pos h2] at hq
  have hrest : rest p = '^' :: '^' :: rest ((p.next h).next hq1) := by
    rw [rest_next p h, rest_next (p.next h) hq1, h1, h2]
  refine ⟨⟨_, hrest⟩, ?_⟩
  rw [hrest]
  split at hq
  · cases hq
  · rename_i str pos2 q2 hi
    split at hq
    · cases hq
    · rename_i wi' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      have := iriRefS_sound _ _ _ _ _ hi
      simp only [readDatatype, this, hm]

/-- A literal without a language tag or datatype: `xsd:string`. -/
def plainLiteralS {s : String} (lex : String) (pos1 : Nat) (q1 : s.Pos) :
    Option (WfLiteral × Nat × s.Pos) :=
  match mkLiteral pos1
      { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none } with
  | .error _ => none
  | .ok wl => some (wl, pos1, q1)

/-- A literal, RDF 1.1: the body, then an optional `@lang` or `^^<datatype>`. -/
def literalS {s : String} (pos : Nat) (p : s.Pos) : Option (WfLiteral × Nat × s.Pos) :=
  match litQuotedS pos p with
  | none => none
  | some (lex, pos1, q1) =>
    if h : q1 = s.endPos then plainLiteralS lex pos1 q1
    else if q1.get h = '@' then
      match langS pos1 q1 with
      | none => none
      | some (tag, pos2, q2) =>
        match mkLiteral pos1
            { lexicalForm := lex, datatype := rdfLangString, langTag := some tag,
              direction := none } with
        | .error _ => none
        | .ok wl => some (wl, pos2, q2)
    else if q1.get h = '^' then
      match datatypeS pos1 q1 with
      | none => none
      | some (dt, pos2, q2) =>
        match mkLiteral pos1
            { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
        | .error _ => none
        | .ok wl => some (wl, pos2, q2)
    else plainLiteralS lex pos1 q1

theorem literalS_sound {s : String} (pos : Nat) (p : s.Pos)
    (wl : WfLiteral) (pos' : Nat) (q : s.Pos) (hq : literalS pos p = some (wl, pos', q)) :
    readLiteral .rdf11 pos (rest p) = .ok (wl, pos', rest q) := by
  unfold literalS at hq
  split at hq
  · cases hq
  rename_i lex pos1 q1 hlq
  have hl := litQuotedS_sound _ _ _ _ _ hlq
  by_cases h : q1 = s.endPos
  · rw [dif_pos h] at hq
    unfold plainLiteralS at hq
    split at hq
    · cases hq
    · rename_i wl' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      simp only [readLiteral, hl, rest_eq_nil q1 h, hm]
  rw [dif_neg h] at hq
  by_cases h1 : q1.get h = '@'
  · rw [if_pos h1] at hq
    split at hq
    · cases hq
    · rename_i tag pos2 q2 hlang
      split at hq
      · cases hq
      · rename_i wl' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl, rfl⟩ := hq
        obtain ⟨⟨t, ht⟩, hr⟩ := langS_sound _ _ _ _ _ hlang
        rw [ht] at hr
        simp only [readLiteral, hl, ht, hr, hm]
  rw [if_neg h1] at hq
  by_cases h2 : q1.get h = '^'
  · rw [if_pos h2] at hq
    split at hq
    · cases hq
    · rename_i dt pos2 q2 hdt
      split at hq
      · cases hq
      · rename_i wl' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl, rfl⟩ := hq
        obtain ⟨⟨t, ht⟩, hr⟩ := datatypeS_sound _ _ _ _ _ hdt
        rw [ht] at hr
        simp only [readLiteral, hl, ht, hr, hm]
  rw [if_neg h2] at hq
  unfold plainLiteralS at hq
  split at hq
  · cases hq
  · rename_i wl' hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    have hr := rest_next q1 h
    generalize q1.get h = c at hr h1 h2
    generalize rest (q1.next h) = t at hr
    simp only [readLiteral, hl, hr]
    cases c with
    | mk v hv => simp_all [Char.ext_iff]

/-! ## Subject, predicate, object, graph label -/

/-- An IRIREF as a well-formed IRI. -/
def wfIriS {s : String} (pos : Nat) (p : s.Pos) : Option (WfIri × Nat × s.Pos) :=
  match iriRefS pos p with
  | none => none
  | some (str, pos', q) =>
    match mkIri pos str with
    | .error _ => none
    | .ok wi => some (wi, pos', q)

/-- The IRIREF-and-`mkIri` step shared by the subject, predicate, object and graph label
readers of `Syntax.NTriples`, as the list reader states it. -/
def wfIriL (pos : Nat) (cs : List Char) : Except ParseError (WfIri × Nat × List Char) :=
  match readIriRef pos cs with
  | .error e => .error e
  | .ok (s', pos', rest') =>
      match mkIri pos s' with
      | .error e => .error e
      | .ok wi => .ok (wi, pos', rest')

theorem wfIriS_sound {s : String} (pos : Nat) (p : s.Pos)
    (wi : WfIri) (pos' : Nat) (q : s.Pos) (hq : wfIriS pos p = some (wi, pos', q)) :
    wfIriL pos (rest p) = .ok (wi, pos', rest q) := by
  unfold wfIriS at hq
  split at hq
  · cases hq
  · rename_i str pos2 q2 hi
    split at hq
    · cases hq
    · rename_i wi' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      simp only [wfIriL, iriRefS_sound _ _ _ _ _ hi, hm]

theorem readPredicate_eq (pos : Nat) (cs : List Char) :
    readPredicate pos cs = wfIriL pos cs := rfl

def predicateS {s : String} (pos : Nat) (p : s.Pos) : Option (WfIri × Nat × s.Pos) :=
  wfIriS pos p

def subjectS {s : String} (pos : Nat) (p : s.Pos) : Option (Subject × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '<' then
    match wfIriS pos p with
    | none => none
    | some (wi, pos', q) => some (.iri wi, pos', q)
  else if p.get h = '_' then
    match bnodeS pos p with
    | none => none
    | some (label, pos', q) => some (.bnode label, pos', q)
  else none

theorem subjectS_sound {s : String} (pos : Nat) (p : s.Pos)
    (v : Subject) (pos' : Nat) (q : s.Pos) (hq : subjectS pos p = some (v, pos', q)) :
    readSubject pos (rest p) = .ok (v, pos', rest q) := by
  unfold subjectS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  rw [dif_neg h] at hq
  by_cases h1 : p.get h = '<'
  · rw [if_pos h1] at hq
    split at hq
    · cases hq
    · rename_i wi pos2 q2 hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      have hr := wfIriS_sound _ _ _ _ _ hw
      have ht : rest p = '<' :: rest (p.next h) := by rw [rest_next p h, h1]
      rw [ht] at hr ⊢
      simp only [readSubject]
      simp only [wfIriL] at hr
      split at hr
      · cases hr
      · rename_i s' p' r' hi
        split at hr
        · cases hr
        · rename_i wi' hm
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp only [hi, hm]
  rw [if_neg h1] at hq
  by_cases h2 : p.get h = '_'
  · rw [if_pos h2] at hq
    split at hq
    · cases hq
    · rename_i label pos2 q2 hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      obtain ⟨⟨t, ht⟩, hr⟩ := bnodeS_sound _ _ _ _ _ hb
      rw [ht] at hr ⊢
      simp only [readSubject, hr]
  rw [if_neg h2] at hq; cases hq

theorem predicateS_sound {s : String} (pos : Nat) (p : s.Pos)
    (v : WfIri) (pos' : Nat) (q : s.Pos) (hq : predicateS pos p = some (v, pos', q)) :
    readPredicate pos (rest p) = .ok (v, pos', rest q) := by
  rw [readPredicate_eq]; exact wfIriS_sound _ _ _ _ _ hq

def objectS {s : String} (pos : Nat) (p : s.Pos) : Option (Term × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '<' then
    match wfIriS pos p with
    | none => none
    | some (wi, pos', q) => some (.iri wi, pos', q)
  else if p.get h = '_' then
    match bnodeS pos p with
    | none => none
    | some (label, pos', q) => some (.bnode label, pos', q)
  else if p.get h = '"' then
    match literalS pos p with
    | none => none
    | some (wl, pos', q) => some (.literal wl, pos', q)
  else none

theorem objectS_sound {s : String} (pos : Nat) (p : s.Pos)
    (v : Term) (pos' : Nat) (q : s.Pos) (hq : objectS pos p = some (v, pos', q)) :
    readObject11 pos (rest p) = .ok (v, pos', rest q) := by
  unfold objectS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  rw [dif_neg h] at hq
  by_cases h1 : p.get h = '<'
  · rw [if_pos h1] at hq
    split at hq
    · cases hq
    · rename_i wi pos2 q2 hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      have hr := wfIriS_sound _ _ _ _ _ hw
      have ht : rest p = '<' :: rest (p.next h) := by rw [rest_next p h, h1]
      rw [ht] at hr ⊢
      simp only [readObject11]
      simp only [wfIriL] at hr
      split at hr
      · cases hr
      · rename_i s' p' r' hi
        split at hr
        · cases hr
        · rename_i wi' hm
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp only [hi, hm]
  rw [if_neg h1] at hq
  by_cases h2 : p.get h = '_'
  · rw [if_pos h2] at hq
    split at hq
    · cases hq
    · rename_i label pos2 q2 hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      obtain ⟨⟨t, ht⟩, hr⟩ := bnodeS_sound _ _ _ _ _ hb
      rw [ht] at hr ⊢
      simp only [readObject11, hr]
  rw [if_neg h2] at hq
  by_cases h3 : p.get h = '"'
  · rw [if_pos h3] at hq
    split at hq
    · cases hq
    · rename_i wl pos2 q2 hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      have hr := literalS_sound _ _ _ _ _ hl
      have ht : rest p = '"' :: rest (p.next h) := by rw [rest_next p h, h3]
      rw [ht] at hr ⊢
      simp only [readObject11, hr]
  rw [if_neg h3] at hq; cases hq

/-! ## The optional graph label -/

def optGraphLabelAt {s : String} (pos1 : Nat) (p1 : s.Pos) :
    Option (Option Subject × Nat × s.Pos) :=
  if h : p1 = s.endPos then some (none, pos1, p1)
  else if p1.get h = '.' then some (none, pos1, p1)
  else if p1.get h = '<' then
    match wfIriS pos1 p1 with
    | none => none
    | some (wi, pos', q) => some (some (.iri wi), pos', q)
  else if p1.get h = '_' then
    match bnodeS pos1 p1 with
    | none => none
    | some (label, pos', q) => some (some (.bnode label), pos', q)
  else if p1.get h = '"' then none
  else some (none, pos1, p1)

def optGraphLabelS {s : String} (pos : Nat) (p : s.Pos) :
    Option (Option Subject × Nat × s.Pos) :=
  optGraphLabelAt (skipWsS pos p).1 (skipWsS pos p).2

theorem optGraphLabelS_sound {s : String} (pos : Nat) (p : s.Pos)
    (v : Option Subject) (pos' : Nat) (q : s.Pos)
    (hq : optGraphLabelS pos p = some (v, pos', q)) :
    readOptGraphLabel pos (rest p) = .ok (v, pos', rest q) := by
  unfold optGraphLabelS at hq
  have hw := skipWsS_eq pos p
  generalize (skipWsS pos p).1 = pos1 at hq hw
  generalize (skipWsS pos p).2 = p1 at hq hw
  unfold readOptGraphLabel
  rw [← hw]
  simp only []
  unfold optGraphLabelAt at hq
  by_cases h : p1 = s.endPos
  · rw [dif_pos h] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    rw [rest_eq_nil p1 h]
  rw [dif_neg h] at hq
  have hr := rest_next p1 h
  by_cases h1 : p1.get h = '.'
  · rw [if_pos h1] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    rw [hr, h1]
    rfl
  rw [if_neg h1] at hq
  by_cases h2 : p1.get h = '<'
  · rw [if_pos h2] at hq
    split at hq
    · cases hq
    · rename_i wi pos2 q2 hw2
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      have hr2 := wfIriS_sound _ _ _ _ _ hw2
      rw [hr, h2] at hr2 ⊢
      simp only [readGraphLabel]
      simp only [wfIriL] at hr2
      split at hr2
      · cases hr2
      · rename_i s' p' r' hi
        split at hr2
        · cases hr2
        · rename_i wi' hm
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr2
          obtain ⟨rfl, rfl, rfl⟩ := hr2
          simp only [hi, hm]
  rw [if_neg h2] at hq
  by_cases h3 : p1.get h = '_'
  · rw [if_pos h3] at hq
    split at hq
    · cases hq
    · rename_i label pos2 q2 hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      obtain ⟨⟨t, ht⟩, hr3⟩ := bnodeS_sound _ _ _ _ _ hb
      rw [ht] at hr3 ⊢
      simp only [readGraphLabel, hr3]
  rw [if_neg h3] at hq
  by_cases h4 : p1.get h = '"'
  · rw [if_pos h4] at hq; cases hq
  rw [if_neg h4] at hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl⟩ := hq
  rw [hr]
  generalize p1.get h = c at h1 h2 h3 h4
  generalize rest (p1.next h) = t
  cases c with
  | mk v hv => simp_all [Char.ext_iff]

/-! ## Statements -/

def dotS {s : String} (pos : Nat) (p : s.Pos) : Option (Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '.' then some (pos + 1, p.next h)
  else none

theorem dotS_sound {s : String} (pos : Nat) (p : s.Pos) (pos' : Nat) (q : s.Pos)
    (hq : dotS pos p = some (pos', q)) : ∃ t, rest p = '.' :: t ∧ rest q = t ∧ pos' = pos + 1 := by
  unfold dotS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  rw [dif_neg h] at hq
  by_cases h1 : p.get h = '.'
  · rw [if_pos h1] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact ⟨_, by rw [rest_next p h, h1], rfl, rfl⟩
  · rw [if_neg h1] at hq; cases hq

/-- One N-Quads line, RDF 1.1: `readNQuad11` at a cursor. -/
def nquad11S {s : String} (pos : Nat) (p : s.Pos) :
    Option (Triple × Option Subject × Nat × s.Pos) :=
  match subjectS (skipWsS pos p).1 (skipWsS pos p).2 with
  | none => none
  | some (subj, pos2, p2) =>
    match predicateS (skipWsS pos2 p2).1 (skipWsS pos2 p2).2 with
    | none => none
    | some (pred, pos4, p4) =>
      match objectS (skipWsS pos4 p4).1 (skipWsS pos4 p4).2 with
      | none => none
      | some (obj, pos6, p6) =>
        match optGraphLabelS pos6 p6 with
        | none => none
        | some (gopt, pos7, p7) =>
          match dotS (skipWsS pos7 p7).1 (skipWsS pos7 p7).2 with
          | none => none
          | some (pos9, p9) => some ({ s := subj, p := pred, o := obj }, gopt, pos9, p9)

theorem nquad11S_sound {s : String} (pos : Nat) (p : s.Pos)
    (t : Triple) (g : Option Subject) (pos' : Nat) (q : s.Pos)
    (hq : nquad11S pos p = some (t, g, pos', q)) :
    readNQuad11 pos (rest p) = .ok (t, g, pos', rest q) := by
  unfold nquad11S at hq
  split at hq
  · cases hq
  rename_i subj pos2 p2 hs
  split at hq
  · cases hq
  rename_i pred pos4 p4 hp
  split at hq
  · cases hq
  rename_i obj pos6 p6 ho
  split at hq
  · cases hq
  rename_i gopt pos7 p7 hg
  split at hq
  · cases hq
  rename_i pos9 p9 hd
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
  have w1 := skipWsS_eq pos p
  have w2 := skipWsS_eq pos2 p2
  have w3 := skipWsS_eq pos4 p4
  have w4 := skipWsS_eq pos7 p7
  generalize (skipWsS pos p).1 = a1 at *
  generalize (skipWsS pos p).2 = b1 at *
  generalize (skipWsS pos2 p2).1 = a2 at *
  generalize (skipWsS pos2 p2).2 = b2 at *
  generalize (skipWsS pos4 p4).1 = a3 at *
  generalize (skipWsS pos4 p4).2 = b3 at *
  generalize (skipWsS pos7 p7).1 = a4 at *
  generalize (skipWsS pos7 p7).2 = b4 at *
  obtain ⟨tt, hd1, hd2, hd3⟩ := dotS_sound _ _ _ _ hd
  have e1 := subjectS_sound _ _ _ _ _ hs
  have e2 := predicateS_sound _ _ _ _ _ hp
  have e3 := objectS_sound _ _ _ _ _ ho
  have e4 := optGraphLabelS_sound _ _ _ _ _ hg
  simp only [readNQuad11]
  rw [← w1]
  simp only []
  rw [e1]
  simp only []
  rw [← w2]
  simp only []
  rw [e2]
  simp only []
  rw [← w3]
  simp only []
  rw [e3]
  simp only []
  rw [e4]
  simp only []
  rw [← w4]
  simp only []
  rw [hd1, hd2, hd3]
  rfl

/-- One N-Triples line, RDF 1.1: `readTriple11` at a cursor. -/
def triple11S {s : String} (pos : Nat) (p : s.Pos) :
    Option (Triple × Nat × s.Pos) :=
  match subjectS (skipWsS pos p).1 (skipWsS pos p).2 with
  | none => none
  | some (subj, pos2, p2) =>
    match predicateS (skipWsS pos2 p2).1 (skipWsS pos2 p2).2 with
    | none => none
    | some (pred, pos4, p4) =>
      match objectS (skipWsS pos4 p4).1 (skipWsS pos4 p4).2 with
      | none => none
      | some (obj, pos6, p6) =>
        match dotS (skipWsS pos6 p6).1 (skipWsS pos6 p6).2 with
        | none => none
        | some (pos9, p9) => some ({ s := subj, p := pred, o := obj }, pos9, p9)

theorem triple11S_sound {s : String} (pos : Nat) (p : s.Pos)
    (t : Triple) (pos' : Nat) (q : s.Pos)
    (hq : triple11S pos p = some (t, pos', q)) :
    readTriple11 pos (rest p) = .ok (t, pos', rest q) := by
  unfold triple11S at hq
  split at hq
  · cases hq
  rename_i subj pos2 p2 hs
  split at hq
  · cases hq
  rename_i pred pos4 p4 hp
  split at hq
  · cases hq
  rename_i obj pos6 p6 ho
  split at hq
  · cases hq
  rename_i pos9 p9 hd
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl⟩ := hq
  have w1 := skipWsS_eq pos p
  have w2 := skipWsS_eq pos2 p2
  have w3 := skipWsS_eq pos4 p4
  have w4 := skipWsS_eq pos6 p6
  generalize (skipWsS pos p).1 = a1 at *
  generalize (skipWsS pos p).2 = b1 at *
  generalize (skipWsS pos2 p2).1 = a2 at *
  generalize (skipWsS pos2 p2).2 = b2 at *
  generalize (skipWsS pos4 p4).1 = a3 at *
  generalize (skipWsS pos4 p4).2 = b3 at *
  generalize (skipWsS pos6 p6).1 = a4 at *
  generalize (skipWsS pos6 p6).2 = b4 at *
  obtain ⟨tt, hd1, hd2, hd3⟩ := dotS_sound _ _ _ _ hd
  have e1 := subjectS_sound _ _ _ _ _ hs
  have e2 := predicateS_sound _ _ _ _ _ hp
  have e3 := objectS_sound _ _ _ _ _ ho
  simp only [readTriple11]
  rw [← w1]
  simp only []
  rw [e1]
  simp only []
  rw [← w2]
  simp only []
  rw [e2]
  simp only []
  rw [← w3]
  simp only []
  rw [e3]
  simp only []
  rw [← w4]
  simp only []
  rw [hd1, hd2, hd3]
  rfl

/-! ## The strict line walk over text -/

/-- The statement reader the text walk declines to, and the answer it gives. -/
def readerOf (quads : Bool) : LineReader :=
  if quads then quadReader .rdf11 else tripleReader .rdf11

/-- The native statement reader of a kind of document, in the shape of a `LineReader`. -/
def stmtS {s : String} (quads : Bool) (pos : Nat) (p : s.Pos) :
    Option (Triple × Option Subject × Nat × s.Pos) :=
  if quads then nquad11S pos p
  else
    match triple11S pos p with
    | none => none
    | some (t, pos', q) => some (t, none, pos', q)

theorem stmtS_sound {s : String} (quads : Bool) (pos : Nat) (p : s.Pos)
    (t : Triple) (g : Option Subject) (pos' : Nat) (q : s.Pos)
    (hq : stmtS quads pos p = some (t, g, pos', q)) :
    readerOf quads pos (rest p) = .ok (t, g, pos', rest q) := by
  unfold stmtS at hq
  cases quads
  · simp only [Bool.false_eq_true, if_false] at hq
    split at hq
    · cases hq
    · rename_i t' pos2 q2 ht
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
      simp only [readerOf, tripleReader, Bool.false_eq_true, if_false, triple11S_sound _ _ _ _ _ ht]
  · simp only [if_true] at hq
    simp only [readerOf, quadReader, if_true, nquad11S_sound _ _ _ _ _ _ hq]

/-- `foldLines` over a cursor. A round whose statement the native reader declines runs the
list walk from the start of that round on `rest p`. -/
def foldLinesS {s : String} (quads : Bool) {α : Type}
    (consume : α → Triple → Option Subject → α) :
    Nat → Nat → s.Pos → α → Except ParseError α
  | 0, pos, _, _ =>
      .error ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
  | fuel' + 1, pos, p, acc =>
      match skipWsS pos p with
      | (pos1, p1) =>
        if h : p1 = s.endPos then .ok acc
        else if p1.get h = '#' then
          match skipCommentS pos1 p1 with
          | (pos2, p2) =>
            match skipEolS pos2 p2 with
            | (pos3, p3) => foldLinesS quads consume fuel' pos3 p3 acc
        else if p1.get h = '\n' then
          match skipEolS pos1 p1 with
          | (pos2, p2) => foldLinesS quads consume fuel' pos2 p2 acc
        else if p1.get h = '\r' then
          match skipEolS pos1 p1 with
          | (pos2, p2) => foldLinesS quads consume fuel' pos2 p2 acc
        else
          match stmtS quads pos1 p1 with
          | none => foldLines (readerOf quads) consume (fuel' + 1) pos (rest p) acc
          | some (t, gopt, pos2, p2) =>
            match skipWsS pos2 p2 with
            | (pos3, p3) =>
              match skipCommentS pos3 p3 with
              | (pos4, p4) =>
                match skipEolS pos4 p4 with
                | (pos5, p5) => foldLinesS quads consume fuel' pos5 p5 (consume acc t gopt)

theorem foldLinesS_eq {s : String} (quads : Bool) {α : Type}
    (consume : α → Triple → Option Subject → α) :
    ∀ (fuel pos : Nat) (p : s.Pos) (acc : α),
      foldLinesS quads consume fuel pos p acc =
        foldLines (readerOf quads) consume fuel pos (rest p) acc := by
  intro fuel
  induction fuel with
  | zero => intro pos p acc; rfl
  | succ n ih =>
    intro pos p acc
    have e1 := skipWsS_eq pos p
    rcases hw : skipWsS pos p with ⟨pos1, p1⟩
    rw [hw] at e1
    simp only [] at e1
    simp only [foldLinesS, hw]
    rw [foldLines, ← e1]
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
      rw [ih]
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
      rw [ih]
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
      rw [ih]
      rw [hr, h3] at e3 ⊢
      rw [← e3]
      rfl
    rw [if_neg h3]
    rcases hs : stmtS quads pos1 p1 with _ | ⟨t, gopt, pos2, p2⟩
    · simp only []
    · simp only []
      have hsound := stmtS_sound _ _ _ _ _ _ _ hs
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
      rw [ih]
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

/-! ## The chunked walk over text -/

/-- What the chunked text walk keeps between chunks: the consumer's state, the partial last
line as text (it holds no line break), and the absolute offset in characters of its first
character. `LineFeed` keeps the partial line as a `List Char`, which costs about 33 bytes of
memory per character. -/
structure TextFeed (α : Type) where
  acc : α
  carryText : String := ""
  pos : Nat := 0

/-- The `LineFeed` state with the same partial line. -/
def TextFeed.toLF {α : Type} (st : TextFeed α) : LineFeed α :=
  { acc := st.acc, carryRev := st.carryText.toList.reverse, pos := st.pos }

/-- The `TextFeed` state with the same partial line. -/
def TextFeed.ofLF {α : Type} (st : LineFeed α) : TextFeed α :=
  { acc := st.acc, carryText := String.ofList st.carryRev.reverse, pos := st.pos }

theorem TextFeed.ofLF_toLF {α : Type} (st : TextFeed α) : TextFeed.ofLF st.toLF = st := by
  cases st; simp [TextFeed.toLF, TextFeed.ofLF, String.ofList_toList]

theorem TextFeed.toLF_ofLF {α : Type} (st : LineFeed α) : (TextFeed.ofLF st).toLF = st := by
  cases st; simp [TextFeed.toLF, TextFeed.ofLF, String.toList_ofList]

/-- The statement reader of a kind of document in a mode. -/
def modeReader (quads : Bool) (mode : Mode) : LineReader :=
  if quads then quadReader mode else tripleReader mode

theorem readerOf_eq (quads : Bool) : readerOf quads = modeReader quads .rdf11 := rfl

/-- Feed one chunk of text, RDF 1.1. The partial line stays text. A line that crosses a chunk
boundary is read as text; the lines of a chunk that follows no partial line are read as the
list walk reads them. -/
def TextFeed.feed11 (quads : Bool) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) (text : String) :
    Except ParseError (TextFeed α) :=
  match st with
  | { acc, carryText, pos } =>
    match splitCompleteLines text.toList with
    | ([], _) => .ok { acc := acc, carryText := carryText ++ text, pos := pos }
    | (cut, rest) =>
      if carryText.isEmpty then
        match foldLines (readerOf quads) consume (cut.length + 1) pos cut acc with
        | .ok acc' => .ok { acc := acc', carryText := String.ofList rest, pos := pos + cut.length }
        | .error e => .error e
      else
        let complete := carryText ++ String.ofList cut
        match foldLinesS quads consume (complete.length + 1) pos complete.startPos acc with
        | .ok acc' =>
            .ok { acc := acc', carryText := String.ofList rest, pos := pos + complete.length }
        | .error e => .error e

/-- Feed one chunk of text in a mode. RDF 1.2 takes the list walk. -/
def TextFeed.feed (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) (text : String) :
    Except ParseError (TextFeed α) :=
  match mode with
  | .rdf11 => TextFeed.feed11 quads consume st text
  | .rdf12 =>
    (LineFeed.feed (modeReader quads .rdf12) consume st.toLF text.toList).map TextFeed.ofLF

theorem TextFeed.feed11_eq (quads : Bool) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) (text : String) :
    TextFeed.feed11 quads consume st text =
      (LineFeed.feed (readerOf quads) consume st.toLF text.toList).map TextFeed.ofLF := by
  cases st with
  | mk acc carryText pos =>
  simp only [TextFeed.feed11, TextFeed.toLF, LineFeed.feed]
  rcases hs : splitCompleteLines text.toList with ⟨cut, rest'⟩
  cases cut with
  | nil =>
    simp only [List.reverseAux_eq, Except.map, TextFeed.ofLF, List.reverse_append,
      List.reverse_reverse, String.ofList_append, String.ofList_toList]
  | cons x xs =>
    simp only [List.reverseAux_eq, List.reverse_reverse]
    by_cases he : carryText.isEmpty = true
    · have h0 : carryText = "" := by simpa using he
      subst h0
      simp only [he, if_true, String.toList_empty, List.nil_append]
      generalize foldLines (readerOf quads) consume ((x :: xs).length + 1) pos (x :: xs) acc = r
      cases r <;> simp [TextFeed.ofLF, Except.map]
    · rw [if_neg he]
      have ht : (carryText ++ String.ofList (x :: xs)).toList = carryText.toList ++ x :: xs := by
        simp [String.toList_append, String.toList_ofList]
      have hl : (carryText ++ String.ofList (x :: xs)).length =
          (carryText.toList ++ x :: xs).length := by
        rw [← String.length_toList, ht]
      rw [foldLinesS_eq, rest_startPos, hl, ht]
      generalize foldLines (readerOf quads) consume
        ((carryText.toList ++ x :: xs).length + 1) pos (carryText.toList ++ x :: xs) acc = r
      cases r <;> simp [TextFeed.ofLF, Except.map]

theorem TextFeed.feed_eq (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) (text : String) :
    TextFeed.feed quads mode consume st text =
      (LineFeed.feed (modeReader quads mode) consume st.toLF text.toList).map TextFeed.ofLF := by
  cases mode
  · exact TextFeed.feed11_eq quads consume st text
  · rfl

/-- End of input: walk the partial last line. -/
def TextFeed.finish (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) : Except ParseError α :=
  match mode with
  | .rdf11 =>
    foldLinesS quads consume (st.carryText.length + 1) st.pos st.carryText.startPos st.acc
  | .rdf12 => LineFeed.finish (modeReader quads .rdf12) consume st.toLF

theorem TextFeed.finish_eq (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) :
    TextFeed.finish quads mode consume st =
      LineFeed.finish (modeReader quads mode) consume st.toLF := by
  cases mode
  · simp only [TextFeed.finish, LineFeed.finish, LineFeed.carry, TextFeed.toLF,
      List.reverse_reverse]
    rw [foldLinesS_eq, rest_startPos, String.length_toList]
    rfl
  · rfl


/-! ## Guards

The text walk against the list walk on documents cut into pieces of 1 to 89 characters, so
that a partial line is held across chunks and read as text. Accepted and refused documents,
every token form the native reader reads, and the forms it declines (an escape `\u`, a label
that ends in a dot). The values compared are the triples with their graph labels and the
errors, offsets included. -/

/-- The pieces of `n` characters of a text. -/
def piecesOf (n : Nat) (s : String) : List String :=
  if n = 0 then [s] else
  (List.range ((s.length + n - 1) / n)).map fun i =>
    String.ofList ((s.toList.drop (i * n)).take n)

private def collectPair (a : List (Triple × Option Subject)) (t : Triple) (g : Option Subject) :
    List (Triple × Option Subject) := (t, g) :: a

private def runText (quads : Bool) (mode : Mode) (chunks : List String) :
    Except ParseError (List (Triple × Option Subject)) :=
  match chunks.foldlM (TextFeed.feed quads mode collectPair) { acc := [] } with
  | .error e => .error e
  | .ok st => TextFeed.finish quads mode collectPair st

private def runList (quads : Bool) (mode : Mode) (chunks : List String) :
    Except ParseError (List (Triple × Option Subject)) :=
  LineFeed.run (modeReader quads mode) collectPair [] (chunks.map String.toList)

private def sameRun (quads : Bool) (mode : Mode) (doc : String) : Bool :=
  [1, 2, 3, 5, 7, 16, 89, 4096].all fun n =>
    match runText quads mode (piecesOf n doc), runList quads mode (piecesOf n doc) with
    | .ok x, .ok y => x == y
    | .error e, .error e' => e == e'
    | _, _ => false

private def docs : List String :=
  [ "<urn:s> <urn:p> <urn:o> .\n<urn:s> <urn:p> \"a\" .\n",
    "<urn:s> <urn:p> \"a\"@en .\n<urn:s> <urn:p> \"b\"^^<urn:t> .\n",
    "_:b0 <urn:p> _:b1 .\n_:b1 <urn:p> _:b2.\n_:b3 <urn:p> _:b4 . # c\n",
    "# only a comment\n\n   \n<urn:s> <urn:p> \"tab\\there \\\"q\\\" \\\\ \\n\" .\r\n",
    "<urn:s> <urn:p> \"\\u0041 \\U0001F600\" .\n<urn:\\u0041> <urn:p> <urn:o> .\n",
    "<urn:s> <urn:p> <urn:o> <urn:g> .\n_:x <urn:p> \"o\" _:g .\n",
    "<urn:s> <urn:p> \"é ü ✓ 😀\"@fr .\n<urn:é> <urn:p> <urn:o> .\n",
    "<urn:s> <urn:p> <urn:o> .\n<urn:s> <urn:p> .\n",
    "<urn:s> <urn:p> \"unterminated",
    "<urn:s> <urn:p> \"x\" .",
    "<urn:s> <urn:p> \"x\" . <urn:s> <urn:p> \"y\" .\n",
    "<s> <urn:p> <urn:o> .\n",
    "<urn:s> <urn:p> \"x\"^<urn:t> .\n",
    "<urn:s> <urn:p> \"x\" \"y\" .\n",
    String.ofList (List.replicate 300 'a') ++ "\n",
    "<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 700 'x') ++ "\"@en-US .\n" ++
      "<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 300 'y') ++ "\" <urn:g> .\n" ]

#guard docs.all fun d => sameRun true .rdf11 d
#guard docs.all fun d => sameRun false .rdf11 d
#guard docs.all fun d => sameRun true .rdf12 d
#guard docs.all fun d => sameRun false .rdf12 d

-- The native reader reads these forms (a declined form would make the guards above compare
-- the list walk with itself).
private def native (quads : Bool) (line : String) : Bool :=
  (stmtS quads 0 line.startPos).isSome

#guard native true "<urn:s> <urn:p> <urn:o> .\n"
#guard native true "<urn:s> <urn:p> \"a\" <urn:g> .\n"
#guard native true "_:s <urn:p> \"a\"@en _:g .\n"
#guard native true "<urn:s> <urn:p> \"a\"^^<urn:t> .\n"
#guard native true "<urn:s> <urn:p> \"a\\n\\t\\\"b\" .\n"
#guard native false ("<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 100000 'x') ++ "\" .\n")
#guard !native true "<urn:s> <urn:p> \"\\u0041\" .\n"
#guard !native true "<urn:s> <urn:p> _:b. \n"
#guard !native true "<urn:s> <urn:p> .\n"

#print axioms skipWsS_eq
#print axioms iriBodyS_sound
#print axioms litBodyS_sound
#print axioms bnodeS_sound
#print axioms literalS_sound
#print axioms nquad11S_sound
#print axioms triple11S_sound
#print axioms stmtS_sound
#print axioms foldLinesS_eq
#print axioms TextFeed.feed_eq
#print axioms TextFeed.finish_eq

end L4Factoidal.Syntax.StrictFeedText
