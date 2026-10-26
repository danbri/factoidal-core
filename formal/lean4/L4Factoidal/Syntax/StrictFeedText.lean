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
* The readers cover RDF 1.1 and RDF 1.2 (`Mode`): IRIs, blank node labels (a label that ends
  in a dot gives the dot back, `bnodeRunS`), literals with ECHAR and UCHAR escapes (`escS`),
  language tags with an RDF 1.2 base direction, white space before `@` and `^^` in RDF 1.2,
  and triple terms nested to any depth with the open terms in a list (`object12DownS`, a
  tail call per level, as `readObject12Down`)
  (https://github.com/danbri/factoidal/issues/949).
* A native reader DECLINES (`none`) on an error and on an escape inside an IRIREF. The walk
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

theorem next_rb {s : String} (p : s.Pos) (h : p ≠ s.endPos) :
    (p.next h).remainingBytes < p.remainingBytes := by
  simp [← String.Pos.lt_iff_remainingBytes_lt]

/-- Four characters at `p`, and the cursor after them. -/
def take4S {s : String} (p : s.Pos) : Option (Char × Char × Char × Char × s.Pos) :=
  if h0 : p = s.endPos then none else
  if h1 : p.next h0 = s.endPos then none else
  if h2 : (p.next h0).next h1 = s.endPos then none else
  if h3 : ((p.next h0).next h1).next h2 = s.endPos then none else
  some (p.get h0, (p.next h0).get h1, ((p.next h0).next h1).get h2,
        (((p.next h0).next h1).next h2).get h3, (((p.next h0).next h1).next h2).next h3)

theorem take4S_sound {s : String} (p : s.Pos) (a b c d : Char) (q : s.Pos)
    (hq : take4S p = some (a, b, c, d, q)) :
    rest p = a :: b :: c :: d :: rest q ∧ q.remainingBytes < p.remainingBytes := by
  unfold take4S at hq
  split at hq; · cases hq
  rename_i h0
  split at hq; · cases hq
  rename_i h1
  split at hq; · cases hq
  rename_i h2
  split at hq; · cases hq
  rename_i h3
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hq
  refine ⟨?_, ?_⟩
  · rw [rest_next p h0, rest_next _ h1, rest_next _ h2, rest_next _ h3]
  · have := next_rb p h0; have := next_rb _ h1; have := next_rb _ h2; have := next_rb _ h3
    omega

theorem strLitNextStep_u (pos : Nat) (a b c d : Char) (t : List Char) (cp : Nat) (ch : Char)
    (hh : hex4 a b c d = some cp) (hc : codepointToChar cp pos = .ok ch) :
    strLitNextStep pos ('\\' :: 'u' :: a :: b :: c :: d :: t) = .emit ch 6 t := by
  simp [strLitNextStep, hh, strLitEmitAt, hc]

theorem strLitNextStep_U (pos : Nat) (a b c d e f g h : Char) (t : List Char) (cp : Nat)
    (ch : Char) (hh : hex8 a b c d e f g h = some cp) (hc : codepointToChar cp pos = .ok ch) :
    strLitNextStep pos ('\\' :: 'U' :: a :: b :: c :: d :: e :: f :: g :: h :: t) =
      .emit ch 10 t := by
  simp [strLitNextStep, hh, strLitEmitAt, hc]

/-- The escape at `p` (a backslash): ECHAR or UCHAR, decoded. Declines on what the list
reader refuses. -/
def escS {s : String} (pos : Nat) (p : s.Pos) : Option (Char × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '\\' then
    if h1 : p.next h = s.endPos then none
    else if (p.next h).get h1 = 'u' then
      match take4S ((p.next h).next h1) with
      | none => none
      | some (a, b, c, d, q) =>
        match hex4 a b c d with
        | none => none
        | some cp =>
          match codepointToChar cp pos with
          | .error _ => none
          | .ok ch => some (ch, 6, q)
    else if (p.next h).get h1 = 'U' then
      match take4S ((p.next h).next h1) with
      | none => none
      | some (a, b, c, d, q1) =>
        match take4S q1 with
        | none => none
        | some (e, f, g, k, q) =>
          match hex8 a b c d e f g k with
          | none => none
          | some cp =>
            match codepointToChar cp pos with
            | .error _ => none
            | .ok ch => some (ch, 10, q)
    else
      match echar? ((p.next h).get h1) with
      | some d => some (d, 2, (p.next h).next h1)
      | none => none
  else none

theorem escS_sound {s : String} (pos : Nat) (p : s.Pos) (ch : Char) (w : Nat) (q : s.Pos)
    (hq : escS pos p = some (ch, w, q)) :
    strLitNextStep pos (rest p) = .emit ch w (rest q) ∧
      q.remainingBytes < p.remainingBytes := by
  unfold escS at hq
  split at hq; · cases hq
  rename_i h
  split at hq
  case isFalse => cases hq
  rename_i hb
  split at hq; · cases hq
  rename_i h1
  have hr : rest p = '\\' :: (p.next h).get h1 :: rest ((p.next h).next h1) := by
    rw [rest_next p h, rest_next _ h1, hb]
  have l1 := next_rb p h
  have l2 := next_rb _ h1
  split at hq
  · rename_i hu
    split at hq; · cases hq
    rename_i a b c d q4 ht
    split at hq; · cases hq
    rename_i cp hh
    split at hq; · cases hq
    rename_i ch' hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    obtain ⟨ht1, ht2⟩ := take4S_sound _ _ _ _ _ _ ht
    rw [hr, hu, ht1]
    exact ⟨strLitNextStep_u _ _ _ _ _ _ _ _ hh hc, by omega⟩
  split at hq
  · rename_i hu' hU
    split at hq; · cases hq
    rename_i a b c d q4 ht
    split at hq; · cases hq
    rename_i e f g k q8 ht'
    split at hq; · cases hq
    rename_i cp hh
    split at hq; · cases hq
    rename_i ch' hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    obtain ⟨ht1, ht2⟩ := take4S_sound _ _ _ _ _ _ ht
    obtain ⟨ht1', ht2'⟩ := take4S_sound _ _ _ _ _ _ ht'
    rw [hr, hU, ht1, ht1']
    exact ⟨strLitNextStep_U _ _ _ _ _ _ _ _ _ _ _ _ hh hc, by omega⟩
  · split at hq
    · rename_i d hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      rw [hr]
      exact ⟨strLitNextStep_echar _ _ hd, by omega⟩
    · cases hq

/-- The literal body from `p`: plain characters and escapes up to `"`. Declines on what the
list reader refuses. -/
def litBodyS {s : String} (pos : Nat) (acc : String) (p : s.Pos) :
    Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '"' then some (acc, pos + 1, p.next h)
  else if litPlain (p.get h) then litBodyS (pos + 1) (acc.push (p.get h)) (p.next h)
  else
    match _he : escS pos p with
    | some (c, w, q) => litBodyS (pos + w) (acc.push c) q
    | none => none
termination_by p.remainingBytes
decreasing_by
  · exact next_rb p h
  · exact (escS_sound _ _ _ _ _ _he).2

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
  | case4 pos acc p h hg hp c w q2 he ih =>
    rw [litBodyS, dif_neg h, if_neg hg, if_neg hp] at hq
    split at hq
    · rename_i c' w' q' he'
      rw [he] at he'
      simp only [Option.some.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl, rfl⟩ := he'
      rw [readStringLiteralBodyGo_emit _ _ _ _ _ _ (escS_sound _ _ _ _ _ he).1]
      exact ih str pos' q hq
    · rename_i he'; rw [he] at he'; cases he'
  | case5 pos acc p h hg hp he =>
    rw [litBodyS, dif_neg h, if_neg hg, if_neg hp] at hq
    split at hq
    · rename_i c' w' q' he'; rw [he] at he'; cases he'
    · cases hq

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

/-! ## Blank node label with a final dot -/

/-- A label run without its final dot, as `readBlankNodeLabel` cuts it. -/
def trimDot (l : List Char) : List Char :=
  match l.getLast? with
  | some '.' => l.dropLast
  | _ => l

/-- The label run ends in a dot, which `readBlankNodeLabel` gives back to the input. -/
def endsDot (l : List Char) : Bool :=
  match l.getLast? with
  | some '.' => true
  | _ => false

theorem trimDot_nil : trimDot [] = [] := rfl
theorem endsDot_nil : endsDot [] = false := rfl
theorem trimDot_dot : trimDot ['.'] = [] := rfl
theorem endsDot_dot : endsDot ['.'] = true := rfl

theorem trimDot_cons_cons (x y : Char) (b : List Char) :
    trimDot (x :: y :: b) = x :: trimDot (y :: b) := by
  unfold trimDot
  rw [List.getLast?_cons_cons]
  split <;> simp_all

theorem endsDot_cons_cons (x y : Char) (b : List Char) :
    endsDot (x :: y :: b) = endsDot (y :: b) := by
  unfold endsDot
  rw [List.getLast?_cons_cons]

theorem trimDot_single {x : Char} (hx : x ≠ '.') : trimDot [x] = [x] := by
  unfold trimDot; simp [hx]

theorem endsDot_single {x : Char} (hx : x ≠ '.') : endsDot [x] = false := by
  unfold endsDot; simp [hx]

theorem trimDot_cons {x : Char} (b : List Char) (hx : x ≠ '.') :
    trimDot (x :: b) = x :: trimDot b := by
  cases b with
  | nil => rw [trimDot_single hx, trimDot_nil]
  | cons y b => exact trimDot_cons_cons x y b

theorem endsDot_cons {x : Char} (b : List Char) (hx : x ≠ '.') :
    endsDot (x :: b) = endsDot b := by
  cases b with
  | nil => rw [endsDot_single hx, endsDot_nil]
  | cons y b => exact endsDot_cons_cons x y b

/-- The run of label characters from `p`, as `readBlankNodeLabel` keeps it: a dot is taken
only when a label character follows it, so a final dot stays in the input. -/
def bnodeRunS {s : String} (n : Nat) (acc : String) (p : s.Pos) : Nat × String × s.Pos :=
  if h : p = s.endPos then (n, acc, p)
  else if p.get h = '.' then
    if h1 : p.next h = s.endPos then (n, acc, p)
    else if isBnodeChar ((p.next h).get h1) then bnodeRunS (n + 1) (acc.push '.') (p.next h)
    else (n, acc, p)
  else if isBnodeChar (p.get h) then bnodeRunS (n + 1) (acc.push (p.get h)) (p.next h)
  else (n, acc, p)
termination_by p.remainingBytes
decreasing_by all_goals exact next_rb p h

theorem dot_isBnodeChar : isBnodeChar '.' = true := by decide

theorem bnodeRunS_eq {s : String} (n : Nat) (acc : String) (p : s.Pos) :
    ∃ b a, (rest p).span isBnodeChar = (b, a) ∧
      (bnodeRunS n acc p).1 = n + (trimDot b).length ∧
      (bnodeRunS n acc p).2.1.toList = acc.toList ++ trimDot b ∧
      rest (bnodeRunS n acc p).2.2 = (if endsDot b then '.' :: a else a) := by
  induction n, acc, p using bnodeRunS.induct with
  | case1 n acc =>
    refine ⟨[], [], ?_, ?_, ?_, ?_⟩ <;>
      simp [bnodeRunS, rest_endPos, span_nil, trimDot_nil, endsDot_nil]
  | case2 n acc p h hd h1 =>
    have hr : rest p = ['.'] := by rw [rest_next p h, hd, rest_eq_nil _ h1]
    refine ⟨['.'], [], ?_, ?_, ?_, ?_⟩
    · rw [hr, span_cons_pos _ _ dot_isBnodeChar, span_nil]
    · rw [bnodeRunS, dif_neg h, if_pos hd, dif_pos h1, trimDot_dot]; rfl
    · rw [bnodeRunS, dif_neg h, if_pos hd, dif_pos h1, trimDot_dot]; simp
    · rw [bnodeRunS, dif_neg h, if_pos hd, dif_pos h1, endsDot_dot, hr]; rfl
  | case3 n acc p h hd h1 hb ih =>
    obtain ⟨b, a, hs, e1, e2, e3⟩ := ih
    have hr : rest p = '.' :: rest (p.next h) := by rw [rest_next p h, hd]
    have hr1 := rest_next (p.next h) h1
    rw [hr1, span_cons_pos _ _ hb] at hs
    have hb' : b = (p.next h).get h1 :: (List.span isBnodeChar (rest ((p.next h).next h1))).1 := by
      simp only [Prod.mk.injEq] at hs; exact hs.1.symm
    rw [bnodeRunS, dif_neg h, if_pos hd, dif_neg h1, if_pos hb]
    refine ⟨'.' :: b, a, ?_, ?_, ?_, ?_⟩
    · rw [hr, span_cons_pos _ _ dot_isBnodeChar, hr1, span_cons_pos _ _ hb, hs]
    · rw [e1, hb', trimDot_cons_cons]; simp; omega
    · rw [e2, hb', trimDot_cons_cons]; simp
    · rw [e3, hb', endsDot_cons_cons]
  | case4 n acc p h hd h1 hb =>
    have hr : rest p = '.' :: (p.next h).get h1 :: rest ((p.next h).next h1) := by
      rw [rest_next p h, hd, rest_next _ h1]
    rw [bnodeRunS, dif_neg h, if_pos hd, dif_neg h1, if_neg hb]
    refine ⟨['.'], (p.next h).get h1 :: rest ((p.next h).next h1), ?_, ?_, ?_, ?_⟩
    · rw [hr, span_cons_pos _ _ dot_isBnodeChar, span_cons_neg _ _ (by simpa using hb)]
    · rw [trimDot_dot]; rfl
    · rw [trimDot_dot]; simp
    · rw [endsDot_dot, hr]; rfl
  | case5 n acc p h hd hb ih =>
    obtain ⟨b, a, hs, e1, e2, e3⟩ := ih
    rw [bnodeRunS, dif_neg h, if_neg hd, if_pos hb]
    refine ⟨p.get h :: b, a, ?_, ?_, ?_, ?_⟩
    · rw [rest_next p h, span_cons_pos _ _ hb, hs]
    · rw [e1, trimDot_cons _ hd]; simp; omega
    · rw [e2, trimDot_cons _ hd]; simp
    · rw [e3, endsDot_cons _ hd]
  | case6 n acc p h hd hb =>
    rw [bnodeRunS, dif_neg h, if_neg hd, if_neg hb]
    refine ⟨[], rest p, ?_, ?_, ?_, ?_⟩
    · rw [rest_next p h, span_cons_neg _ _ (by simpa using hb)]
    · simp [trimDot_nil]
    · simp [trimDot_nil]
    · simp [endsDot_nil]

theorem labelMatch (l a : List Char) (pos : Nat) :
    (match l.getLast? with
      | some '.' =>
        (Except.ok (String.ofList l.dropLast, pos + 2 + l.dropLast.length, '.' :: a) :
          Except ParseError (String × Nat × List Char))
      | _ => .ok (String.ofList l, pos + 2 + l.length, a)) =
      .ok (String.ofList (trimDot l), pos + 2 + (trimDot l).length,
        if endsDot l then '.' :: a else a) := by
  unfold trimDot endsDot
  split <;> simp_all

theorem bnodeStart_ne_dot {c : Char} (h : isBnodeStartChar c = true) : c ≠ '.' := by
  intro hc; subst hc; revert h; decide

/-- `_:` and a label; a final dot stays in the input. -/
def bnodeS {s : String} (pos : Nat) (p : s.Pos) : Option (String × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '_' then
    if hq : p.next h = s.endPos then none
    else if (p.next h).get hq = ':' then
      if hr : (p.next h).next hq = s.endPos then none
      else if isBnodeStartChar (((p.next h).next hq).get hr) then
        match bnodeRunS 1 ("".push (((p.next h).next hq).get hr)) (((p.next h).next hq).next hr) with
        | (n, label, e) => some (label, pos + 2 + n, e)
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
  have hc0 := bnodeStart_ne_dot h3
  have hrest : rest p = '_' :: ':' :: (((p.next h).next hq1).get hr :: rest (((p.next h).next hq1).next hr)) := by
    rw [rest_next p h, rest_next (p.next h) hq1, rest_next ((p.next h).next hq1) hr, h1, h2]
  generalize ((p.next h).next hq1).get hr = c0 at hq h3 hc0 hrest
  generalize ((p.next h).next hq1).next hr = p3 at hq hrest
  refine ⟨⟨_, hrest⟩, ?_⟩
  obtain ⟨b, a, hs, e1, e2, e3⟩ := bnodeRunS_eq 1 ("".push c0) p3
  rcases hrun : bnodeRunS 1 ("".push c0) p3 with ⟨n, lab, e⟩
  rw [hrun] at hq e1 e2 e3
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl⟩ := hq
  simp only at e1 e2 e3
  rw [hrest]
  simp only [readBlankNodeLabel, h3, Bool.not_true, Bool.false_eq_true, if_false, hs]
  refine (labelMatch (c0 :: b) a pos).trans ?_
  rw [trimDot_cons b hc0, endsDot_cons b hc0, e3, e1]
  have : String.ofList (c0 :: trimDot b) = lab := by
    rw [← String.ofList_toList (s := lab), e2]; simp
  rw [this]; simp; omega


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

/-! ## RDF 1.2: language tag with a base direction -/

/-- What `readLangDir12` does with the run of tag characters: the language tag and the base
direction. -/
def langDirCore (pos : Nat) (raw : String) : Except ParseError (String × Option Bool) :=
  match splitOnDoubleHyphen raw.toList [] with
  | (ltChars, dirOpt) =>
    if !validLangSubtags ltChars 0 then .error ⟨"invalid language tag", pos⟩
    else
      match dirOpt with
      | none => .ok (String.ofList ltChars, none)
      | some dchars =>
          if dchars = ['l', 't', 'r'] then .ok (String.ofList ltChars, some false)
          else if dchars = ['r', 't', 'l'] then .ok (String.ofList ltChars, some true)
          else .error ⟨"invalid base direction (expected ltr or rtl)", pos⟩

theorem readLangDir12_core (pos : Nat) {c1 : Char} (t : List Char) (h : isLangStart c1 = true) :
    readLangDir12 pos ('@' :: c1 :: t) =
      match langDirCore pos (readLangTagRun (pos + 1) (c1 :: t)).1 with
      | .error e => .error e
      | .ok v => .ok (v, (readLangTagRun (pos + 1) (c1 :: t)).2.1,
                      (readLangTagRun (pos + 1) (c1 :: t)).2.2) := by
  simp only [readLangDir12, h, Bool.not_true, Bool.false_eq_true, if_false]
  generalize readLangTagRun (pos + 1) (c1 :: t) = r
  rcases r with ⟨raw, pos', rest'⟩
  simp only [langDirCore]
  generalize splitOnDoubleHyphen raw.toList [] = sp
  rcases sp with ⟨lt, d⟩
  simp only []
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all

/-- `@`, a language tag and an optional `--ltr` or `--rtl`, RDF 1.2. -/
def langDir12S {s : String} (pos : Nat) (p : s.Pos) :
    Option ((String × Option Bool) × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '@' then
    if hq : p.next h = s.endPos then none
    else if isLangStart ((p.next h).get hq) then
      match runS isLangChar 0 "" (p.next h) with
      | (n, raw, q) =>
        match langDirCore pos raw with
        | .error _ => none
        | .ok v => some (v, pos + 1 + n, q)
    else none
  else none

theorem langDir12S_sound {s : String} (pos : Nat) (p : s.Pos)
    (v : String × Option Bool) (pos' : Nat) (q : s.Pos)
    (hq : langDir12S pos p = some (v, pos', q)) :
    (∃ t, rest p = '@' :: t) ∧ readLangDir12 pos (rest p) = .ok (v, pos', rest q) := by
  unfold langDir12S at hq
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
  rcases hrun : runS isLangChar 0 "" (p.next h) with ⟨n, raw, e⟩
  rw [hrun] at hq hspan hn hs
  simp only at hq hspan hn hs
  have hrest' := rest_next (p.next h) hq1
  rw [hrest, readLangDir12_core _ _ h2, ← hrest']
  have hraw : String.ofList run = raw := by
    rw [← String.ofList_toList (s := raw), hs]; simp
  simp only [readLangTagRun, hspan, hraw]
  split at hq
  · cases hq
  · rename_i v' hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    simp only [hn, Nat.zero_add]

/-! ## RDF 1.2: datatype with white space -/

/-- `^^`, white space, an IRIREF: `readDatatypeWs12` at a cursor. -/
def datatypeWs12S {s : String} (pos : Nat) (p : s.Pos) : Option (WfIri × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '^' then
    if hq : p.next h = s.endPos then none
    else if (p.next h).get hq = '^' then
      match skipWsS (pos + 2) ((p.next h).next hq) with
      | (pos2, p2) =>
        match iriRefS pos2 p2 with
        | none => none
        | some (str, pos', q) =>
            match mkIri pos str with
            | .error _ => none
            | .ok wi => some (wi, pos', q)
    else none
  else none

theorem datatypeWs12S_sound {s : String} (pos : Nat) (p : s.Pos)
    (wi : WfIri) (pos' : Nat) (q : s.Pos) (hq : datatypeWs12S pos p = some (wi, pos', q)) :
    (∃ t, rest p = '^' :: '^' :: t) ∧ readDatatypeWs12 pos (rest p) = .ok (wi, pos', rest q) := by
  unfold datatypeWs12S at hq
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
  have hw := skipWsS_eq (pos + 2) ((p.next h).next hq1)
  rcases hws : skipWsS (pos + 2) ((p.next h).next hq1) with ⟨pos2, p2⟩
  rw [hws] at hq hw
  simp only at hq hw
  simp only [readDatatypeWs12, ← hw]
  split at hq
  · cases hq
  · rename_i str pos3 q3 hi
    split at hq
    · cases hq
    · rename_i wi' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      simp only [iriRefS_sound _ _ _ _ _ hi, hm]

/-! ## RDF 1.2: literal -/

theorem skipWs_cases (n : Nat) (r : List Char) :
    (skipWs n r).2 = r ∨ ∃ c t, r = c :: t ∧ isNtWs c = true := by
  cases r with
  | nil => left; rw [skipWs_nil]
  | cons c t =>
    by_cases hc : isNtWs c = true
    · right; exact ⟨c, t, rfl, hc⟩
    · left; rw [skipWs_nows n t (by simpa using hc)]

theorem isNtWs_ne_at {c : Char} (h : isNtWs c = true) : c ≠ '@' := by
  intro hc; subst hc; revert h; decide

theorem isNtWs_ne_caret {c : Char} (h : isNtWs c = true) : c ≠ '^' := by
  intro hc; subst hc; revert h; decide

/-- The RDF 1.2 literal after its body: an `@` tag or a `^^` datatype, either after white
space; else `xsd:string`, white space left in the input. -/
def lit12Tail (lex : String) (pos1 : Nat) (r : List Char) :
    Except ParseError (WfLiteral × Nat × List Char) :=
  match skipWs pos1 r with
  | (pw, rw) =>
    match rw with
    | '@' :: _ =>
        match readLangDir12 pw rw with
        | .error e => .error e
        | .ok ((tag, dopt), pos2, rest2) =>
            match mkLiteral pw
                { lexicalForm := lex,
                  datatype := (match dopt with
                    | none => rdfLangString
                    | some _ => rdfDirLangString),
                  langTag := some tag,
                  direction := dopt.map (fun b => if b then TextDirection.rtl else TextDirection.ltr) } with
            | .error e => .error e
            | .ok wl => .ok (wl, pos2, rest2)
    | '^' :: '^' :: _ =>
        match readDatatypeWs12 pw rw with
        | .error e => .error e
        | .ok (dt, pos2, rest2) =>
            match mkLiteral pw
                { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
            | .error e => .error e
            | .ok wl => .ok (wl, pos2, rest2)
    | _ =>
        match mkLiteral pos1
            { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none } with
        | .error e => .error e
        | .ok wl => .ok (wl, pos1, r)

theorem readLiteral12_eq (pos : Nat) (cs : List Char) :
    readLiteral .rdf12 pos cs =
      match readStringLiteralQuoted pos cs with
      | .error e => .error e
      | .ok (lex, pos1, r) => lit12Tail lex pos1 r := by
  unfold readLiteral
  cases hr : readStringLiteralQuoted pos cs with
  | error e => rfl
  | ok v =>
    rcases v with ⟨lex, pos1, r⟩
    simp only [lit12Tail]
    have hc := skipWs_cases pos1 r
    rcases hsw : skipWs pos1 r with ⟨pw, rw⟩
    rw [hsw] at hc
    simp only at hc ⊢
    rcases hc with rfl | ⟨c, t, rfl, hws⟩
    · rcases rw with _ | ⟨c, t⟩
      · rfl
      by_cases hc : c = '@'
      · subst hc; rfl
      by_cases hc2 : c = '^'
      · subst hc2
        rcases t with _ | ⟨d, t⟩
        · rfl
        by_cases hd : d = '^'
        · subst hd; rfl
        · (split <;> (try simp_all)) <;> rfl
      · (split <;> (try simp_all)) <;> rfl
    · have h1 := isNtWs_ne_at hws
      have h2 := isNtWs_ne_caret hws
      rcases rw with _ | ⟨e, u⟩
      · (split <;> (try simp_all)) <;> rfl
      by_cases he : e = '@'
      · subst he; rfl
      by_cases he2 : e = '^'
      · subst he2
        rcases u with _ | ⟨d, u⟩
        · (split <;> (try simp_all)) <;> rfl
        by_cases hd : d = '^'
        · subst hd; rfl
        · (split <;> (try simp_all)) <;> rfl
      · (split <;> (try simp_all)) <;> rfl

/-- A literal, RDF 1.2: `readLiteral .rdf12` at a cursor. -/
def literal12S {s : String} (pos : Nat) (p : s.Pos) : Option (WfLiteral × Nat × s.Pos) :=
  match litQuotedS pos p with
  | none => none
  | some (lex, pos1, q1) =>
    match skipWsS pos1 q1 with
    | (pw, qw) =>
      if h : qw = s.endPos then plainLiteralS lex pos1 q1
      else if qw.get h = '@' then
        match langDir12S pw qw with
        | none => none
        | some ((tag, dopt), pos2, q2) =>
          match mkLiteral pw
              { lexicalForm := lex,
                datatype := (match dopt with
                  | none => rdfLangString
                  | some _ => rdfDirLangString),
                langTag := some tag,
                direction := dopt.map (fun b => if b then TextDirection.rtl else TextDirection.ltr) } with
          | .error _ => none
          | .ok wl => some (wl, pos2, q2)
      else if qw.get h = '^' then
        if h2 : qw.next h = s.endPos then plainLiteralS lex pos1 q1
        else if (qw.next h).get h2 = '^' then
          match datatypeWs12S pw qw with
          | none => none
          | some (dt, pos2, q2) =>
            match mkLiteral pw
                { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
            | .error _ => none
            | .ok wl => some (wl, pos2, q2)
        else plainLiteralS lex pos1 q1
      else plainLiteralS lex pos1 q1

theorem plainLiteralS_tail {s : String} (lex : String) (pos1 : Nat) (q1 : s.Pos)
    (wl : WfLiteral) (pos' : Nat) (q : s.Pos) (hq : plainLiteralS lex pos1 q1 = some (wl, pos', q))
    (r : List Char) (hr : r = rest q1) :
    (match mkLiteral pos1
        { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none } with
      | .error e => Except.error e
      | .ok wl => (.ok (wl, pos1, r) : Except ParseError (WfLiteral × Nat × List Char))) =
      .ok (wl, pos', rest q) := by
  unfold plainLiteralS at hq
  split at hq
  · cases hq
  · rename_i wl' hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    simp only [hr]

theorem literal12S_sound {s : String} (pos : Nat) (p : s.Pos)
    (wl : WfLiteral) (pos' : Nat) (q : s.Pos) (hq : literal12S pos p = some (wl, pos', q)) :
    readLiteral .rdf12 pos (rest p) = .ok (wl, pos', rest q) := by
  unfold literal12S at hq
  split at hq
  · cases hq
  rename_i lex pos1 q1 hlq
  rw [readLiteral12_eq, litQuotedS_sound _ _ _ _ _ hlq]
  simp only [lit12Tail]
  have hw := skipWsS_eq pos1 q1
  rcases hws : skipWsS pos1 q1 with ⟨pw, qw⟩
  rw [hws] at hq hw
  simp only at hq hw
  rw [← hw]
  simp only []
  by_cases h : qw = s.endPos
  · rw [dif_pos h] at hq
    rw [rest_eq_nil qw h]
    exact plainLiteralS_tail _ _ _ _ _ _ hq _ rfl
  rw [dif_neg h] at hq
  have hr := rest_next qw h
  by_cases h1 : qw.get h = '@'
  · rw [if_pos h1] at hq
    split at hq
    · cases hq
    rename_i tag dopt pos2 q2 hl
    obtain ⟨⟨t, ht⟩, hl'⟩ := langDir12S_sound _ _ _ _ _ hl
    rw [ht]
    simp only []
    rw [← ht, hl']
    simp only []
    split at hq
    · cases hq
    · rename_i wl' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      rfl
  rw [if_neg h1] at hq
  by_cases h2 : qw.get h = '^'
  · rw [if_pos h2] at hq
    by_cases h3 : qw.next h = s.endPos
    · rw [dif_pos h3] at hq
      rw [hr, h2, rest_eq_nil _ h3]
      exact plainLiteralS_tail _ _ _ _ _ _ hq _ rfl
    rw [dif_neg h3] at hq
    by_cases h4 : (qw.next h).get h3 = '^'
    · rw [if_pos h4] at hq
      split at hq
      · cases hq
      rename_i dt pos2 q2 hd
      obtain ⟨⟨t, ht⟩, hd'⟩ := datatypeWs12S_sound _ _ _ _ _ hd
      rw [ht]
      simp only []
      rw [← ht, hd']
      simp only []
      split at hq
      · cases hq
      · rename_i wl' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl, rfl⟩ := hq
        rfl
    · rw [if_neg h4] at hq
      rw [hr, h2, rest_next _ h3]
      have := plainLiteralS_tail _ _ _ _ _ _ hq (rest q1) rfl
      generalize (qw.next h).get h3 = d at h4
      split
      · rename_i heq; simp at heq
      · rename_i heq; simp at heq; exact absurd heq.1 h4
      · exact this
  rw [if_neg h2] at hq
  rw [hr]
  have := plainLiteralS_tail _ _ _ _ _ _ hq (rest q1) rfl
  generalize qw.get h = c at h1 h2
  split
  · rename_i heq; simp at heq; exact absurd heq.1 h1
  · rename_i heq; simp at heq; exact absurd heq.1 h2
  · exact this

/-! ## RDF 1.2: object, with triple terms -/

/-- `<<(` at `p`, and the cursor after it. -/
def open3S {s : String} (p : s.Pos) : Option s.Pos :=
  if h : p = s.endPos then none
  else if p.get h = '<' then
    if h1 : p.next h = s.endPos then none
    else if (p.next h).get h1 = '<' then
      if h2 : (p.next h).next h1 = s.endPos then none
      else if ((p.next h).next h1).get h2 = '(' then some (((p.next h).next h1).next h2)
      else none
    else none
  else none

theorem open3S_sound {s : String} (p q : s.Pos) (hq : open3S p = some q) :
    rest p = '<' :: '<' :: '(' :: rest q := by
  unfold open3S at hq
  split at hq; · cases hq
  rename_i h
  split at hq
  case isFalse => cases hq
  rename_i ha
  split at hq; · cases hq
  rename_i h1
  split at hq
  case isFalse => cases hq
  rename_i hb
  split at hq; · cases hq
  rename_i h2
  split at hq
  case isFalse => cases hq
  rename_i hc
  simp only [Option.some.injEq] at hq
  subst hq
  rw [rest_next p h, rest_next _ h1, rest_next _ h2, ha, hb, hc]

/-- `)>>` at `p`, and the cursor after it. -/
def close3S {s : String} (p : s.Pos) : Option s.Pos :=
  if h : p = s.endPos then none
  else if p.get h = ')' then
    if h1 : p.next h = s.endPos then none
    else if (p.next h).get h1 = '>' then
      if h2 : (p.next h).next h1 = s.endPos then none
      else if ((p.next h).next h1).get h2 = '>' then some (((p.next h).next h1).next h2)
      else none
    else none
  else none

theorem close3S_sound {s : String} (p q : s.Pos) (hq : close3S p = some q) :
    rest p = ')' :: '>' :: '>' :: rest q := by
  unfold close3S at hq
  split at hq; · cases hq
  rename_i h
  split at hq
  case isFalse => cases hq
  rename_i ha
  split at hq; · cases hq
  rename_i h1
  split at hq
  case isFalse => cases hq
  rename_i hb
  split at hq; · cases hq
  rename_i h2
  split at hq
  case isFalse => cases hq
  rename_i hc
  simp only [Option.some.injEq] at hq
  subst hq
  rw [rest_next p h, rest_next _ h1, rest_next _ h2, ha, hb, hc]

/-- `closeObject12` at a cursor: each open triple term takes the object, white space and
`)>>`, innermost first. A tail call for each. -/
def closeS {s : String} : OpenTerms12 → Term → Nat → s.Pos → Option (Term × Nat × s.Pos)
  | [], obj, n, q => some (obj, n, q)
  | (subj, pred) :: opens, obj, n, q =>
    match skipWsS n q with
    | (p7, q7) =>
      match close3S q7 with
      | none => none
      | some q8 => closeS opens (.tripleTerm subj pred obj) (p7 + 3) q8

theorem closeS_sound {s : String} :
    ∀ (opens : OpenTerms12) (obj : Term) (n : Nat) (q : s.Pos) (v : Term) (n' : Nat) (q' : s.Pos),
      closeS opens obj n q = some (v, n', q') →
        closeObject12 opens (.ok (obj, n, rest q)) = .ok (v, n', rest q')
  | [], obj, n, q, v, n', q', h => by
      simp only [closeS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | (subj, pred) :: opens, obj, n, q, v, n', q', h => by
      unfold closeS at h
      have hw := skipWsS_eq n q
      rcases hws : skipWsS n q with ⟨p7, q7⟩
      rw [hws] at h hw
      simp only at h hw
      split at h
      · cases h
      rename_i q8 hc
      simp only [closeObject12]
      rw [← hw]
      simp only []
      rw [close3S_sound _ _ hc]
      exact closeS_sound opens _ _ _ _ _ _ h

/-- An object that is not a triple term, RDF 1.2: IRI, blank node or literal. Declines on a
triple term and on what the list reader refuses. -/
def object12LeafS {s : String} (pos : Nat) (p : s.Pos) : Option (Term × Nat × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = '<' then
    if h1 : p.next h = s.endPos then none
    else if (p.next h).get h1 = '<' then none
    else
      match wfIriS pos p with
      | none => none
      | some (wi, pos', q) => some (.iri wi, pos', q)
  else if p.get h = '_' then
    match bnodeS pos p with
    | none => none
    | some (label, pos', q) => some (.bnode label, pos', q)
  else if p.get h = '"' then
    match literal12S pos p with
    | none => none
    | some (wl, pos', q) => some (.literal wl, pos', q)
  else none

theorem object12LeafS_sound {s : String} (f pos : Nat) (p : s.Pos)
    (v : Term) (pos' : Nat) (q : s.Pos) (hq : object12LeafS pos p = some (v, pos', q)) :
    readObject12 (f + 1) pos (rest p) = .ok (v, pos', rest q) := by
  unfold object12LeafS at hq
  by_cases h : p = s.endPos
  · rw [dif_pos h] at hq; cases hq
  rw [dif_neg h] at hq
  by_cases h1 : p.get h = '<'
  · rw [if_pos h1] at hq
    by_cases h2 : p.next h = s.endPos
    · rw [dif_pos h2] at hq; cases hq
    rw [dif_neg h2] at hq
    by_cases h3 : (p.next h).get h2 = '<'
    · rw [if_pos h3] at hq; cases hq
    rw [if_neg h3] at hq
    split at hq
    · cases hq
    rename_i wi pos2 q2 hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    have hr := wfIriS_sound _ _ _ _ _ hw
    have ht : rest p = '<' :: (p.next h).get h2 :: rest ((p.next h).next h2) := by
      rw [rest_next p h, h1, rest_next _ h2]
    rw [ht] at hr ⊢
    generalize (p.next h).get h2 = c at h3 hr
    generalize rest ((p.next h).next h2) = t at hr
    simp only [wfIriL] at hr
    unfold readObject12
    split
    · simp_all
    · simp_all
    · rename_i cs' hcs
      simp only [List.cons.injEq] at hcs
      split at hr
      · cases hr
      · rename_i s' p' r' hi
        split at hr
        · cases hr
        · rename_i wi' hm
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp only [hi, hm]
    · simp_all
    · simp_all
    · simp_all
  rw [if_neg h1] at hq
  by_cases h2 : p.get h = '_'
  · rw [if_pos h2] at hq
    split at hq
    · cases hq
    rename_i label pos2 q2 hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    obtain ⟨⟨t, ht⟩, hr⟩ := bnodeS_sound _ _ _ _ _ hb
    rw [ht] at hr ⊢
    simp only [readObject12, hr]
  rw [if_neg h2] at hq
  by_cases h3 : p.get h = '"'
  · rw [if_pos h3] at hq
    split at hq
    · cases hq
    rename_i wl pos2 q2 hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    have hr := literal12S_sound _ _ _ _ _ hl
    have ht : rest p = '"' :: rest (p.next h) := by rw [rest_next p h, h3]
    rw [ht] at hr ⊢
    simp only [readObject12, hr]
  rw [if_neg h3] at hq; cases hq

/-- `readObject12Down` at a cursor: the triple terms that are open are kept in a list, and
each level is a tail call. -/
def object12DownS {s : String} : Nat → OpenTerms12 → Nat → s.Pos → Option (Term × Nat × s.Pos)
  | 0, _, _, _ => none
  | f + 1, opens, pos, p =>
    match open3S p with
    | some q3 =>
      match skipWsS (pos + 3) q3 with
      | (p1, q1) =>
        match subjectS p1 q1 with
        | none => none
        | some (subj, p2, q2) =>
          match skipWsS p2 q2 with
          | (p3, q3') =>
            match predicateS p3 q3' with
            | none => none
            | some (pred, p4, q4) =>
              match skipWsS p4 q4 with
              | (p5, q5) => object12DownS f ((subj, pred) :: opens) p5 q5
    | none =>
      match object12LeafS pos p with
      | none => none
      | some (obj, n, q) => closeS opens obj n q

theorem object12DownS_sound {s : String} :
    ∀ (fuel : Nat) (opens : OpenTerms12) (pos : Nat) (p : s.Pos) (v : Term) (pos' : Nat) (q : s.Pos),
      object12DownS fuel opens pos p = some (v, pos', q) →
        readObject12Down fuel opens pos (rest p) = .ok (v, pos', rest q)
  | 0, _, _, _, _, _, _, h => by simp [object12DownS] at h
  | f + 1, opens, pos, p, v, pos', q, h => by
      unfold object12DownS at h
      split at h
      · rename_i q3 ho
        rw [open3S_sound _ _ ho]
        simp only [readObject12Down]
        have w1 := skipWsS_eq (pos + 3) q3
        rcases hw1 : skipWsS (pos + 3) q3 with ⟨p1, q1⟩
        rw [hw1] at h w1
        simp only at h w1
        rw [← w1]
        simp only []
        split at h
        · cases h
        rename_i subj p2 q2 hs
        rw [subjectS_sound _ _ _ _ _ hs]
        simp only []
        have w2 := skipWsS_eq p2 q2
        rcases hw2 : skipWsS p2 q2 with ⟨p3, q3'⟩
        rw [hw2] at h w2
        simp only at h w2
        rw [← w2]
        simp only []
        split at h
        · cases h
        rename_i pred p4 q4 hp
        rw [predicateS_sound _ _ _ _ _ hp]
        simp only []
        have w3 := skipWsS_eq p4 q4
        rcases hw3 : skipWsS p4 q4 with ⟨p5, q5⟩
        rw [hw3] at h w3
        simp only at h w3
        rw [← w3]
        exact object12DownS_sound f _ _ _ _ _ _ h
      · split at h
        · cases h
        rename_i obj n q6 hl
        rw [readObject12Down_eq, object12LeafS_sound _ _ _ _ _ _ hl]
        exact closeS_sound _ _ _ _ _ _ _ h

/-- `lineFuelGo` at a cursor. -/
def lineFuelS {s : String} (acc : Nat) (p : s.Pos) : Nat :=
  if h : p = s.endPos then acc
  else if p.get h = '\n' then acc
  else lineFuelS (acc + 1) (p.next h)
termination_by p.remainingBytes
decreasing_by exact next_rb p h

theorem lineFuelS_eq {s : String} (acc : Nat) (p : s.Pos) :
    lineFuelS acc p = lineFuelGo (rest p) acc := by
  induction acc, p using lineFuelS.induct with
  | case1 acc => rw [lineFuelS, dif_pos rfl, rest_endPos]; rfl
  | case2 acc p h hn => rw [lineFuelS, dif_neg h, if_pos hn, rest_next p h, hn]; rfl
  | case3 acc p h hn ih =>
    rw [lineFuelS, dif_neg h, if_neg hn, ih, rest_next p h]
    simp [lineFuelGo, hn]

/-- An object, RDF 1.2: `readObject12 (lineFuel cs)` at a cursor. -/
def object12S {s : String} (pos : Nat) (p : s.Pos) : Option (Term × Nat × s.Pos) :=
  object12DownS (lineFuelS 1 p) [] pos p

theorem object12S_sound {s : String} (pos : Nat) (p : s.Pos)
    (v : Term) (pos' : Nat) (q : s.Pos) (hq : object12S pos p = some (v, pos', q)) :
    readObject12 (lineFuel (rest p)) pos (rest p) = .ok (v, pos', rest q) := by
  have h := object12DownS_sound _ _ _ _ _ _ _ hq
  rw [readObject12Down_eq, closeObject12_nil, lineFuelS_eq] at h
  exact h

/-! ## RDF 1.2: statements -/

/-- One N-Quads line, RDF 1.2: `readNQuad12` at a cursor. -/
def nquad12S {s : String} (pos : Nat) (p : s.Pos) :
    Option (Triple × Option Subject × Nat × s.Pos) :=
  match subjectS (skipWsS pos p).1 (skipWsS pos p).2 with
  | none => none
  | some (subj, pos2, p2) =>
    match predicateS (skipWsS pos2 p2).1 (skipWsS pos2 p2).2 with
    | none => none
    | some (pred, pos4, p4) =>
      match object12S (skipWsS pos4 p4).1 (skipWsS pos4 p4).2 with
      | none => none
      | some (obj, pos6, p6) =>
        match optGraphLabelS pos6 p6 with
        | none => none
        | some (gopt, pos7, p7) =>
          match dotS (skipWsS pos7 p7).1 (skipWsS pos7 p7).2 with
          | none => none
          | some (pos9, p9) => some ({ s := subj, p := pred, o := obj }, gopt, pos9, p9)

theorem nquad12S_sound {s : String} (pos : Nat) (p : s.Pos)
    (t : Triple) (g : Option Subject) (pos' : Nat) (q : s.Pos)
    (hq : nquad12S pos p = some (t, g, pos', q)) :
    readNQuad12 pos (rest p) = .ok (t, g, pos', rest q) := by
  unfold nquad12S at hq
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
  have e3 := object12S_sound _ _ _ _ _ ho
  have e4 := optGraphLabelS_sound _ _ _ _ _ hg
  simp only [readNQuad12]
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

/-- One N-Triples line, RDF 1.2: `readTriple12` at a cursor. -/
def triple12S {s : String} (pos : Nat) (p : s.Pos) :
    Option (Triple × Nat × s.Pos) :=
  match subjectS (skipWsS pos p).1 (skipWsS pos p).2 with
  | none => none
  | some (subj, pos2, p2) =>
    match predicateS (skipWsS pos2 p2).1 (skipWsS pos2 p2).2 with
    | none => none
    | some (pred, pos4, p4) =>
      match object12S (skipWsS pos4 p4).1 (skipWsS pos4 p4).2 with
      | none => none
      | some (obj, pos6, p6) =>
        match dotS (skipWsS pos6 p6).1 (skipWsS pos6 p6).2 with
        | none => none
        | some (pos9, p9) => some ({ s := subj, p := pred, o := obj }, pos9, p9)

theorem triple12S_sound {s : String} (pos : Nat) (p : s.Pos)
    (t : Triple) (pos' : Nat) (q : s.Pos)
    (hq : triple12S pos p = some (t, pos', q)) :
    readTriple12 pos (rest p) = .ok (t, pos', rest q) := by
  unfold triple12S at hq
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
  have e3 := object12S_sound _ _ _ _ _ ho
  simp only [readTriple12]
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

/-- The statement reader of a kind of document in a mode. -/
def modeReader (quads : Bool) (mode : Mode) : LineReader :=
  if quads then quadReader mode else tripleReader mode

/-- The native statement reader of a kind of document in a mode, in the shape of a
`LineReader`. -/
def stmtS {s : String} (quads : Bool) (mode : Mode) (pos : Nat) (p : s.Pos) :
    Option (Triple × Option Subject × Nat × s.Pos) :=
  match mode with
  | .rdf11 =>
    if quads then nquad11S pos p
    else
      match triple11S pos p with
      | none => none
      | some (t, pos', q) => some (t, none, pos', q)
  | .rdf12 =>
    if quads then nquad12S pos p
    else
      match triple12S pos p with
      | none => none
      | some (t, pos', q) => some (t, none, pos', q)

theorem stmtS_sound {s : String} (quads : Bool) (mode : Mode) (pos : Nat) (p : s.Pos)
    (t : Triple) (g : Option Subject) (pos' : Nat) (q : s.Pos)
    (hq : stmtS quads mode pos p = some (t, g, pos', q)) :
    modeReader quads mode pos (rest p) = .ok (t, g, pos', rest q) := by
  unfold stmtS at hq
  cases mode <;> cases quads
  · simp only [Bool.false_eq_true, if_false] at hq
    split at hq
    · cases hq
    · rename_i t' pos2 q2 ht
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
      simp only [modeReader, tripleReader, Bool.false_eq_true, if_false, triple11S_sound _ _ _ _ _ ht]
  · simp only [if_true] at hq
    simp only [modeReader, quadReader, if_true, nquad11S_sound _ _ _ _ _ _ hq]
  · simp only [Bool.false_eq_true, if_false] at hq
    split at hq
    · cases hq
    · rename_i t' pos2 q2 ht
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
      simp only [modeReader, tripleReader, Bool.false_eq_true, if_false, triple12S_sound _ _ _ _ _ ht]
  · simp only [if_true] at hq
    simp only [modeReader, quadReader, if_true, nquad12S_sound _ _ _ _ _ _ hq]

/-- `foldLines` over a cursor. A round whose statement the native reader declines runs the
list walk from the start of that round on `rest p`. -/
def foldLinesS {s : String} (quads : Bool) (mode : Mode) {α : Type}
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
            | (pos3, p3) => foldLinesS quads mode consume fuel' pos3 p3 acc
        else if p1.get h = '\n' then
          match skipEolS pos1 p1 with
          | (pos2, p2) => foldLinesS quads mode consume fuel' pos2 p2 acc
        else if p1.get h = '\r' then
          match skipEolS pos1 p1 with
          | (pos2, p2) => foldLinesS quads mode consume fuel' pos2 p2 acc
        else
          match stmtS quads mode pos1 p1 with
          | none => foldLines (modeReader quads mode) consume (fuel' + 1) pos (rest p) acc
          | some (t, gopt, pos2, p2) =>
            match skipWsS pos2 p2 with
            | (pos3, p3) =>
              match skipCommentS pos3 p3 with
              | (pos4, p4) =>
                match skipEolS pos4 p4 with
                | (pos5, p5) => foldLinesS quads mode consume fuel' pos5 p5 (consume acc t gopt)

theorem foldLinesS_eq {s : String} (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) :
    ∀ (fuel pos : Nat) (p : s.Pos) (acc : α),
      foldLinesS quads mode consume fuel pos p acc =
        foldLines (modeReader quads mode) consume fuel pos (rest p) acc := by
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

/-- Feed one chunk of text. The partial line stays text. A line that crosses a chunk
boundary is read as text; the lines of a chunk that follows no partial line are read as the
list walk reads them. -/
def TextFeed.feed (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) (text : String) :
    Except ParseError (TextFeed α) :=
  match st with
  | { acc, carryText, pos } =>
    match splitCompleteLines text.toList with
    | ([], _) => .ok { acc := acc, carryText := carryText ++ text, pos := pos }
    | (cut, rest) =>
      if carryText.isEmpty then
        match foldLines (modeReader quads mode) consume (cut.length + 1) pos cut acc with
        | .ok acc' => .ok { acc := acc', carryText := String.ofList rest, pos := pos + cut.length }
        | .error e => .error e
      else
        let complete := carryText ++ String.ofList cut
        match foldLinesS quads mode consume (complete.length + 1) pos complete.startPos acc with
        | .ok acc' =>
            .ok { acc := acc', carryText := String.ofList rest, pos := pos + complete.length }
        | .error e => .error e

theorem TextFeed.feed_eq (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) (text : String) :
    TextFeed.feed quads mode consume st text =
      (LineFeed.feed (modeReader quads mode) consume st.toLF text.toList).map TextFeed.ofLF := by
  cases st with
  | mk acc carryText pos =>
  simp only [TextFeed.feed, TextFeed.toLF, LineFeed.feed]
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
      generalize foldLines (modeReader quads mode) consume ((x :: xs).length + 1) pos (x :: xs) acc = r
      cases r <;> simp [TextFeed.ofLF, Except.map]
    · rw [if_neg he]
      have ht : (carryText ++ String.ofList (x :: xs)).toList = carryText.toList ++ x :: xs := by
        simp [String.toList_append, String.toList_ofList]
      have hl : (carryText ++ String.ofList (x :: xs)).length =
          (carryText.toList ++ x :: xs).length := by
        rw [← String.length_toList, ht]
      rw [foldLinesS_eq, rest_startPos, hl, ht]
      generalize foldLines (modeReader quads mode) consume
        ((carryText.toList ++ x :: xs).length + 1) pos (carryText.toList ++ x :: xs) acc = r
      cases r <;> simp [TextFeed.ofLF, Except.map]

/-- End of input: walk the partial last line. -/
def TextFeed.finish (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) : Except ParseError α :=
  foldLinesS quads mode consume (st.carryText.length + 1) st.pos st.carryText.startPos st.acc

theorem TextFeed.finish_eq (quads : Bool) (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (st : TextFeed α) :
    TextFeed.finish quads mode consume st =
      LineFeed.finish (modeReader quads mode) consume st.toLF := by
  simp only [TextFeed.finish, LineFeed.finish, LineFeed.carry, TextFeed.toLF,
    List.reverse_reverse]
  rw [foldLinesS_eq, rest_startPos, String.length_toList]


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
      "<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 300 'y') ++ "\" <urn:g> .\n",
    "<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 200 'x') ++ "\\u0041\\U0001F600\\t\" .\n",
    "<urn:s> <urn:p> _:" ++ String.ofList (List.replicate 200 'a') ++ ".\n_:a.b.c <urn:p> _:b..\n",
    "_:a. <urn:p> <urn:o> .\n<urn:s> <urn:p> _:x.y.\n",
    "<urn:s> <urn:p> \"\\u004\" .\n",
    "<urn:s> <urn:p> \"\\uD800\" .\n",
    "<urn:s> <urn:p> \"\\U0011FFFF\" .\n",
    "<urn:s> <urn:p> \"\\q\" .\n",
    "<urn:s> <urn:p> <<( <urn:a> <urn:b> <<( _:c <urn:d> \"e\"@en--rtl )>> )>> .\n",
    "<urn:s> <urn:p> <<(<urn:a> <urn:b> \"x\")>> <urn:g> .\n",
    "<urn:s> <urn:p> \"Alice\" @en .\n<urn:s> <urn:p> \"2\"  ^^  <urn:int> .\n",
    "<urn:s> <urn:p> \"x\"@en--ltr .\n<urn:s> <urn:p> \"x\"@en--up .\n",
    "<urn:s> <urn:p> \"x\" ^<urn:t> .\n",
    "<urn:s> <urn:p> \"x\"\t .\n<urn:s> <urn:p> \"y\" @ .\n",
    "<urn:s> <urn:p> << <urn:a> <urn:b> <urn:c> >> .\n",
    "<urn:s> <urn:p> <<( <urn:a> <urn:b> <urn:c> .\n",
    "<urn:s> <urn:p> <<( <urn:a> <urn:b> <urn:c> )>> )>> .\n",
    "<urn:s> <urn:p> " ++ String.join (List.replicate 40 "<<( <urn:a> <urn:b> ") ++ "\"" ++
      String.ofList (List.replicate 300 'z') ++ "\"" ++ String.join (List.replicate 40 " )>>") ++ " .\n" ]

#guard docs.all fun d => sameRun true .rdf11 d
#guard docs.all fun d => sameRun false .rdf11 d
#guard docs.all fun d => sameRun true .rdf12 d
#guard docs.all fun d => sameRun false .rdf12 d

-- The native reader reads these forms (a declined form would make the guards above compare
-- the list walk with itself).
private def native (quads : Bool) (line : String) (mode : Mode := .rdf11) : Bool :=
  (stmtS quads mode 0 line.startPos).isSome

#guard native true "<urn:s> <urn:p> <urn:o> .\n"
#guard native true "<urn:s> <urn:p> \"a\" <urn:g> .\n"
#guard native true "_:s <urn:p> \"a\"@en _:g .\n"
#guard native true "<urn:s> <urn:p> \"a\"^^<urn:t> .\n"
#guard native true "<urn:s> <urn:p> \"a\\n\\t\\\"b\" .\n"
#guard native false ("<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 100000 'x') ++ "\" .\n")
#guard native true "<urn:s> <urn:p> \"\\u0041 \\U0001F600\" .\n"
#guard native false "<urn:s> <urn:p> _:b. \n"
#guard native false "_:a.b <urn:p> _:b..\n"
#guard !native true "<urn:s> <urn:p> \"\\u004\" .\n"
#guard !native true "<urn:s> <urn:p> \"\\uD800\" .\n"
#guard !native true "<urn:s> <urn:p> .\n"
#guard native true "<urn:s> <urn:p> <<( <urn:a> <urn:b> <<( _:c <urn:d> \"e\"@en--rtl )>> )>> <urn:g> .\n" .rdf12
#guard native false "<urn:s> <urn:p> \"Alice\" @en .\n" .rdf12
#guard native false "<urn:s> <urn:p> \"2\"  ^^  <urn:int> .\n" .rdf12
#guard native false "<urn:s> <urn:p> \"x\\u0041\" .\n" .rdf12
#guard native false "<urn:s> <urn:p> _:b. \n" .rdf12
#guard native false ("<urn:s> <urn:p> \"" ++ String.ofList (List.replicate 100000 'x') ++ "\" .\n") .rdf12
#guard !native false "<urn:s> <urn:p> << <urn:a> <urn:b> <urn:c> >> .\n" .rdf12
#guard !native false "<urn:s> <urn:p> \"x\"@en--up .\n" .rdf12

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
