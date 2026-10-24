/-
L4Factoidal.Syntax.NTriplesDocRoundTrip — the N-Triples document round trip:
`parseNTriples` reads back the graph that `Graph.toNTriples` wrote
(https://github.com/danbri/factoidal/issues/975, phase C).

`Syntax/NTriplesRoundTrip.lean` proves the IRI half for one closed triple.
This module adds the other terms and the composition over lines:

* blank nodes: `readBlankNodeLabel_safe`;
* literals: the escaper and the string reader are inverse
  (`readStringLiteralBody_escape`), then the language tag
  (`readLangTag_safe`) and the datatype IRI;
* RDF 1.2 mode: the language tag with a base direction
  (`readLangDir12_plain`, `readLangDir12_dir`) and triple terms nested to any
  depth (`readObject12_safe`); the object fuel `lineFuel` is more than the
  length of the object's text, which has no line break (`nl_not_mem_term`);
* one line: `readTriple11_line`, `readTriple12_line`;
* the document: `parseNTriples_toNTriples mode`, the equality
  `parseNTriples text mode = .ok g`, the list of triples in order, in both
  modes.

## The domain: three lexical restrictions of the grammar

The writer writes an IRI, a blank-node label and a language tag as they are.
`WfIri`, `BNodeId` and `WfLiteral` admit strings that the N-Triples grammar
does not, so the round trip holds on a domain only (`Triple.ntLex`):

* IRIREF, RDF 1.1 N-Triples production [8]: `iriPrintSafe` (from
  `NTriplesRoundTrip`);
* BLANK_NODE_LABEL, production [141s]:
  `(PN_CHARS_U | [0-9]) ((PN_CHARS | '.')* PN_CHARS)?` (`bnodeLabelSafe`);
* LANGTAG, production [144s]: `[a-zA-Z]+ ('-' [a-zA-Z0-9]+)*`, and each
  subtag at most 8 characters, which the RDF 1.2 reader checks (BCP 47
  section 2.1) (`langTagSafe`).

The `#guard`s at the end show one counter-example outside each restriction.

The writer domain of `RDF/Sink.lean` is wider (`Triple.ntSafe`, no condition on
blank-node labels, https://github.com/danbri/factoidal/issues/986): those
writers relabel first (`Dataset.relabelForWrite`), and
`Triple.ntLex_renameBnodes` takes a relabelled triple of the writer domain into
`Triple.ntLex`. A language tag outside LANGTAG is refused by `Term.toNTriples`
with an error (`langTagWritable`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.NTriplesRoundTrip
import L4Factoidal.Syntax.BlankNodeLabel
import L4Factoidal.RDF.BnodeTransport

namespace L4Factoidal.Syntax.NTriplesRoundTrip

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## The domain -/

/-- BLANK_NODE_LABEL [141s], the characters after `_:`: a first character
`PN_CHARS_U` or a digit, then `PN_CHARS` or `.`, and no `.` at the end. -/
def bnodeLabelCharsSafe : List Char → Bool
  | [] => false
  | c0 :: rest => isBnodeStartChar c0 && rest.all isBnodeChar && (c0 :: rest).getLast? != some '.'

/-- A blank-node label that the N-Triples grammar admits. -/
def bnodeLabelSafe (b : String) : Bool := bnodeLabelCharsSafe b.toList

/-- LANGTAG [144s], the characters after `@`: a letter first, then letters,
digits and `-`, every subtag 1 to 8 characters (`validLangSubtags`). -/
def langTagCharsSafe : List Char → Bool
  | [] => false
  | c :: rest => isLangStart c && rest.all isLangChar && validLangSubtags (c :: rest) 0

/-- A language tag that the N-Triples grammar admits. -/
def langTagSafe (tag : String) : Bool := langTagCharsSafe tag.toList

/-- A subject that the N-Triples grammar can state. -/
def Subject.ntLex : Subject → Bool
  | .iri i => iriPrintSafe i.val
  | .bnode b => bnodeLabelSafe b

/-- A term that the N-Triples grammar can state: every IRI (the datatype IRI of
a literal too), every blank-node label and every language tag, nested ones
included. -/
def Term.ntLex : Term → Bool
  | .iri i => iriPrintSafe i.val
  | .bnode b => bnodeLabelSafe b
  | .literal l => iriPrintSafe l.val.datatype.val && l.val.langTag.all langTagSafe
  | .tripleTerm s p o => Subject.ntLex s && iriPrintSafe p.val && Term.ntLex o

/-- A triple that the N-Triples grammar can state. -/
def Triple.ntLex (t : Triple) : Bool :=
  Subject.ntLex t.s && iriPrintSafe t.p.val && Term.ntLex t.o

/-! ## The writer domain: no condition on blank-node labels

The writers of `RDF/Sink.lean` write the dataset `Dataset.relabelForWrite`
(`RDF/WriterLabels.lean`), whose blank-node labels are all BLANK_NODE_LABELs.
So the domain of the writers (`Dataflow.writerDomain`) needs no condition on
the labels: `Triple.ntSafe` is `Triple.ntLex` without it. A triple in
`Triple.ntSafe` whose labels are all in BLANK_NODE_LABEL is in `Triple.ntLex`
(`Triple.ntLex_of_ntSafe`); relabelling keeps `Triple.ntSafe`
(`Triple.ntSafe_renameBnodes`). -/

/-- A subject in the writer domain: an IRI in IRIREF, or any blank node. -/
def Subject.ntSafe : Subject → Bool
  | .iri i => iriPrintSafe i.val
  | .bnode _ => true

/-- A term in the writer domain: every IRI (the datatype IRI of a literal too)
and every language tag in its production, nested ones included; any blank
node. -/
def Term.ntSafe : Term → Bool
  | .iri i => iriPrintSafe i.val
  | .bnode _ => true
  | .literal l => iriPrintSafe l.val.datatype.val && l.val.langTag.all langTagSafe
  | .tripleTerm s p o => Subject.ntSafe s && iriPrintSafe p.val && Term.ntSafe o

/-- A triple in the writer domain of N-Triples. -/
def Triple.ntSafe (t : Triple) : Bool :=
  Subject.ntSafe t.s && iriPrintSafe t.p.val && Term.ntSafe t.o

/-- The two checks of BLANK_NODE_LABEL agree. -/
theorem bnodeLabelSafe_eq_isBlankNodeLabel (b : String) : bnodeLabelSafe b = isBlankNodeLabel b := by
  unfold bnodeLabelSafe isBlankNodeLabel
  cases b.toList with
  | nil => rfl
  | cons c0 rest =>
    simp only [bnodeLabelCharsSafe]
    cases rest with
    | nil =>
      by_cases hc : c0 = '.'
      · subst hc; rfl
      · have h1 : (some c0 != some '.') = true := by simpa using hc
        have h2 : ((none : Option Char) != some '.') = true := rfl
        show (isBnodeStartChar c0 && [].all isBnodeChar && (some c0 != some '.')) =
          (isBnodeStartChar c0 && [].all isBnodeChar && ((none : Option Char) != some '.'))
        rw [h1, h2]
    | cons c1 r =>
      simp [List.getLast?_cons_cons]

theorem Subject.ntLex_of_ntSafe {s : Subject} (h : Subject.ntSafe s = true)
    (hb : ∀ b ∈ s.bnodes, isBlankNodeLabel b = true) : Subject.ntLex s = true := by
  cases s with
  | iri i => exact h
  | bnode b =>
    show bnodeLabelSafe b = true
    rw [bnodeLabelSafe_eq_isBlankNodeLabel]
    exact hb b (by simp [Subject.bnodes])

theorem Term.ntLex_of_ntSafe : ∀ {t : Term}, Term.ntSafe t = true →
    (∀ b ∈ t.bnodes, isBlankNodeLabel b = true) → Term.ntLex t = true
  | .iri _, h, _ => h
  | .bnode b, _, hb => by
    show bnodeLabelSafe b = true
    rw [bnodeLabelSafe_eq_isBlankNodeLabel]
    exact hb b (by simp [Term.bnodes])
  | .literal _, h, _ => h
  | .tripleTerm s p o, h, hb => by
    simp only [Term.ntSafe, Bool.and_eq_true] at h
    simp only [Term.ntLex, Bool.and_eq_true]
    refine ⟨⟨Subject.ntLex_of_ntSafe h.1.1 fun b hm => hb b ?_, h.1.2⟩,
      Term.ntLex_of_ntSafe h.2 fun b hm => hb b ?_⟩
    · simp [Term.bnodes, hm]
    · simp [Term.bnodes, hm]

/-- **A triple of the writer domain whose labels are BLANK_NODE_LABELs is in
the domain of the round trip.** -/
theorem Triple.ntLex_of_ntSafe {t : Triple} (h : Triple.ntSafe t = true)
    (hb : ∀ b ∈ t.bnodes, isBlankNodeLabel b = true) : Triple.ntLex t = true := by
  simp only [Triple.ntSafe, Bool.and_eq_true] at h
  simp only [Triple.ntLex, Bool.and_eq_true]
  exact ⟨⟨Subject.ntLex_of_ntSafe h.1.1 fun b hm => hb b (by simp [Triple.bnodes, hm]), h.1.2⟩,
    Term.ntLex_of_ntSafe h.2 fun b hm => hb b (by simp [Triple.bnodes, hm])⟩

theorem Subject.ntSafe_renameBnodes (f : BNodeId → BNodeId) (s : Subject) :
    Subject.ntSafe (s.renameBnodes f) = Subject.ntSafe s := by
  cases s <;> rfl

theorem Term.ntSafe_renameBnodes (f : BNodeId → BNodeId) : ∀ t : Term, Term.ntSafe (t.renameBnodes f) = Term.ntSafe t
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal _ => rfl
  | .tripleTerm s p o => by
    simp only [Term.renameBnodes, Term.ntSafe, Subject.ntSafe_renameBnodes, Term.ntSafe_renameBnodes f o]

/-- **Relabelling keeps the writer domain.** -/
theorem Triple.ntSafe_renameBnodes (f : BNodeId → BNodeId) (t : Triple) :
    Triple.ntSafe (t.renameBnodes f) = Triple.ntSafe t := by
  simp only [Triple.renameBnodes, Triple.ntSafe, Subject.ntSafe_renameBnodes, Term.ntSafe_renameBnodes]

/-- A relabelled triple of the writer domain, with a map whose labels are
BLANK_NODE_LABELs, is in the domain of the round trip. -/
theorem Triple.ntLex_renameBnodes {f : BNodeId → BNodeId} (hf : ∀ b, isBlankNodeLabel (f b) = true)
    {t : Triple} (h : Triple.ntSafe t = true) : Triple.ntLex (t.renameBnodes f) = true := by
  apply Triple.ntLex_of_ntSafe
  · rw [Triple.ntSafe_renameBnodes]; exact h
  · intro b hb
    rw [Triple.bnodes_renameBnodes, List.mem_map] at hb
    obtain ⟨a, -, rfl⟩ := hb
    exact hf a

/-! ## Small facts about the scanners -/

theorem span_loop_append_stop (p : Char → Bool) (c : Char) (tail : List Char) (hc : p c = false) :
    ∀ (xs acc : List Char), xs.all p = true →
      List.span.loop p (xs ++ c :: tail) acc = (acc.reverse ++ xs, c :: tail)
  | [], acc, _ => by simp [List.span.loop, hc]
  | x :: xs, acc, hx => by
    simp only [List.all_cons, Bool.and_eq_true] at hx
    simp only [List.cons_append, List.span.loop, hx.1]
    rw [span_loop_append_stop p c tail hc xs (x :: acc) hx.2]
    simp

theorem span_append_stop (p : Char → Bool) :
    ∀ (xs : List Char) (c : Char) (tail : List Char),
      xs.all p = true → p c = false → (xs ++ c :: tail).span p = (xs, c :: tail) := by
  intro xs c tail hx hc
  unfold List.span
  rw [span_loop_append_stop p c tail hc xs [] hx]
  simp

theorem skipWs_stop (pos : Nat) {c : Char} {rest : List Char}
    (h : isNtWs c = false) : skipWs pos (c :: rest) = (pos, c :: rest) := by
  simp [skipWs, List.span, List.span.loop, h]

theorem skipWs_space (pos : Nat) {c : Char} {rest : List Char}
    (h : isNtWs c = false) : skipWs pos (' ' :: c :: rest) = (pos + 1, c :: rest) := by
  simp only [isNtWs, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  simp [skipWs, List.span, List.span.loop, isNtWs, h.1, h.2]

theorem mkLiteral_wf (pos : Nat) (l : Literal) (h : literalWf l = true) :
    mkLiteral pos l = .ok ⟨l, h⟩ :=
  mkLiteral_of_wf pos l h

theorem string_ofList_cons (c : Char) (cs : List Char) :
    String.ofList (c :: cs) = c.toString ++ String.ofList cs := by
  first
    | rfl
    | (apply String.ext; simp [Char.toString])

/-! ## Blank nodes -/

/-- **A blank-node label in the domain reads back**, followed by a space. -/
theorem readBlankNodeLabel_safe (pos : Nat) (b : String) (tail : List Char)
    (h : bnodeLabelSafe b = true) :
    ∃ p, readBlankNodeLabel pos ('_' :: ':' :: (b.toList ++ ' ' :: tail)) = .ok (b, p, ' ' :: tail) := by
  unfold bnodeLabelSafe at h
  have hb : String.ofList b.toList = b := String.ofList_toList
  generalize b.toList = cs at h hb
  subst hb
  cases cs with
  | nil => simp [bnodeLabelCharsSafe] at h
  | cons c0 rest =>
    simp only [bnodeLabelCharsSafe, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hst, hall⟩, hlast⟩ := h
    have hsp : (rest ++ ' ' :: tail).span isBnodeChar = (rest, ' ' :: tail) :=
      span_append_stop _ rest ' ' tail hall (by decide)
    simp only [List.cons_append, readBlankNodeLabel, hst, Bool.not_true, hsp]
    split
    · next hl => cases hl
    · exact ⟨_, rfl⟩

/-! ## Literals -/

/-- The escape of one character, as `escapeLiteral` writes it. -/
def escChar (c : Char) : List Char :=
  match c with
  | '\\' => ['\\', '\\']
  | '"'  => ['\\', '"']
  | '\n' => ['\\', 'n']
  | '\r' => ['\\', 'r']
  | '\t' => ['\\', 't']
  | _    => [c]

theorem escapeLiteral_toList (s : String) :
    (escapeLiteral s).toList = s.toList.flatMap escChar := by
  simp only [escapeLiteral, String.toList_ofList]
  rfl

theorem strLitNextStep_plain {pos : Nat} {c : Char} {rest : List Char}
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c ≠ '\n') (h4 : c ≠ '\r') :
    strLitNextStep pos (c :: rest) = .emit c 1 rest := by
  unfold strLitNextStep
  split <;> simp_all

/-- The string reader decodes the escape of each character to the character. -/
theorem strLitNextStep_escChar (pos : Nat) (c : Char) (r : List Char) :
    ∃ w, strLitNextStep pos (escChar c ++ r) = .emit c w r := by
  by_cases h1 : c = '\\'
  · subst h1; exact ⟨2, rfl⟩
  by_cases h2 : c = '"'
  · subst h2; exact ⟨2, rfl⟩
  by_cases h3 : c = '\n'
  · subst h3; exact ⟨2, rfl⟩
  by_cases h4 : c = '\r'
  · subst h4; exact ⟨2, rfl⟩
  by_cases h5 : c = '\t'
  · subst h5; exact ⟨2, rfl⟩
  have he : escChar c = [c] := by
    unfold escChar
    split <;> simp_all
  rw [he]
  exact ⟨1, strLitNextStep_plain h2 h1 h3 h4⟩

/-- **The escaper and the string reader are inverse**: the body of a quoted
string written by `escapeLiteral` reads back to the string, up to the closing
quote, and the rest is handed on. -/
theorem readStringLiteralBody_escape : ∀ (cs : List Char) (pos : Nat) (tail : List Char),
    ∃ p, readStringLiteralBody pos (cs.flatMap escChar ++ '"' :: tail) = .ok (String.ofList cs, p, tail)
  | [], pos, tail => ⟨pos + 1, by simp⟩
  | c :: cs, pos, tail => by
    obtain ⟨w, hw⟩ := strLitNextStep_escChar pos c (cs.flatMap escChar ++ '"' :: tail)
    obtain ⟨p, hp⟩ := readStringLiteralBody_escape cs (pos + w) tail
    refine ⟨p, ?_⟩
    rw [List.flatMap_cons, List.append_assoc, readStringLiteralBody_emit _ _ _ _ _ hw, hp,
      string_ofList_cons]
    rfl

/-- The quoted string of a lexical form, followed by anything. -/
theorem readStringLiteralQuoted_escape (pos : Nat) (lex : String) (tail : List Char) :
    ∃ p, readStringLiteralQuoted pos ('"' :: ((escapeLiteral lex).toList ++ '"' :: tail))
      = .ok (lex, p, tail) := by
  obtain ⟨p, hp⟩ := readStringLiteralBody_escape lex.toList (pos + 1) tail
  refine ⟨p, ?_⟩
  rw [escapeLiteral_toList]
  simpa [readStringLiteralQuoted, String.ofList_toList] using hp

/-- **A language tag in the domain reads back** (RDF 1.1 reader), followed by
a space. -/
theorem readLangTag_safe (pos : Nat) (tag : String) (tail : List Char)
    (h : langTagSafe tag = true) :
    ∃ p, readLangTag pos ('@' :: (tag.toList ++ ' ' :: tail)) = .ok (tag, p, ' ' :: tail) := by
  unfold langTagSafe at h
  have hb : String.ofList tag.toList = tag := String.ofList_toList
  generalize tag.toList = cs at h hb
  subst hb
  cases cs with
  | nil => simp [langTagCharsSafe] at h
  | cons c rest =>
    simp only [langTagCharsSafe, Bool.and_eq_true] at h
    obtain ⟨⟨hst, hall⟩, -⟩ := h
    have hall' : (c :: rest).all isLangChar = true := by
      simp only [List.all_cons, hall, Bool.and_true]
      simp only [isLangStart, Bool.or_eq_true, decide_eq_true_eq] at hst
      simp only [isLangChar, Bool.or_eq_true, decide_eq_true_eq]
      rcases hst with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
    have hsp : ((c :: rest) ++ ' ' :: tail).span isLangChar = (c :: rest, ' ' :: tail) :=
      span_append_stop _ (c :: rest) ' ' tail hall' (by decide)
    simp only [List.cons_append, readLangTag, hst, Bool.not_true]
    simp only [readLangTagRun, ← List.cons_append, hsp]
    exact ⟨_, rfl⟩

/-! ## Terms -/

/-- **A subject in the domain reads back**, followed by a space. -/
theorem readSubject_safe (pos : Nat) (s : Subject) (tail : List Char)
    (h : Subject.ntLex s = true) :
    ∃ p, readSubject pos ((Subject.toNTriples s).toList ++ ' ' :: tail) = .ok (s, p, ' ' :: tail) := by
  cases s with
  | iri i =>
    have hc : (Subject.toNTriples (.iri i)).toList ++ ' ' :: tail
        = '<' :: (i.val.toList ++ '>' :: ' ' :: tail) := by simp [Subject.toNTriples]
    rw [hc, readSubject_printSafe pos i _ h]
    exact ⟨_, rfl⟩
  | bnode b =>
    have hc : (Subject.toNTriples (.bnode b)).toList ++ ' ' :: tail
        = '_' :: ':' :: (b.toList ++ ' ' :: tail) := by simp [Subject.toNTriples]
    obtain ⟨p, hp⟩ := readBlankNodeLabel_safe pos b tail h
    rw [hc]
    simp only [readSubject, ← hc]
    rw [hc, hp]
    exact ⟨p, rfl⟩

/-- The text of a subject starts with `<` or `_`. -/
theorem subject_toNTriples_head (s : Subject) (tail : List Char) :
    ∃ r, (Subject.toNTriples s).toList ++ tail = '<' :: r ∨
      (Subject.toNTriples s).toList ++ tail = '_' :: r := by
  cases s with
  | iri i => exact ⟨_, Or.inl (by simp [Subject.toNTriples]; rfl)⟩
  | bnode b => exact ⟨_, Or.inr (by simp [Subject.toNTriples]; rfl)⟩

/-- **An object in the domain reads back** (RDF 1.1 reader), followed by a
space: an IRI, a blank node, or a literal with its lexical form, its datatype
IRI and its language tag. -/
theorem readObject11_safe (pos : Nat) (t : Term) (str : String) (tail : List Char)
    (hs : Term.ntLex t = true) (h : Term.toNTriples .rdf11 t = .ok str) :
    ∃ p, readObject11 pos (str.toList ++ ' ' :: tail) = .ok (t, p, ' ' :: tail) := by
  cases t with
  | iri i =>
    simp only [Term.toNTriples, Except.ok.injEq] at h
    subst h
    have hc : ("<" ++ i.val ++ ">").toList ++ ' ' :: tail
        = '<' :: (i.val.toList ++ '>' :: ' ' :: tail) := by simp
    rw [hc, readObject11_printSafe pos i _ hs]
    exact ⟨_, rfl⟩
  | bnode b =>
    simp only [Term.toNTriples, Except.ok.injEq] at h
    subst h
    have hc : ("_:" ++ b).toList ++ ' ' :: tail = '_' :: ':' :: (b.toList ++ ' ' :: tail) := by simp
    obtain ⟨p, hp⟩ := readBlankNodeLabel_safe pos b tail hs
    rw [hc]
    simp only [readObject11, ← hc]
    rw [hc, hp]
    exact ⟨p, rfl⟩
  | tripleTerm s p o =>
    simp [Term.toNTriples] at h
  | literal wl =>
    obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := wl
    simp only [Term.ntLex, Bool.and_eq_true] at hs
    obtain ⟨hdt, htag⟩ := hs
    cases tag with
    | none =>
      cases dir with
      | some d => simp [literalWf] at hwf
      | none =>
        by_cases hx : dt = xsdString
        · subst hx
          simp only [Term.toNTriples, if_pos, Except.ok.injEq] at h
          subst h
          obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape (pos) lex (' ' :: tail)
          have hc : ("\"" ++ escapeLiteral lex ++ "\"").toList ++ ' ' :: tail
              = '"' :: ((escapeLiteral lex).toList ++ '"' :: ' ' :: tail) := by simp
          rw [hc]
          simp only [readObject11, readLiteral, ← hc]
          rw [hc, hp1]
          simp only [mkLiteral_wf _ _ hwf]
          exact ⟨_, rfl⟩
        · simp only [Term.toNTriples, if_neg hx, Except.ok.injEq] at h
          subst h
          obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape (pos) lex
            ('^' :: '^' :: '<' :: (dt.val.toList ++ '>' :: ' ' :: tail))
          have hc : ("\"" ++ escapeLiteral lex ++ "\"^^<" ++ dt.val ++ ">").toList ++ ' ' :: tail
              = '"' :: ((escapeLiteral lex).toList ++ '"' ::
                  '^' :: '^' :: '<' :: (dt.val.toList ++ '>' :: ' ' :: tail)) := by simp
          rw [hc]
          simp only [readObject11, readLiteral, ← hc]
          rw [hc, hp1]
          simp only [readDatatype, readIriRef_printSafe _ dt _ hdt, mkIri_val, mkLiteral_wf _ _ hwf]
          exact ⟨_, rfl⟩
    | some tg =>
      cases dir with
      | some d => simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp at h
      | none =>
        have hdt' : dt = rdfLangString := Subtype.ext (by simp [literalWf] at hwf; exact hwf.1)
        subst hdt'
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq] at h
        subst h
        simp only [Option.all_some] at htag
        obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape (pos) lex ('@' :: (tg.toList ++ ' ' :: tail))
        obtain ⟨p2, hp2⟩ := readLangTag_safe p1 tg tail htag
        have hc : ("\"" ++ escapeLiteral lex ++ "\"@" ++ tg).toList ++ ' ' :: tail
            = '"' :: ((escapeLiteral lex).toList ++ '"' :: '@' :: (tg.toList ++ ' ' :: tail)) := by simp
        rw [hc]
        simp only [readObject11, readLiteral, ← hc]
        rw [hc, hp1]
        dsimp only
        simp only [hp2, mkLiteral_wf _ _ hwf]
        exact ⟨_, rfl⟩

/-- The text of an object written in RDF 1.1 mode starts with `<`, `_` or `"`:
never white space. -/
theorem term_toNTriples11_head (t : Term) (str : String) (tail : List Char)
    (h : Term.toNTriples .rdf11 t = .ok str) :
    ∃ c r, str.toList ++ tail = c :: r ∧ isNtWs c = false := by
  cases t with
  | iri i =>
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    exact ⟨'<', _, by simp; rfl, by decide⟩
  | bnode b =>
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    exact ⟨'_', _, by simp; rfl, by decide⟩
  | tripleTerm s p o => simp [Term.toNTriples] at h
  | literal wl =>
    obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := wl
    cases tag with
    | none =>
      by_cases hx : dt = xsdString
      · simp only [Term.toNTriples, if_pos hx, Except.ok.injEq] at h; subst h
        exact ⟨'"', _, by simp; rfl, by decide⟩
      · simp only [Term.toNTriples, if_neg hx, Except.ok.injEq] at h; subst h
        exact ⟨'"', _, by simp; rfl, by decide⟩
    | some tg =>
      cases dir with
      | some d => simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp at h
      | none =>
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq] at h; subst h
        exact ⟨'"', _, by simp; rfl, by decide⟩

/-! ## One line -/

/-- **One line in the domain reads back** (RDF 1.1 reader): the triple, and
the line break after its `.`. -/
theorem readTriple11_line (pos : Nat) (t : Triple) (line : String) (tail : List Char)
    (hs : Triple.ntLex t = true) (h : Triple.toNTriples .rdf11 t = .ok line) :
    ∃ p, readTriple11 pos (line.toList ++ tail) = .ok (t, p, '\n' :: tail) := by
  obtain ⟨s, pr, o⟩ := t
  simp only [Triple.ntLex, Bool.and_eq_true] at hs
  obtain ⟨⟨hss, hps⟩, hos⟩ := hs
  unfold Triple.toNTriples at h
  cases ho : Term.toNTriples .rdf11 o with
  | error e => simp [ho] at h
  | ok oStr =>
    simp only [ho, Except.ok.injEq] at h
    subst h
    have hc : (Subject.toNTriples s ++ " <" ++ pr.val ++ "> " ++ oStr ++ " .\n").toList ++ tail
        = (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))) := by simp
    rw [hc]
    obtain ⟨r0, hr0⟩ := subject_toNTriples_head s (' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))))
    have hws0 : skipWs pos ((Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))))
        = (pos, (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail)))) := by
      rcases hr0 with hr0 | hr0 <;> rw [hr0] <;> exact skipWs_stop pos (by decide)
    obtain ⟨p2, hp2⟩ := readSubject_safe pos s ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))) hss
    obtain ⟨c, r, hcr, hcws⟩ := term_toNTriples11_head o oStr (' ' :: '.' :: '\n' :: tail) ho
    obtain ⟨p6, hp6⟩ := readObject11_safe (p2 + 1 + pr.val.length + 2 + 1) o oStr ('.' :: '\n' :: tail) hos ho
    unfold readTriple11
    rw [hws0]
    dsimp only
    rw [hp2]
    dsimp only
    rw [skipWs_space _ (by decide : isNtWs '<' = false)]
    dsimp only
    rw [readPredicate_printSafe _ pr _ hps]
    dsimp only
    rw [hcr, skipWs_space _ hcws, ← hcr, hp6]
    dsimp only
    rw [skipWs_space _ (by decide : isNtWs '.' = false)]
    exact ⟨_, rfl⟩

/-! ## RDF 1.2 mode: language tags with a direction, triple terms -/
theorem validLangSubtags_other {c : Char} (h : c ≠ '-') (l : List Char) (cur : Nat) :
    validLangSubtags (c :: l) cur = validLangSubtags l (cur + 1) := by
  rw [validLangSubtags.eq_def]
  split
  · next heq => cases heq
  · next heq => simp at heq; exact absurd heq.1 h
  · next heq => simp at heq; obtain ⟨rfl, rfl⟩ := heq; rfl

theorem validLangSubtags_step {c1 c2 : Char} {rest : List Char} {cur : Nat}
    (h : validLangSubtags (c1 :: c2 :: rest) cur = true) :
    validLangSubtags (c2 :: rest) (if c1 = '-' then 0 else cur + 1) = true ∧
      ¬ (c1 = '-' ∧ c2 = '-') := by
  by_cases h1 : c1 = '-'
  · subst h1
    simp only [validLangSubtags, Bool.and_eq_true] at h
    refine ⟨by simpa using h.2, ?_⟩
    rintro ⟨-, rfl⟩
    simp [validLangSubtags] at h
  · rw [validLangSubtags_other h1] at h
    exact ⟨by simpa [h1] using h, fun h' => h1 h'.1⟩

theorem splitOnDoubleHyphen_valid : ∀ (cs : List Char) (cur : Nat) (acc : List Char),
    validLangSubtags cs cur = true → splitOnDoubleHyphen cs acc = (acc.reverse ++ cs, none)
  | [], _, acc, _ => by simp [splitOnDoubleHyphen]
  | [c], _, acc, _ => by simp [splitOnDoubleHyphen]
  | c1 :: c2 :: rest, cur, acc, h => by
    obtain ⟨hc, hn⟩ := validLangSubtags_step h
    have ih := splitOnDoubleHyphen_valid (c2 :: rest) _ (c1 :: acc) hc
    simp only [splitOnDoubleHyphen]
    rw [if_neg (by simpa using hn), ih]
    simp

theorem splitOnDoubleHyphen_dir : ∀ (cs : List Char) (cur : Nat) (acc d : List Char),
    validLangSubtags cs cur = true →
    splitOnDoubleHyphen (cs ++ '-' :: '-' :: d) acc = (acc.reverse ++ cs, some d)
  | [], _, acc, d, _ => by simp [splitOnDoubleHyphen]
  | [c], cur, acc, d, h => by
    have hc : c ≠ '-' := by
      rintro rfl; simp [validLangSubtags] at h
    simp [splitOnDoubleHyphen, hc]
  | c1 :: c2 :: rest, cur, acc, d, h => by
    obtain ⟨hc, hn⟩ := validLangSubtags_step h
    have ih := splitOnDoubleHyphen_dir (c2 :: rest) _ (c1 :: acc) d hc
    simp only [List.cons_append] at ih ⊢
    simp only [splitOnDoubleHyphen]
    rw [if_neg (by simpa using hn), ih]
    simp

theorem langTagSafe_parts {tag : String} (h : langTagSafe tag = true) :
    ∃ c rest, tag.toList = c :: rest ∧ isLangStart c = true ∧ (c :: rest).all isLangChar = true ∧
      validLangSubtags (c :: rest) 0 = true := by
  unfold langTagSafe at h
  cases hv : tag.toList with
  | nil => rw [hv] at h; simp [langTagCharsSafe] at h
  | cons c rest =>
    rw [hv] at h
    simp only [langTagCharsSafe, Bool.and_eq_true] at h
    obtain ⟨⟨hst, hall⟩, hval⟩ := h
    refine ⟨c, rest, rfl, hst, ?_, hval⟩
    simp only [List.all_cons, hall, Bool.and_true]
    simp only [isLangStart, Bool.or_eq_true, decide_eq_true_eq] at hst
    simp only [isLangChar, Bool.or_eq_true, decide_eq_true_eq]
    rcases hst with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))

/-- **A language tag in the domain reads back** (RDF 1.2 reader, no
direction). -/
theorem readLangDir12_plain (pos : Nat) (tag : String) (tail : List Char)
    (h : langTagSafe tag = true) :
    ∃ p, readLangDir12 pos ('@' :: (tag.toList ++ ' ' :: tail)) = .ok ((tag, none), p, ' ' :: tail) := by
  obtain ⟨c, rest, hv, hst, hall, hval⟩ := langTagSafe_parts h
  have hb : String.ofList tag.toList = tag := String.ofList_toList
  rw [hv] at hb ⊢
  have hsp : ((c :: rest) ++ ' ' :: tail).span isLangChar = (c :: rest, ' ' :: tail) :=
    span_append_stop _ (c :: rest) ' ' tail hall (by decide)
  simp only [List.cons_append, readLangDir12, hst, Bool.not_true]
  simp only [readLangTagRun, ← List.cons_append, hsp]
  rw [String.toList_ofList, splitOnDoubleHyphen_valid _ 0 [] hval]
  simp only [List.reverse_nil, List.nil_append, hval, Bool.not_true]
  rw [hb]
  exact ⟨_, rfl⟩

/-- **A language tag and a base direction read back** (RDF 1.2 reader):
, . -/
theorem readLangDir12_dir (pos : Nat) (tag : String) (d : TextDirection) (tail : List Char)
    (h : langTagSafe tag = true) :
    ∃ p, readLangDir12 pos ('@' :: (tag.toList ++ ('-' :: '-' ::
        (match d with | .ltr => ['l', 't', 'r'] | .rtl => ['r', 't', 'l'])) ++ ' ' :: tail)) =
      .ok ((tag, some (match d with | .ltr => false | .rtl => true)), p, ' ' :: tail) := by
  obtain ⟨c, rest, hv, hst, hall, hval⟩ := langTagSafe_parts h
  have hb : String.ofList tag.toList = tag := String.ofList_toList
  rw [hv] at hb ⊢
  cases d with
  | ltr =>
    have hall' : ((c :: rest) ++ ['-', '-', 'l', 't', 'r']).all isLangChar = true := by
      simp only [List.all_append, hall, Bool.true_and]; decide
    have hsp : ((c :: rest) ++ (['-', '-', 'l', 't', 'r'] ++ ' ' :: tail)).span isLangChar
        = ((c :: rest) ++ ['-', '-', 'l', 't', 'r'], ' ' :: tail) := by
      rw [← List.append_assoc]
      exact span_append_stop _ _ ' ' tail hall' (by decide)
    simp only [List.append_assoc, List.cons_append, readLangDir12, hst, Bool.not_true]
    simp only [readLangTagRun, ← List.cons_append, hsp]
    rw [String.toList_ofList,
      show (c :: rest) ++ ['-', '-', 'l', 't', 'r'] = (c :: rest) ++ '-' :: '-' :: ['l', 't', 'r'] from rfl,
      splitOnDoubleHyphen_dir _ 0 [] _ hval]
    simp only [List.reverse_nil, List.nil_append, hval, Bool.not_true]
    rw [hb]
    exact ⟨_, rfl⟩
  | rtl =>
    have hall' : ((c :: rest) ++ ['-', '-', 'r', 't', 'l']).all isLangChar = true := by
      simp only [List.all_append, hall, Bool.true_and]; decide
    have hsp : ((c :: rest) ++ (['-', '-', 'r', 't', 'l'] ++ ' ' :: tail)).span isLangChar
        = ((c :: rest) ++ ['-', '-', 'r', 't', 'l'], ' ' :: tail) := by
      rw [← List.append_assoc]
      exact span_append_stop _ _ ' ' tail hall' (by decide)
    simp only [List.append_assoc, List.cons_append, readLangDir12, hst, Bool.not_true]
    simp only [readLangTagRun, ← List.cons_append, hsp]
    rw [String.toList_ofList,
      show (c :: rest) ++ ['-', '-', 'r', 't', 'l'] = (c :: rest) ++ '-' :: '-' :: ['r', 't', 'l'] from rfl,
      splitOnDoubleHyphen_dir _ 0 [] _ hval]
    simp only [List.reverse_nil, List.nil_append, hval, Bool.not_true]
    rw [hb]
    exact ⟨_, rfl⟩

/-- **A literal in the domain reads back** (RDF 1.2 reader), followed by
` .`, ` )`, ` <` or ` _`: what follows an object in a line, in a triple term
and before an N-Quads graph label. -/
theorem readLiteral12_safe (pos : Nat) (wl : WfLiteral) (str : String) (c : Char) (tail : List Char)
    (hs : Term.ntLex (.literal wl) = true) (h : Term.toNTriples .rdf12 (.literal wl) = .ok str)
    (hc : c = '.' ∨ c = ')' ∨ c = '<' ∨ c = '_') :
    ∃ p, readLiteral .rdf12 pos (str.toList ++ ' ' :: c :: tail) = .ok (wl, p, ' ' :: c :: tail) := by
  obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := wl
  simp only [Term.ntLex, Bool.and_eq_true] at hs
  obtain ⟨hdt, htag⟩ := hs
  cases tag with
  | none =>
    cases dir with
    | some d => simp [literalWf] at hwf
    | none =>
      by_cases hx : dt = xsdString
      · subst hx
        simp only [Term.toNTriples, if_pos, Except.ok.injEq] at h
        subst h
        obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape pos lex (' ' :: c :: tail)
        have he : ("\"" ++ escapeLiteral lex ++ "\"").toList ++ ' ' :: c :: tail
            = '"' :: ((escapeLiteral lex).toList ++ '"' :: ' ' :: c :: tail) := by simp
        rw [he]
        unfold readLiteral
        rw [hp1]
        rcases hc with rfl | rfl | rfl | rfl <;>
        · simp only [skipWs_space _ (by decide : isNtWs '.' = false),
            skipWs_space _ (by decide : isNtWs ')' = false),
            skipWs_space _ (by decide : isNtWs '<' = false),
            skipWs_space _ (by decide : isNtWs '_' = false), mkLiteral_wf _ _ hwf]
          exact ⟨_, rfl⟩
      · simp only [Term.toNTriples, if_neg hx, Except.ok.injEq] at h
        subst h
        obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape pos lex
          ('^' :: '^' :: '<' :: (dt.val.toList ++ '>' :: ' ' :: c :: tail))
        have he : ("\"" ++ escapeLiteral lex ++ "\"^^<" ++ dt.val ++ ">").toList ++ ' ' :: c :: tail
            = '"' :: ((escapeLiteral lex).toList ++ '"' ::
                '^' :: '^' :: '<' :: (dt.val.toList ++ '>' :: ' ' :: c :: tail)) := by simp
        rw [he]
        unfold readLiteral
        rw [hp1]
        simp only [skipWs_stop _ (by decide : isNtWs '^' = false), readDatatypeWs12,
          skipWs_stop _ (by decide : isNtWs '<' = false),
          readIriRef_printSafe _ dt _ hdt, mkIri_val, mkLiteral_wf _ _ hwf]
        exact ⟨_, rfl⟩
  | some tg =>
    simp only [Option.all_some] at htag
    cases dir with
    | none =>
      have hdt' : dt = rdfLangString := Subtype.ext (by simp [literalWf] at hwf; exact hwf.1)
      subst hdt'
      simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape pos lex ('@' :: (tg.toList ++ ' ' :: c :: tail))
      obtain ⟨p2, hp2⟩ := readLangDir12_plain p1 tg (c :: tail) htag
      have he : ("\"" ++ escapeLiteral lex ++ "\"@" ++ tg).toList ++ ' ' :: c :: tail
          = '"' :: ((escapeLiteral lex).toList ++ '"' :: '@' :: (tg.toList ++ ' ' :: c :: tail)) := by simp
      rw [he]
      unfold readLiteral
      rw [hp1]
      simp only [skipWs_stop _ (by decide : isNtWs '@' = false), hp2]
      simp only [Option.map_none, mkLiteral_wf _ _ hwf]
      exact ⟨_, rfl⟩
    | some d =>
      have hdt' : dt = rdfDirLangString := Subtype.ext (by simp [literalWf] at hwf; exact hwf.1)
      subst hdt'
      cases d with
      | ltr =>
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq, if_neg (by decide : ¬ (Mode.rdf12 = Mode.rdf11))] at h
        subst h
        obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape pos lex
          ('@' :: (tg.toList ++ ('-' :: '-' :: ['l', 't', 'r']) ++ ' ' :: c :: tail))
        obtain ⟨p2, hp2⟩ := readLangDir12_dir p1 tg .ltr (c :: tail) htag
        dsimp only at hp2
        have he : ("\"" ++ escapeLiteral lex ++ "\"@" ++ tg ++ "--ltr").toList ++ ' ' :: c :: tail
            = '"' :: ((escapeLiteral lex).toList ++ '"' ::
                '@' :: (tg.toList ++ ('-' :: '-' :: ['l', 't', 'r']) ++ ' ' :: c :: tail)) := by simp
        rw [he]
        unfold readLiteral
        rw [hp1]
        simp only [skipWs_stop _ (by decide : isNtWs '@' = false), hp2]
        simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, mkLiteral_wf _ _ hwf]
        exact ⟨_, rfl⟩
      | rtl =>
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq, if_neg (by decide : ¬ (Mode.rdf12 = Mode.rdf11))] at h
        subst h
        obtain ⟨p1, hp1⟩ := readStringLiteralQuoted_escape pos lex
          ('@' :: (tg.toList ++ ('-' :: '-' :: ['r', 't', 'l']) ++ ' ' :: c :: tail))
        obtain ⟨p2, hp2⟩ := readLangDir12_dir p1 tg .rtl (c :: tail) htag
        dsimp only at hp2
        have he : ("\"" ++ escapeLiteral lex ++ "\"@" ++ tg ++ "--rtl").toList ++ ' ' :: c :: tail
            = '"' :: ((escapeLiteral lex).toList ++ '"' ::
                '@' :: (tg.toList ++ ('-' :: '-' :: ['r', 't', 'l']) ++ ' ' :: c :: tail)) := by simp
        rw [he]
        unfold readLiteral
        rw [hp1]
        simp only [skipWs_stop _ (by decide : isNtWs '@' = false), hp2]
        simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, mkLiteral_wf _ _ hwf]
        exact ⟨_, rfl⟩

/-- The text of a term starts with `<`, `_` or `"`: never white space, `@`
or `^`. -/
theorem term_toNTriples_head (mode : Mode) (t : Term) (str : String) (tail : List Char)
    (h : Term.toNTriples mode t = .ok str) :
    ∃ c r, str.toList ++ tail = c :: r ∧ (c = '<' ∨ c = '_' ∨ c = '"') := by
  cases t with
  | iri i =>
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    exact ⟨'<', _, by simp; rfl, by decide⟩
  | bnode b =>
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    exact ⟨'_', _, by simp; rfl, by decide⟩
  | tripleTerm s p o =>
    unfold Term.toNTriples at h
    split at h
    · cases h
    · cases ho : Term.toNTriples mode o with
      | error e => rw [ho] at h; cases h
      | ok oStr =>
        rw [ho] at h
        simp only [Except.ok.injEq] at h; subst h
        exact ⟨'<', _, by simp; rfl, by decide⟩
  | literal wl =>
    obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := wl
    cases tag with
    | none =>
      by_cases hx : dt = xsdString
      · simp only [Term.toNTriples, if_pos hx, Except.ok.injEq] at h; subst h
        exact ⟨'"', _, by simp; rfl, by decide⟩
      · simp only [Term.toNTriples, if_neg hx, Except.ok.injEq] at h; subst h
        exact ⟨'"', _, by simp; rfl, by decide⟩
    | some tg =>
      cases dir with
      | none =>
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq] at h; subst h
        exact ⟨'"', _, by simp; rfl, by decide⟩
      | some d =>
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h
        split at h
        · cases h
        · simp only [Except.ok.injEq] at h; subst h
          exact ⟨'"', _, by simp; rfl, by decide⟩

/-! ### No line break in the text of a term -/

theorem nl_not_mem_iri {s : String} (h : iriPrintSafe s = true) : '\n' ∉ s.toList := by
  intro hm
  have := List.all_eq_true.mp h _ hm
  revert this; decide

theorem nl_not_mem_bnode {b : String} (h : bnodeLabelSafe b = true) : '\n' ∉ b.toList := by
  unfold bnodeLabelSafe at h
  cases hv : b.toList with
  | nil => simp
  | cons c0 rest =>
    rw [hv] at h
    simp only [bnodeLabelCharsSafe, Bool.and_eq_true] at h
    obtain ⟨⟨hst, hall⟩, -⟩ := h
    intro hm
    rcases List.mem_cons.mp hm with he | he
    · rw [← he] at hst; revert hst; decide
    · have := List.all_eq_true.mp hall _ he
      revert this; decide

theorem nl_not_mem_lang {tag : String} (h : langTagSafe tag = true) : '\n' ∉ tag.toList := by
  obtain ⟨c, rest, hv, -, hall, -⟩ := langTagSafe_parts h
  rw [hv]
  intro hm
  have := List.all_eq_true.mp hall _ hm
  revert this; decide

theorem nl_not_mem_escape (s : String) : '\n' ∉ (escapeLiteral s).toList := by
  rw [escapeLiteral_toList]
  intro hm
  obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hm
  revert hc
  unfold escChar
  split <;> simp_all [eq_comm]

theorem nl_not_mem_subject (s : Subject) (h : Subject.ntLex s = true) :
    '\n' ∉ (Subject.toNTriples s).toList := by
  cases s with
  | iri i =>
    have := nl_not_mem_iri (s := i.val) h
    simp [Subject.toNTriples]; exact this
  | bnode b =>
    have := nl_not_mem_bnode (b := b) h
    simp [Subject.toNTriples]; exact this

theorem nl_not_mem_term (mode : Mode) : ∀ (t : Term) (str : String),
    Term.ntLex t = true → Term.toNTriples mode t = .ok str → '\n' ∉ str.toList
  | .iri i, str, hs, h => by
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    have := nl_not_mem_iri (s := i.val) hs
    simp; exact this
  | .bnode b, str, hs, h => by
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    have := nl_not_mem_bnode (b := b) hs
    simp; exact this
  | .tripleTerm s p o, str, hs, h => by
    simp only [Term.ntLex, Bool.and_eq_true] at hs
    obtain ⟨⟨hss, hps⟩, hos⟩ := hs
    unfold Term.toNTriples at h
    split at h
    · cases h
    · cases ho : Term.toNTriples mode o with
      | error e => rw [ho] at h; cases h
      | ok oStr =>
        rw [ho] at h
        simp only [Except.ok.injEq] at h; subst h
        have h1 := nl_not_mem_subject s hss
        have h2 := nl_not_mem_iri (s := p.val) hps
        have h3 := nl_not_mem_term mode o oStr hos ho
        simp only [String.toList_append, List.mem_append, not_or]
        exact ⟨⟨⟨⟨⟨⟨by decide, h1⟩, by decide⟩, h2⟩, by decide⟩, h3⟩, by decide⟩
  | .literal wl, str, hs, h => by
    obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := wl
    simp only [Term.ntLex, Bool.and_eq_true] at hs
    obtain ⟨hdt, htag⟩ := hs
    have he := nl_not_mem_escape lex
    have hd := nl_not_mem_iri (s := dt.val) hdt
    cases tag with
    | none =>
      by_cases hx : dt = xsdString
      · simp only [Term.toNTriples, if_pos hx, Except.ok.injEq] at h; subst h
        simp only [String.toList_append, List.mem_append, not_or]
        exact ⟨⟨by decide, he⟩, by decide⟩
      · simp only [Term.toNTriples, if_neg hx, Except.ok.injEq] at h; subst h
        simp only [String.toList_append, List.mem_append, not_or]
        exact ⟨⟨⟨⟨by decide, he⟩, by decide⟩, hd⟩, by decide⟩
    | some tg =>
      simp only [Option.all_some] at htag
      have hl := nl_not_mem_lang htag
      cases dir with
      | none =>
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq] at h; subst h
        simp only [String.toList_append, List.mem_append, not_or]
        exact ⟨⟨⟨by decide, he⟩, by decide⟩, hl⟩
      | some d =>
        simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h
        split at h
        · cases h
        · simp only [Except.ok.injEq] at h; subst h
          simp only [String.toList_append, List.mem_append, not_or]
          refine ⟨⟨⟨⟨by decide, he⟩, by decide⟩, hl⟩, ?_⟩
          cases d <;> decide

/-! ### The fuel of the RDF 1.2 object -/

theorem lineFuelGo_ge_acc : ∀ (cs : List Char) (acc : Nat), acc ≤ lineFuelGo cs acc
  | [], acc => by simp [lineFuelGo]
  | c :: cs, acc => by
    unfold lineFuelGo
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ acc) (lineFuelGo_ge_acc cs (acc + 1))

theorem lineFuelGo_ge : ∀ (xs r : List Char) (acc : Nat), '\n' ∉ xs →
    acc + xs.length ≤ lineFuelGo (xs ++ r) acc
  | [], r, acc, _ => by simpa using lineFuelGo_ge_acc r acc
  | x :: xs, r, acc, h => by
    have hx : x ≠ '\n' := fun e => h (e ▸ List.mem_cons_self)
    have ih := lineFuelGo_ge xs r (acc + 1) (fun hm => h (List.mem_cons_of_mem _ hm))
    simp only [List.cons_append, lineFuelGo, beq_iff_eq, hx, if_false, List.length_cons]
    omega

/-! ### The RDF 1.2 object -/

theorem iri_text_ne_open (i : WfIri) (tail : List Char) (h : iriPrintSafe i.val = true) (rest : List Char) :
    i.val.toList ++ '>' :: tail ≠ '<' :: rest := by
  intro he
  cases hv : i.val.toList with
  | nil => rw [hv] at he; simp at he
  | cons c r =>
    rw [hv] at he
    simp only [List.cons_append, List.cons.injEq] at he
    have := List.all_eq_true.mp h c (by rw [hv]; exact List.mem_cons_self)
    rw [he.1] at this; revert this; decide

theorem readObject12_iri (f pos : Nat) (i : WfIri) (tail : List Char) (h : iriPrintSafe i.val = true) :
    readObject12 (f + 1) pos ('<' :: (i.val.toList ++ '>' :: tail))
      = .ok (.iri i, pos + i.val.length + 2, tail) := by
  rw [readObject12]
  · rw [readIriRef_printSafe pos i tail h]; simp only [mkIri_val]
  · intro rest he; exact iri_text_ne_open i tail h _ he
  · intro rest he; exact iri_text_ne_open i tail h _ he

/-- The text of a literal starts with `"`. -/
theorem literal_text_head (mode : Mode) (wl : WfLiteral) (str : String) (tail : List Char)
    (h : Term.toNTriples mode (.literal wl) = .ok str) : ∃ r, str.toList ++ tail = '"' :: r := by
  obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := wl
  cases tag with
  | none =>
    by_cases hx : dt = xsdString
    · simp only [Term.toNTriples, if_pos hx, Except.ok.injEq] at h; subst h
      exact ⟨_, by simp; rfl⟩
    · simp only [Term.toNTriples, if_neg hx, Except.ok.injEq] at h; subst h
      exact ⟨_, by simp; rfl⟩
  | some tg =>
    cases dir with
    | none =>
      simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h; simp only [Except.ok.injEq] at h; subst h
      exact ⟨_, by simp; rfl⟩
    | some d =>
      simp only [Term.toNTriples] at h; replace h := ite_error_eq_ok h
      split at h
      · cases h
      · simp only [Except.ok.injEq] at h; subst h
        exact ⟨_, by simp; rfl⟩

/-- **An object in the domain reads back** (RDF 1.2 reader), triple terms
nested to any depth, with fuel more than the length of its text. -/
theorem readObject12_safe : ∀ (t : Term) (fuel pos : Nat) (str : String) (c : Char) (tail : List Char),
    Term.ntLex t = true → Term.toNTriples .rdf12 t = .ok str → str.toList.length < fuel →
    (c = '.' ∨ c = ')' ∨ c = '<' ∨ c = '_') →
    ∃ p, readObject12 fuel pos (str.toList ++ ' ' :: c :: tail) = .ok (t, p, ' ' :: c :: tail)
  | .iri i, fuel, pos, str, c, tail, hs, h, hf, _ => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    have hc : ("<" ++ i.val ++ ">").toList ++ ' ' :: c :: tail
        = '<' :: (i.val.toList ++ '>' :: ' ' :: c :: tail) := by simp
    rw [hc, readObject12_iri f pos i _ hs]
    exact ⟨_, rfl⟩
  | .bnode b, fuel, pos, str, c, tail, hs, h, hf, _ => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [Term.toNTriples, Except.ok.injEq] at h; subst h
    have hc : ("_:" ++ b).toList ++ ' ' :: c :: tail = '_' :: ':' :: (b.toList ++ ' ' :: c :: tail) := by
      simp
    obtain ⟨p, hp⟩ := readBlankNodeLabel_safe pos b (c :: tail) hs
    rw [hc, readObject12.eq_5, hp]
    exact ⟨p, rfl⟩
  | .literal wl, fuel, pos, str, c, tail, hs, h, hf, hc => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r, hr⟩ := literal_text_head .rdf12 wl str (' ' :: c :: tail) h
    obtain ⟨p, hp⟩ := readLiteral12_safe pos wl str c tail hs h hc
    rw [hr] at hp ⊢
    rw [readObject12.eq_6, hp]
    exact ⟨p, rfl⟩
  | .tripleTerm s pr o, fuel, pos, str, c, tail, hs, h, hf, hc => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [Term.ntLex, Bool.and_eq_true] at hs
    obtain ⟨⟨hss, hps⟩, hos⟩ := hs
    unfold Term.toNTriples at h
    rw [if_neg (by decide)] at h
    cases ho : Term.toNTriples .rdf12 o with
    | error e => rw [ho] at h; cases h
    | ok oStr =>
      rw [ho] at h
      simp only [Except.ok.injEq] at h; subst h
      have hlen : oStr.toList.length < f := by
        simp only [String.toList_append, List.length_append] at hf
        have : " )>>".toList.length = 4 := by decide
        omega
      have hcs : ("<<( " ++ Subject.toNTriples s ++ " <" ++ pr.val ++ "> " ++ oStr ++ " )>>").toList
            ++ ' ' :: c :: tail
          = '<' :: '<' :: '(' :: ' ' :: ((Subject.toNTriples s).toList ++ ' ' :: '<' ::
              (pr.val.toList ++ '>' :: ' ' ::
                (oStr.toList ++ ' ' :: ')' :: '>' :: '>' :: ' ' :: c :: tail))) := by
        simp
      rw [hcs, readObject12.eq_2]
      obtain ⟨r0, hr0⟩ := subject_toNTriples_head s (' ' :: '<' ::
              (pr.val.toList ++ '>' :: ' ' ::
                (oStr.toList ++ ' ' :: ')' :: '>' :: '>' :: ' ' :: c :: tail)))
      have hws : skipWs (pos + 3) (' ' :: ((Subject.toNTriples s).toList ++ ' ' :: '<' ::
              (pr.val.toList ++ '>' :: ' ' ::
                (oStr.toList ++ ' ' :: ')' :: '>' :: '>' :: ' ' :: c :: tail))))
          = (pos + 3 + 1, (Subject.toNTriples s).toList ++ ' ' :: '<' ::
              (pr.val.toList ++ '>' :: ' ' ::
                (oStr.toList ++ ' ' :: ')' :: '>' :: '>' :: ' ' :: c :: tail))) := by
        rcases hr0 with hr0 | hr0 <;> rw [hr0] <;> exact skipWs_space _ (by decide)
      obtain ⟨p2, hp2⟩ := readSubject_safe (pos + 3 + 1) s ('<' ::
              (pr.val.toList ++ '>' :: ' ' ::
                (oStr.toList ++ ' ' :: ')' :: '>' :: '>' :: ' ' :: c :: tail))) hss
      obtain ⟨c5, r5, hcr, hc5⟩ := term_toNTriples_head .rdf12 o oStr (' ' :: ')' :: '>' :: '>' :: ' ' :: c :: tail) ho
      have hc5ws : isNtWs c5 = false := by rcases hc5 with rfl | rfl | rfl <;> decide
      obtain ⟨p6, hp6⟩ := readObject12_safe o f (p2 + 1 + pr.val.length + 2 + 1) oStr ')'
        ('>' :: '>' :: ' ' :: c :: tail) hos ho hlen (Or.inr (Or.inl rfl))
      simp only [hws]
      rw [hp2]
      simp only [skipWs_space _ (by decide : isNtWs '<' = false)]
      rw [readPredicate_printSafe _ pr _ hps]
      simp only
      rw [hcr, skipWs_space _ hc5ws, ← hcr, hp6]
      simp only [skipWs_space _ (by decide : isNtWs ')' = false)]
      exact ⟨_, rfl⟩

/-- **One line in the domain reads back** (RDF 1.2 reader). The object fuel
`lineFuel` counts the characters before the line break, and the text of the
object has none (`nl_not_mem_term`), so the fuel is more than its length. -/
theorem readTriple12_line (pos : Nat) (t : Triple) (line : String) (tail : List Char)
    (hs : Triple.ntLex t = true) (h : Triple.toNTriples .rdf12 t = .ok line) :
    ∃ p, readTriple12 pos (line.toList ++ tail) = .ok (t, p, '\n' :: tail) := by
  obtain ⟨s, pr, o⟩ := t
  simp only [Triple.ntLex, Bool.and_eq_true] at hs
  obtain ⟨⟨hss, hps⟩, hos⟩ := hs
  unfold Triple.toNTriples at h
  cases ho : Term.toNTriples .rdf12 o with
  | error e => simp [ho] at h
  | ok oStr =>
    simp only [ho, Except.ok.injEq] at h
    subst h
    have hc : (Subject.toNTriples s ++ " <" ++ pr.val ++ "> " ++ oStr ++ " .\n").toList ++ tail
        = (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))) := by simp
    rw [hc]
    obtain ⟨r0, hr0⟩ := subject_toNTriples_head s (' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))))
    have hws0 : skipWs pos ((Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))))
        = (pos, (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail)))) := by
      rcases hr0 with hr0 | hr0 <;> rw [hr0] <;> exact skipWs_stop pos (by decide)
    obtain ⟨p2, hp2⟩ := readSubject_safe pos s ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: '.' :: '\n' :: tail))) hss
    obtain ⟨c, r, hcr, hc⟩ := term_toNTriples_head .rdf12 o oStr (' ' :: '.' :: '\n' :: tail) ho
    have hcws : isNtWs c = false := by rcases hc with rfl | rfl | rfl <;> decide
    have hfuel : oStr.toList.length < lineFuel (oStr.toList ++ ' ' :: '.' :: '\n' :: tail) := by
      have := lineFuelGo_ge oStr.toList (' ' :: '.' :: '\n' :: tail) 1 (nl_not_mem_term .rdf12 o oStr hos ho)
      unfold lineFuel
      omega
    obtain ⟨p6, hp6⟩ := readObject12_safe o _ (p2 + 1 + pr.val.length + 2 + 1) oStr '.' ('\n' :: tail)
      hos ho hfuel (Or.inl rfl)
    unfold readTriple12
    rw [hws0]
    dsimp only
    rw [hp2]
    dsimp only
    rw [skipWs_space _ (by decide : isNtWs '<' = false)]
    dsimp only
    rw [readPredicate_printSafe _ pr _ hps]
    dsimp only
    rw [hcr, skipWs_space _ hcws, ← hcr, hp6]
    dsimp only
    rw [skipWs_space _ (by decide : isNtWs '.' = false)]
    exact ⟨_, rfl⟩

/-- The text of a line starts with `<` or `_`. -/
theorem triple_toNTriples_head (mode : Mode) (t : Triple) (line : String) (tail : List Char)
    (h : Triple.toNTriples mode t = .ok line) :
    ∃ r, line.toList ++ tail = '<' :: r ∨ line.toList ++ tail = '_' :: r := by
  unfold Triple.toNTriples at h
  cases ho : Term.toNTriples mode t.o with
  | error e => simp [ho] at h
  | ok oStr =>
    simp only [ho, Except.ok.injEq] at h
    subst h
    obtain ⟨r, hr⟩ := subject_toNTriples_head t.s
      ((" <" ++ t.p.val ++ "> " ++ oStr ++ " .\n").toList ++ tail)
    refine ⟨r, ?_⟩
    simpa [String.append_assoc] using hr

/-- The line of a triple has at least one character. -/
theorem triple_toNTriples_ne_nil (mode : Mode) (t : Triple) (line : String)
    (h : Triple.toNTriples mode t = .ok line) : line.toList ≠ [] := by
  obtain ⟨r, hr⟩ := triple_toNTriples_head mode t line [] h
  rw [List.append_nil] at hr
  rcases hr with hr | hr <;> rw [hr] <;> simp

/-! ## The document -/

theorem skipComment_nl (p : Nat) (r : List Char) : skipComment p ('\n' :: r) = (p, '\n' :: r) := rfl

theorem skipEol_nl (p : Nat) (r : List Char) : skipEol p ('\n' :: r) = (p + 1, r) := rfl

/-- The line reader of `mode`. -/
def readTripleOf : Mode → Nat → List Char → Except ParseError (Triple × Nat × List Char)
  | .rdf11 => readTriple11
  | .rdf12 => readTriple12

/-- One line in the domain reads back, in either mode. -/
theorem readTripleOf_line (mode : Mode) (pos : Nat) (t : Triple) (line : String) (tail : List Char)
    (hs : Triple.ntLex t = true) (h : Triple.toNTriples mode t = .ok line) :
    ∃ p, readTripleOf mode pos (line.toList ++ tail) = .ok (t, p, '\n' :: tail) := by
  cases mode
  · exact readTriple11_line pos t line tail hs h
  · exact readTriple12_line pos t line tail hs h

/-- The lines of a graph whose triples all serialise, read in order. -/
theorem parseLinesAcc_lines (mode : Mode) : ∀ (g : Graph) (fuel pos : Nat) (acc : List Triple),
    g.all Triple.ntLex = true →
    g.findSome? (Triple.nTriplesError? mode) = none →
    (String.join (g.map (Triple.toNTriplesLine mode))).toList.length < fuel →
    parseLinesAcc mode fuel pos (String.join (g.map (Triple.toNTriplesLine mode))).toList acc
      = .ok (acc.reverse ++ g)
  | [], fuel, pos, acc, _, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [parseLinesAcc, skipWs, List.span, List.span.loop]
  | t :: g, fuel, pos, acc, hs, he, hf => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    simp only [List.findSome?_cons] at he
    cases hte : Triple.nTriplesError? mode t with
    | some e => rw [hte] at he; cases he
    | none =>
      rw [hte] at he
      have hl : ∃ line, Triple.toNTriples mode t = .ok line := by
        cases hx : Triple.toNTriples mode t with
        | error e => simp [Triple.nTriplesError?, hx] at hte
        | ok line => exact ⟨line, rfl⟩
      obtain ⟨line, hline⟩ := hl
      have hli : Triple.toNTriplesLine mode t = line := by simp [Triple.toNTriplesLine, hline]
      simp only [List.map_cons, String.join_cons, hli, String.toList_append] at hf ⊢
      generalize hR : (String.join (g.map (Triple.toNTriplesLine mode))).toList = R at hf
      have hne := triple_toNTriples_ne_nil mode t line hline
      have hlen : line.toList.length ≥ 1 := by
        cases hh : line.toList with
        | nil => exact absurd hh hne
        | cons _ _ => simp
      rw [List.length_append] at hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfR : R.length < f := by omega
      obtain ⟨p, hp⟩ := readTripleOf_line mode pos t line R hs.1 hline
      obtain ⟨r0, hr0⟩ := triple_toNTriples_head mode t line R hline
      have ih := parseLinesAcc_lines mode g f (p + 1) (t :: acc) hs.2 he (by rw [hR]; exact hfR)
      rw [hR] at ih
      rw [parseLinesAcc]
      rcases hr0 with hr0 | hr0 <;>
      · rw [hr0] at hp
        rw [hr0, skipWs_stop pos (by decide)]
        dsimp only
        split
        · next h => cases h
        · next h => simp at h
        · next h => simp at h
        · next h => simp at h
        · cases mode <;>
          · simp only [readTripleOf] at hp
            simp only [hp]
            simp only [skipWs_stop _ (by decide : isNtWs '\n' = false), skipComment_nl, skipEol_nl]
            rw [ih]
            simp

/-- **The N-Triples document round trip**, in both modes. A graph whose
triples are in the domain (`Triple.ntLex`), written by `Graph.toNTriples`,
is read back by `parseNTriples` as the same list of triples, in order. -/
theorem parseNTriples_toNTriples (mode : Mode) (g : Graph) (hs : g.all Triple.ntLex = true)
    (text : String) (h : Graph.toNTriples g mode = .ok text) : parseNTriples text mode = .ok g := by
  rw [Graph.toNTriples_eq_lines] at h
  unfold Graph.firstNTriplesError at h
  cases he : g.findSome? (Triple.nTriplesError? mode) with
  | some e => rw [he] at h; cases h
  | none =>
    rw [he] at h
    simp only [Except.ok.injEq] at h
    subst h
    unfold parseNTriples
    rw [parseLinesAcc_lines mode g _ 0 [] hs he (by omega)]
    simp

/-- RDF 1.1 mode. -/
theorem parseNTriples_toNTriples11 (g : Graph) (hs : g.all Triple.ntLex = true) (text : String)
    (h : Graph.toNTriples g .rdf11 = .ok text) : parseNTriples text .rdf11 = .ok g :=
  parseNTriples_toNTriples .rdf11 g hs text h

/-! ## Outside the domain: the counter-examples

Each restriction of `Triple.ntLex` is needed: without it, the statement of
`parseNTriples_toNTriples` is false. `Graph.toNTriples` writes a blank-node
label as it is, so a label outside BLANK_NODE_LABEL gives a text that the
parser refuses; the writers of `RDF/Sink.lean` relabel first
(`Dataset.relabelForWrite`), so their domain has no such condition
(`Triple.ntSafe`). A language tag outside LANGTAG [144s] (RDF 1.2: also a
subtag of more than 8 characters) is refused by the writer with an error
(`langTagWritable`, https://github.com/danbri/factoidal/issues/986): `none`
below. -/

private def cxP : WfIri := ⟨"http://example.org/p", by decide⟩
private def cxO : WfIri := ⟨"http://example.org/o", by decide⟩

/-- Write one triple, then parse the text back. `none`: the writer refused. -/
private def cxRoundTrip (mode : Mode) (t : Triple) : Option Bool :=
  match Graph.toNTriples [t] mode with
  | .error _ => none
  | .ok text => some ((parseNTriples text mode).toOption == some [t])

-- BLANK_NODE_LABEL: the empty label, a space in the label, a `.` at the end.
#guard bnodeLabelSafe "" == false
#guard cxRoundTrip .rdf11 { s := .bnode "", p := cxP, o := .iri cxO } == some false
#guard bnodeLabelSafe "a b" == false
#guard cxRoundTrip .rdf11 { s := .bnode "a b", p := cxP, o := .iri cxO } == some false
#guard bnodeLabelSafe "a." == false
#guard cxRoundTrip .rdf11 { s := .bnode "a.", p := cxP, o := .iri cxO } == some false
-- LANGTAG: the empty tag, a space in the tag.
#guard langTagSafe "" == false
#guard cxRoundTrip .rdf11 { s := .iri cxO, p := cxP, o := .literal (Literal.langString "x" "") } == none
#guard langTagSafe "en US" == false
#guard cxRoundTrip .rdf11 { s := .iri cxO, p := cxP, o := .literal (Literal.langString "x" "en US") }
  == none
-- A subtag of nine characters: the RDF 1.1 writer and reader keep it, the RDF 1.2
-- writer refuses it (BCP 47 section 2.1, `validLangSubtags`); the domain leaves it out.
#guard langTagSafe "abcdefghi" == false
#guard cxRoundTrip .rdf11 { s := .iri cxO, p := cxP, o := .literal (Literal.langString "x" "abcdefghi") }
  == some true
#guard cxRoundTrip .rdf12 { s := .iri cxO, p := cxP, o := .literal (Literal.langString "x" "abcdefghi") }
  == none
-- In the domain: every kind of term, both modes.
#guard cxRoundTrip .rdf11 { s := .bnode "b.1", p := cxP, o := .literal (Literal.langString "q\"\n" "en-GB") }
  == some true
private def cxNested : Triple :=
  { s := .bnode "b1", p := cxP,
    o := .tripleTerm (.bnode "b2") cxP (.tripleTerm (.iri cxO) cxP (.literal (Literal.dirLangString "y" "ar" .rtl))) }
#guard cxRoundTrip .rdf12 cxNested == some true

/-! ## Axiom audit -/

#print axioms bnodeLabelSafe_eq_isBlankNodeLabel
#print axioms Triple.ntLex_of_ntSafe
#print axioms Triple.ntSafe_renameBnodes
#print axioms Triple.ntLex_renameBnodes
#print axioms readBlankNodeLabel_safe
#print axioms readStringLiteralBody_escape
#print axioms readLangTag_safe
#print axioms readLangDir12_plain
#print axioms readLangDir12_dir
#print axioms readObject11_safe
#print axioms readObject12_safe
#print axioms nl_not_mem_term
#print axioms readTriple11_line
#print axioms readTriple12_line
#print axioms parseLinesAcc_lines
#print axioms parseNTriples_toNTriples

end L4Factoidal.Syntax.NTriplesRoundTrip
