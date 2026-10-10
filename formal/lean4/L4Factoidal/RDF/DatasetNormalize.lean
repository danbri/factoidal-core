/-
L4Factoidal.RDF.DatasetNormalize — the normalisation the canonical N-Quads
round trip performs, as a function on `Dataset`, and the theorem that the
two are equal.

The command line (`Wasm/Cli.lean`) used to give `query`, `update`,
`canonicalize` and `closure` their input by writing the parsed dataset as
canonical N-Quads text (`Dataset.toCanonicalNQuads`) and parsing the text
again (`parseNQuadsFast`): 74.7 percent of the instructions of a COUNT
query (https://github.com/danbri/factoidal/issues/724). The round trip is
not the identity. It changes a dataset in two ways, and both are the RDF 1.1
Concepts reading of the data:

* RDF 1.1 Concepts §3: "An RDF graph is a set of RDF triples." The Turtle
  reader keeps a repeated triple as two list entries; the N-Quads reader
  keeps each quad of a graph once (`addQuadFast`, set semantics by
  `Triple.eqb`), and merges named graphs of one name.
* RDF 1.1 Concepts §3.3: "Lexical representations of language tags MAY be
  converted to lower case. The value space of language tags is always in
  lower case." The canonical form writes tags in lower case.

`normalizeDataset` performs exactly these two steps: it lower-cases every
language tag (also inside RDF 1.2 triple terms) and adds the quads, in the
order the canonical document lists them, to the same indexed accumulator
`parseNQuadsFast` uses. `parseNQuadsFast_toCanonicalNQuads` proves

    parseNQuadsFast (toCanonicalNQuads ds) mode = .ok (normalizeDataset ds)

for every dataset that `roundTripSafe mode` accepts. The hypothesis is a
decidable syntactic check of the terms; it does not mention the parser:

* every IRI is print-safe (`iriPrintSafe`: no character the IRIREF
  production refuses raw — `RDF.isIri` admits a space or a control
  character, and such an IRI does not survive the text form);
* every blank-node label matches BLANK_NODE_LABEL;
* every language tag, lower-cased, matches LANGTAG with subtags of 1 to 8
  characters (the check `readLangDir12` makes);
* no lexical form contains a character the canonical form writes as a
  `\u` escape (C0 controls other than the six ECHAR ones, DEL, U+FFFE and
  U+FFFF; this module proves the ECHAR escapes, not the hexadecimal ones);
* in RDF 1.1 mode, no triple term and no base direction (the 1.1 grammar
  refuses both).

`datasetForOps` is what the command line calls: the normalised dataset when
the check passes, the text round trip otherwise. `datasetForOps_eq` proves it
equal to the text round trip for EVERY dataset, with no hypothesis, so the
command line's answers are unchanged, row order included.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.NTriplesRoundTrip
import L4Factoidal.Syntax.NQuadsFast

namespace L4Factoidal.RDF

open L4Factoidal.Syntax
open L4Factoidal.Syntax.NTriplesRoundTrip
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## The normalisation -/

/-- Lower-case the language tag of a literal (RDF 1.1 Concepts §3.3). -/
def Literal.lowerTag (l : Literal) : Literal :=
  { l with langTag := l.langTag.map String.toLower }

theorem literalWf_lowerTag (l : Literal) : literalWf l.lowerTag = literalWf l := by
  unfold literalWf Literal.lowerTag
  cases l.langTag <;> cases l.direction <;> rfl

def WfLiteral.lowerTag (l : WfLiteral) : WfLiteral :=
  ⟨l.val.lowerTag, by rw [literalWf_lowerTag]; exact l.property⟩

/-- Lower-case every language tag of a term, inside triple terms too. -/
def Term.lowerTags : Term → Term
  | .iri i => .iri i
  | .bnode b => .bnode b
  | .literal l => .literal l.lowerTag
  | .tripleTerm s p o => .tripleTerm s p o.lowerTags

def Triple.lowerTags (t : Triple) : Triple := { t with o := t.o.lowerTags }

/-- The quads of a dataset in the order `Dataset.toCanonicalNQuads` writes
them: the default graph, then each named graph in list order. -/
def Dataset.quadList (ds : Dataset) : List (Triple × Option Subject) :=
  ds.default.map (fun t => (t, none)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))

/-- RDF 1.1 Concepts §3 and §3.3: one quad per (triple, graph), graphs of one
name merged, language tags in lower case. The quads are added in the
canonical document's order to the accumulator `parseNQuadsFast` uses, so
the result keeps first-occurrence order. -/
def normalizeDataset (ds : Dataset) : Dataset :=
  (ds.quadList.foldl (fun acc q => addQuadFast acc q.1.lowerTags q.2) {}).toDataset

/-! ## The check -/

/-- BLANK_NODE_LABEL: a start character, then label characters, not ending
on `.`. -/
def bnodeLabelSafe (b : String) : Bool :=
  match b.toList with
  | [] => false
  | c :: rest => isBnodeStartChar c && rest.all isBnodeChar && b.toList.getLast? != some '.'

def subjectSafe : Subject → Bool
  | .iri i => iriPrintSafe i.val
  | .bnode b => bnodeLabelSafe b

/-- A lexical-form character that the canonical form writes raw or as one of
the two-character ECHAR escapes. -/
def lexCharSafe (c : Char) : Bool :=
  match canonEscapeChar c with
  | none => true
  | some _ => c == Char.ofNat 0x08 || c == '\t' || c == '\n' || c == Char.ofNat 0x0C ||
              c == '\r' || c == '"' || c == '\\'

/-- No two adjacent hyphens. -/
def noDoubleHyphen : List Char → Bool
  | c1 :: c2 :: rest => !(c1 == '-' && c2 == '-') && noDoubleHyphen (c2 :: rest)
  | _ => true

/-- LANGTAG, after lower-casing, with subtags of 1 to 8 characters. -/
def langTagSafe (tag : String) : Bool :=
  let cs := tag.toList.map Char.toLower
  match cs with
  | [] => false
  | c :: _ =>
      isLangStart c && cs.all isLangChar && noDoubleHyphen cs &&
        cs.getLast? != some '-' && validLangSubtags cs 0

def literalSafe (mode : Mode) (l : Literal) : Bool :=
  l.lexicalForm.toList.all lexCharSafe &&
  match l.langTag with
  | some tag => langTagSafe tag && (mode == .rdf12 || l.direction.isNone)
  | none => decide (l.datatype = xsdString) || iriPrintSafe l.datatype.val

def termSafe (mode : Mode) : Term → Bool
  | .iri i => iriPrintSafe i.val
  | .bnode b => bnodeLabelSafe b
  | .literal l => literalSafe mode l.val
  | .tripleTerm s p o =>
      mode == .rdf12 && subjectSafe s && iriPrintSafe p.val && termSafe mode o

def tripleSafe (mode : Mode) (t : Triple) : Bool :=
  subjectSafe t.s && iriPrintSafe t.p.val && termSafe mode t.o

def quadSafe (mode : Mode) (q : Triple × Option Subject) : Bool :=
  tripleSafe mode q.1 && q.2.all subjectSafe

/-- Every quad of the dataset passes the check. -/
def roundTripSafe (mode : Mode) (ds : Dataset) : Bool :=
  ds.quadList.all (quadSafe mode)

/-! ## Character-list lemmas -/

theorem span_loop_prefix (p : Char → Bool) : ∀ (xs : List Char) (c : Char) (rest acc : List Char),
    xs.all p = true → p c = false →
    List.span.loop p (xs ++ c :: rest) acc = (acc.reverse ++ xs, c :: rest)
  | [], c, rest, acc, _, hc => by simp [List.span.loop, hc]
  | x :: xs, c, rest, acc, hx, hc => by
      simp only [List.all_cons, Bool.and_eq_true] at hx
      simp only [List.cons_append, List.span.loop, hx.1]
      rw [span_loop_prefix p xs c rest (x :: acc) hx.2 hc]
      simp

theorem span_prefix (p : Char → Bool) (xs : List Char) (c : Char) (rest : List Char)
    (hx : xs.all p = true) (hc : p c = false) :
    List.span p (xs ++ c :: rest) = (xs, c :: rest) := by
  simp [List.span, span_loop_prefix p xs c rest [] hx hc]

theorem skipWs_nonWs' (pos : Nat) {c : Char} {rest : List Char}
    (h : isNtWs c = false) : skipWs pos (c :: rest) = (pos, c :: rest) := by
  simp [skipWs, List.span, List.span.loop, h]

theorem skipWs_space (pos : Nat) {c : Char} {rest : List Char}
    (h : isNtWs c = false) : skipWs pos (' ' :: c :: rest) = (pos + 1, c :: rest) := by
  simp only [isNtWs, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  simp [skipWs, List.span, List.span.loop, isNtWs, h.1, h.2]

/-! ## Blank-node labels -/

theorem readBlankNodeLabel_safe (pos : Nat) (b : String) (rest : List Char)
    (hb : bnodeLabelSafe b = true) :
    ∃ p', readBlankNodeLabel pos ('_' :: ':' :: (b.toList ++ ' ' :: rest))
      = .ok (b, p', ' ' :: rest) := by
  unfold bnodeLabelSafe at hb
  cases hcs : b.toList with
  | nil => rw [hcs] at hb; simp at hb
  | cons c0 body =>
      rw [hcs] at hb
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
      obtain ⟨⟨hstart, hbody⟩, hlast⟩ := hb
      have hsp : List.span isBnodeChar (body ++ ' ' :: rest) = (body, ' ' :: rest) :=
        span_prefix isBnodeChar body ' ' rest hbody (by decide)
      have hb' : String.ofList (c0 :: body) = b := by rw [← hcs, String.ofList_toList]
      refine ⟨pos + 2 + (c0 :: body).length, ?_⟩
      simp only [List.cons_append, readBlankNodeLabel, hstart, Bool.not_true, hsp]
      simp only [Bool.false_eq_true, if_false]
      rw [hb']

/-! ## String literals -/

/-- The characters the canonical form writes for one lexical-form character. -/
def escOf (c : Char) : String :=
  match canonEscapeChar c with
  | some e => e
  | none => String.singleton c

theorem canonEscapeLiteral_toList (s : String) :
    (canonEscapeLiteral s).toList = s.toList.flatMap (fun c => (escOf c).toList) := by
  simp only [canonEscapeLiteral, String.toList_join, List.flatMap_map]
  rfl

/-- One safe character is read back by one step of the literal body. -/
theorem strLitNextStep_esc (pos : Nat) (c : Char) (r : List Char) (h : lexCharSafe c = true) :
    ∃ w, strLitNextStep pos ((escOf c).toList ++ r) = .emit c w r := by
  unfold lexCharSafe at h
  cases he : canonEscapeChar c with
  | none =>
      simp only [escOf, he, String.toList_singleton, List.singleton_append]
      have h1 : c ≠ '"' := by intro hc; subst hc; simp [canonEscapeChar] at he
      have h2 : c ≠ '\\' := by intro hc; subst hc; simp [canonEscapeChar] at he
      have h3 : c ≠ '\n' := by intro hc; subst hc; simp [canonEscapeChar] at he
      have h4 : c ≠ '\r' := by intro hc; subst hc; simp [canonEscapeChar] at he
      refine ⟨1, ?_⟩
      unfold strLitNextStep
      split <;> simp_all
  | some e =>
      rw [he] at h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((((((h | h) | h) | h) | h) | h) | h) <;> subst h <;> exact ⟨2, rfl⟩

theorem readStringLiteralBody_safe : ∀ (cs : List Char) (pos : Nat) (tail : List Char),
    cs.all lexCharSafe = true →
    ∃ p', readStringLiteralBody pos (cs.flatMap (fun c => (escOf c).toList) ++ '"' :: tail)
      = .ok (String.ofList cs, p', tail)
  | [], pos, tail, _ => ⟨pos + 1, by simp⟩
  | c :: cs, pos, tail, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨w, hw⟩ := strLitNextStep_esc pos c
        (cs.flatMap (fun c => (escOf c).toList) ++ '"' :: tail) h.1
      obtain ⟨p', hp⟩ := readStringLiteralBody_safe cs (pos + w) tail h.2
      refine ⟨p', ?_⟩
      rw [List.flatMap_cons, List.append_assoc, readStringLiteralBody_emit _ _ _ _ _ hw, hp]
      simp only [Except.map]
      congr 2
      apply String.ext
      simp [Char.toString]

/-! ## Language tags -/

theorem splitOnDoubleHyphen_none : ∀ (cs acc : List Char), noDoubleHyphen cs = true →
    splitOnDoubleHyphen cs acc = (acc.reverse ++ cs, none)
  | [], acc, _ => by simp [splitOnDoubleHyphen]
  | [c], acc, _ => by simp [splitOnDoubleHyphen]
  | c1 :: c2 :: rest, acc, h => by
      simp only [noDoubleHyphen, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq] at h
      have ih := splitOnDoubleHyphen_none (c2 :: rest) (c1 :: acc) h.2
      have hc : ¬ (c1 = '-' ∧ c2 = '-') := by
        rintro ⟨h1, h2⟩; rcases h.1 with h' | h' <;> contradiction
      simp only [splitOnDoubleHyphen]
      rw [if_neg (by simpa using hc), ih]
      simp

theorem splitOnDoubleHyphen_dir : ∀ (cs acc d : List Char), noDoubleHyphen cs = true →
    cs.getLast? ≠ some '-' →
    splitOnDoubleHyphen (cs ++ '-' :: '-' :: d) acc = (acc.reverse ++ cs, some d)
  | [], acc, d, _, _ => by simp [splitOnDoubleHyphen]
  | [c], acc, d, _, hl => by
      have hc : c ≠ '-' := fun h => hl (by simp [h])
      simp [splitOnDoubleHyphen, hc]
  | c1 :: c2 :: rest, acc, d, h, hl => by
      simp only [noDoubleHyphen, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq] at h
      have hl' : (c2 :: rest).getLast? ≠ some '-' := by
        intro h'; apply hl; rw [List.getLast?_cons_cons]; exact h'
      have ih := splitOnDoubleHyphen_dir (c2 :: rest) (c1 :: acc) d h.2 hl'
      have hc : ¬ (c1 = '-' ∧ c2 = '-') := by
        rintro ⟨h1, h2⟩; rcases h.1 with h' | h' <;> contradiction
      simp only [List.cons_append, splitOnDoubleHyphen]
      rw [if_neg (by simpa using hc)]
      rw [List.cons_append] at ih
      rw [ih]
      simp

/-- The lower-cased tag the canonical form writes. -/
def lowerTagChars (tag : String) : List Char := tag.toList.map Char.toLower

theorem ofList_lowerTagChars (tag : String) : String.ofList (lowerTagChars tag) = tag.toLower := by
  unfold lowerTagChars
  rw [← String.toList_map, String.ofList_toList]
  rfl

theorem langTagSafe_parts {tag : String} (h : langTagSafe tag = true) :
    ∃ c cs, lowerTagChars tag = c :: cs ∧ isLangStart c = true ∧
      (c :: cs).all isLangChar = true ∧ noDoubleHyphen (c :: cs) = true ∧
      (c :: cs).getLast? ≠ some '-' ∧ validLangSubtags (c :: cs) 0 = true := by
  unfold langTagSafe at h
  unfold lowerTagChars
  revert h
  cases (tag.toList.map Char.toLower) with
  | nil => simp
  | cons c cs =>
      intro h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ⟨c, cs, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- RDF 1.1 LANGTAG reader on a safe tag followed by a space. -/
theorem readLangTag_safe (pos : Nat) (tag : String) (rest : List Char)
    (h : langTagSafe tag = true) :
    ∃ p', readLangTag pos ('@' :: (lowerTagChars tag ++ ' ' :: rest))
      = .ok (tag.toLower, p', ' ' :: rest) := by
  obtain ⟨c, cs, hlt, hstart, hall, -, -, -⟩ := langTagSafe_parts h
  have hsp := span_prefix isLangChar (c :: cs) ' ' rest hall (by decide)
  rw [← ofList_lowerTagChars, hlt]
  apply Exists.intro
  rw [List.cons_append]
  simp only [readLangTag, hstart, Bool.not_true, Bool.false_eq_true, if_false, readLangTagRun]
  rw [← List.cons_append, hsp]

/-- RDF 1.2 LANGTAG reader, no direction. -/
theorem readLangDir12_safe_none (pos : Nat) (tag : String) (rest : List Char)
    (h : langTagSafe tag = true) :
    ∃ p', readLangDir12 pos ('@' :: (lowerTagChars tag ++ ' ' :: rest))
      = .ok ((tag.toLower, none), p', ' ' :: rest) := by
  obtain ⟨c, cs, hlt, hstart, hall, hnd, -, hvalid⟩ := langTagSafe_parts h
  have hsp := span_prefix isLangChar (c :: cs) ' ' rest hall (by decide)
  have hsplit := splitOnDoubleHyphen_none (c :: cs) [] hnd
  rw [← ofList_lowerTagChars, hlt]
  apply Exists.intro
  rw [List.cons_append]
  simp only [readLangDir12, hstart, Bool.not_true, Bool.false_eq_true, if_false, readLangTagRun]
  rw [← List.cons_append]
  simp only [hsp]
  simp only [String.toList_ofList, hsplit, List.reverse_nil, List.nil_append, hvalid,
    Bool.not_true, Bool.false_eq_true, if_false]
  rfl

/-- The direction word after `--`. -/
def dirWord : TextDirection → List Char
  | .ltr => ['l', 't', 'r']
  | .rtl => ['r', 't', 'l']

/-- The Boolean `readLangDir12` returns for a direction. -/
def dirFlag : TextDirection → Bool
  | .ltr => false
  | .rtl => true

/-- RDF 1.2 LANGTAG reader with a base direction. -/
theorem readLangDir12_safe_dir (pos : Nat) (tag : String) (d : TextDirection) (rest : List Char)
    (h : langTagSafe tag = true) :
    ∃ p', readLangDir12 pos ('@' :: (lowerTagChars tag ++ ('-' :: '-' :: dirWord d ++ ' ' :: rest)))
      = .ok ((tag.toLower, some (dirFlag d)), p', ' ' :: rest) := by
  obtain ⟨c, cs, hlt, hstart, hall, hnd, hlast, hvalid⟩ := langTagSafe_parts h
  rw [← ofList_lowerTagChars, hlt]
  refine ⟨pos + 1 + (cs.length + 5 + 1), ?_⟩
  have hsp := span_prefix isLangChar ((c :: cs) ++ ('-' :: '-' :: dirWord d)) ' ' rest
    (by cases d <;> (simp only [List.all_append, hall, dirWord]; decide)) (by decide)
  have hsplit := splitOnDoubleHyphen_dir (c :: cs) [] (dirWord d) hnd hlast
  simp only [List.cons_append, List.append_assoc] at hsp hsplit ⊢
  simp only [readLangDir12, hstart, Bool.not_true, Bool.false_eq_true, if_false, readLangTagRun,
    hsp, String.toList_ofList, hsplit, List.reverse_nil, List.nil_append]
  cases d <;> simp [hvalid, dirWord, dirFlag]

/-! ## Literals -/

/-- The canonical form of a lexical form, as characters. -/
def escChars (s : String) : List Char := s.toList.flatMap (fun c => (escOf c).toList)

/-- What the canonical form writes after the closing quote of a literal. -/
def litSuffix (l : Literal) : List Char :=
  match l.langTag with
  | some tag => '@' :: (lowerTagChars tag ++
      (match l.direction with
       | some d => '-' :: '-' :: dirWord d
       | none => []))
  | none => if l.datatype = xsdString then [] else '^' :: '^' :: '<' :: (l.datatype.val.toList ++ ['>'])

theorem litChars_eq (wl : WfLiteral) :
    (Term.toCanonicalNTriples (.literal wl)).toList
      = '"' :: (escChars wl.val.lexicalForm ++ '"' :: litSuffix wl.val) := by
  rcases wl with ⟨⟨lex, dt, tag, dir⟩, hwf⟩
  simp only [Term.toCanonicalNTriples, litSuffix, escChars, ← canonEscapeLiteral_toList]
  cases tag with
  | some t =>
      cases dir with
      | none => simp [lowerTagChars, String.toList_map]
      | some d => cases d <;> simp [lowerTagChars, String.toList_map, dirWord]
  | none =>
      by_cases hdt : dt = xsdString
      · simp [hdt]
      · simp [hdt]

/-- The characters that follow an object in a canonical line: a graph label,
the terminating `.`, or the `)>>` of a triple term. -/
def objFollow (c : Char) : Bool := c == '<' || c == '_' || c == '.' || c == ')'

theorem objFollow_facts {c : Char} (h : objFollow c = true) :
    isNtWs c = false ∧ c ≠ '@' ∧ c ≠ '^' := by
  simp only [objFollow, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> subst h <;> decide

theorem mkLiteral_ok (pos : Nat) (l : Literal) (h : literalWf l = true) :
    mkLiteral pos l = .ok ⟨l, h⟩ := by
  simp [mkLiteral, h]

theorem readLiteral_safe (mode : Mode) (pos : Nat) (wl : WfLiteral) (c : Char) (rest : List Char)
    (hc : objFollow c = true) (h : literalSafe mode wl.val = true) :
    ∃ p', readLiteral mode pos
        ('"' :: (escChars wl.val.lexicalForm ++ '"' :: (litSuffix wl.val ++ ' ' :: c :: rest)))
      = .ok (wl.lowerTag, p', ' ' :: c :: rest) := by
  obtain ⟨hcws, hcat, hccaret⟩ := objFollow_facts hc
  rcases wl with ⟨⟨lex, dt, tag, dir⟩, hwf⟩
  simp only [literalSafe, Bool.and_eq_true] at h
  obtain ⟨hlex, hrest⟩ := h
  obtain ⟨p1, hp1⟩ := readStringLiteralBody_safe lex.toList (pos + 1)
    (litSuffix ⟨lex, dt, tag, dir⟩ ++ ' ' :: c :: rest) hlex
  rw [String.ofList_toList] at hp1
  have hq : ∀ X, readStringLiteralQuoted pos ('"' :: X) = readStringLiteralBody (pos + 1) X :=
    fun _ => rfl
  simp only [escChars] at hp1 ⊢
  cases tag with
  | none =>
      cases dir with
      | some d => simp [literalWf] at hwf
      | none =>
          by_cases hdt : dt = xsdString
          · subst hdt
            have hwf' : literalWf ⟨lex, xsdString, none, none⟩ = true := hwf
            simp only [litSuffix, if_pos] at hp1 ⊢
            simp only [List.nil_append] at hp1 ⊢
            refine ⟨p1, ?_⟩
            cases mode with
            | rdf11 =>
                simp only [readLiteral, hq, hp1, mkLiteral_ok _ _ hwf']
                rfl
            | rdf12 =>
                simp only [objFollow, Bool.or_eq_true, beq_iff_eq] at hc
                rcases hc with ((h | h) | h) | h <;> subst h <;>
                  (simp only [readLiteral, hq, hp1, skipWs_space _ hcws,
                    mkLiteral_ok _ _ hwf']; rfl)
          · have hsafe : iriPrintSafe dt.val = true := by
              simp only [hdt, decide_false, Bool.false_or] at hrest; exact hrest
            have hwf' : literalWf ⟨lex, dt, none, none⟩ = true := hwf
            simp only [litSuffix, hdt, if_false] at hp1 ⊢
            simp only [List.cons_append, List.append_assoc, List.nil_append] at hp1 ⊢
            have hiri := readIriRef_printSafe (pos := p1 + 2) dt (' ' :: c :: rest) hsafe
            refine ⟨p1 + 2 + dt.val.length + 2, ?_⟩
            cases mode with
            | rdf11 =>
                simp only [readLiteral, hq, hp1, readDatatype, hiri, mkIri_val,
                  mkLiteral_ok _ _ hwf']
                rfl
            | rdf12 =>
                simp only [readLiteral, hq, hp1, readDatatypeWs12,
                  skipWs_nonWs' _ (show isNtWs '^' = false by decide),
                  skipWs_nonWs' _ (show isNtWs '<' = false by decide), hiri, mkIri_val,
                  mkLiteral_ok _ _ hwf']
                rfl
  | some t =>
      simp only at hrest
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrest
      obtain ⟨htag, hmode⟩ := hrest
      cases dir with
      | none =>
          have hdt : dt = rdfLangString := Subtype.ext (by simpa [literalWf] using hwf)
          subst hdt
          have hwf' : literalWf ⟨lex, rdfLangString, some t.toLower, none⟩ = true := rfl
          simp only [litSuffix, List.append_nil, List.cons_append] at hp1 ⊢
          cases mode with
          | rdf11 =>
              obtain ⟨p2, hp2⟩ := readLangTag_safe p1 t (c :: rest) htag
              refine ⟨p2, ?_⟩
              simp only [readLiteral, hq, hp1, hp2, mkLiteral_ok _ _ hwf']
              rfl
          | rdf12 =>
              obtain ⟨p2, hp2⟩ := readLangDir12_safe_none p1 t (c :: rest) htag
              refine ⟨p2, ?_⟩
              simp only [readLiteral, hq, hp1,
                skipWs_nonWs' _ (show isNtWs '@' = false by decide), hp2,
                Option.map_none, mkLiteral_ok _ _ hwf']
              rfl
      | some d =>
          have hdt : dt = rdfDirLangString := Subtype.ext (by simpa [literalWf] using hwf)
          subst hdt
          have hm : mode = .rdf12 := by
            rcases hmode with h | h
            · exact h
            · simp at h
          subst hm
          have hwf' : literalWf ⟨lex, rdfDirLangString, some t.toLower, some d⟩ = true := rfl
          simp only [litSuffix, List.cons_append, List.append_assoc] at hp1 ⊢
          obtain ⟨p2, hp2⟩ := readLangDir12_safe_dir p1 t d (c :: rest) htag
          simp only [List.cons_append] at hp2
          refine ⟨p2, ?_⟩
          have hdir : (some (dirFlag d)).map
              (fun b => if b then TextDirection.rtl else TextDirection.ltr) = some d := by
            cases d <;> rfl
          simp only [readLiteral, hq, hp1,
            skipWs_nonWs' _ (show isNtWs '@' = false by decide), hp2, hdir,
            mkLiteral_ok _ _ hwf']
          rfl

/-! ## Terms -/

/-- The characters of a subject (or a graph label) in canonical form. -/
def subjChars (s : Subject) : List Char := (Subject.toNTriples s).toList

/-- The characters of an object term in canonical form. -/
def termChars (t : Term) : List Char := (Term.toCanonicalNTriples t).toList

theorem subjChars_iri (i : WfIri) : subjChars (.iri i) = '<' :: (i.val.toList ++ ['>']) := by
  simp [subjChars, Subject.toNTriples]

theorem subjChars_bnode (b : String) : subjChars (.bnode b) = '_' :: ':' :: b.toList := by
  simp [subjChars, Subject.toNTriples]

theorem termChars_iri (i : WfIri) : termChars (.iri i) = '<' :: (i.val.toList ++ ['>']) := by
  simp [termChars, Term.toCanonicalNTriples]

theorem termChars_bnode (b : String) : termChars (.bnode b) = '_' :: ':' :: b.toList := by
  simp [termChars, Term.toCanonicalNTriples]

theorem termChars_triple (s : Subject) (p : WfIri) (o : Term) :
    termChars (.tripleTerm s p o) =
      '<' :: '<' :: '(' :: ' ' :: (subjChars s ++ ' ' :: '<' :: (p.val.toList ++ '>' :: ' ' ::
        (termChars o ++ [' ', ')', '>', '>']))) := by
  simp [termChars, subjChars, Term.toCanonicalNTriples]

theorem readSubject_safe (pos : Nat) (s : Subject) (rest : List Char) (h : subjectSafe s = true) :
    ∃ p', readSubject pos (subjChars s ++ ' ' :: rest) = .ok (s, p', ' ' :: rest) := by
  cases s with
  | iri i =>
      rw [subjChars_iri, List.cons_append, List.append_assoc, List.singleton_append]
      exact ⟨_, readSubject_printSafe pos i (' ' :: rest) h⟩
  | bnode b =>
      rw [subjChars_bnode]
      obtain ⟨p', hp⟩ := readBlankNodeLabel_safe pos b rest h
      refine ⟨p', ?_⟩
      simp only [List.cons_append, readSubject]
      rw [hp]

theorem readGraphLabel_safe (pos : Nat) (s : Subject) (rest : List Char) (h : subjectSafe s = true) :
    ∃ p', readGraphLabel pos (subjChars s ++ ' ' :: rest) = .ok (s, p', ' ' :: rest) := by
  cases s with
  | iri i =>
      rw [subjChars_iri, List.cons_append, List.append_assoc, List.singleton_append]
      refine ⟨pos + i.val.length + 2, ?_⟩
      simp only [readGraphLabel, readIriRef_printSafe pos i (' ' :: rest) h, mkIri_val]
  | bnode b =>
      rw [subjChars_bnode]
      obtain ⟨p', hp⟩ := readBlankNodeLabel_safe pos b rest h
      refine ⟨p', ?_⟩
      simp only [List.cons_append, readGraphLabel]
      rw [hp]

theorem readPredicate_safe (pos : Nat) (i : WfIri) (rest : List Char) (h : iriPrintSafe i.val = true) :
    ∃ p', readPredicate pos ('<' :: (i.val.toList ++ '>' :: ' ' :: rest)) = .ok (i, p', ' ' :: rest) :=
  ⟨_, readPredicate_printSafe pos i (' ' :: rest) h⟩

theorem iri_head_ne_lt (i : WfIri) (h : iriPrintSafe i.val = true) :
    ∃ x xs, i.val.toList = x :: xs ∧ x ≠ '<' := by
  have hne : i.val.toList ≠ [] := by
    intro h0
    have := i.property
    simp [isIri, h0] at this
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨x, xs, hx, ?_⟩
  intro hxl
  unfold iriPrintSafe at h
  rw [hx] at h
  simp only [List.all_cons, Bool.and_eq_true] at h
  have := h.1
  subst hxl
  simp [IriSafeChar, isIriForbiddenCodepoint] at this

theorem readObject11_safe (pos : Nat) (t : Term) (c : Char) (rest : List Char)
    (hc : objFollow c = true) (h : termSafe .rdf11 t = true) :
    ∃ p', readObject11 pos (termChars t ++ ' ' :: c :: rest) = .ok (t.lowerTags, p', ' ' :: c :: rest) := by
  cases t with
  | iri i =>
      rw [termChars_iri, List.cons_append, List.append_assoc, List.singleton_append]
      exact ⟨_, readObject11_printSafe pos i (' ' :: c :: rest) h⟩
  | bnode b =>
      rw [termChars_bnode]
      obtain ⟨p', hp⟩ := readBlankNodeLabel_safe pos b (c :: rest) h
      refine ⟨p', ?_⟩
      simp only [List.cons_append, readObject11, Term.lowerTags]
      rw [hp]
  | literal wl =>
      obtain ⟨p', hp⟩ := readLiteral_safe .rdf11 pos wl c rest hc h
      refine ⟨p', ?_⟩
      simp only [termChars, litChars_eq, List.cons_append, List.append_assoc, readObject11,
        Term.lowerTags] at hp ⊢
      rw [hp]
  | tripleTerm s p o => simp [termSafe] at h

theorem subjChars_head (s : Subject) : ∃ x xs, subjChars s = x :: xs ∧ isNtWs x = false := by
  cases s with
  | iri i => exact ⟨_, _, subjChars_iri i, by decide⟩
  | bnode b => exact ⟨_, _, subjChars_bnode b, by decide⟩

theorem termChars_head (t : Term) : ∃ x xs, termChars t = x :: xs ∧ isNtWs x = false := by
  cases t with
  | iri i => exact ⟨_, _, termChars_iri i, by decide⟩
  | bnode b => exact ⟨_, _, termChars_bnode b, by decide⟩
  | literal wl => exact ⟨_, _, litChars_eq wl, by decide⟩
  | tripleTerm s p o => exact ⟨_, _, termChars_triple s p o, by decide⟩

/-- Nesting depth of triple terms. -/
def Term.ttDepth : Term → Nat
  | .tripleTerm _ _ o => o.ttDepth + 1
  | _ => 0

theorem readObject12_safe : ∀ (t : Term) (f pos : Nat) (c : Char) (rest : List Char),
    t.ttDepth < f → objFollow c = true → termSafe .rdf12 t = true →
    ∃ p', readObject12 f pos (termChars t ++ ' ' :: c :: rest)
      = .ok (t.lowerTags, p', ' ' :: c :: rest)
  | .iri i, f + 1, pos, c, rest, _, _, h => by
      obtain ⟨x, xs, hx, hxl⟩ := iri_head_ne_lt i h
      have hr := readIriRef_printSafe pos i (' ' :: c :: rest) h
      rw [termChars_iri, List.cons_append, List.append_assoc, List.singleton_append]
      refine ⟨pos + i.val.length + 2, ?_⟩
      rw [hx] at hr ⊢
      simp only [List.cons_append] at hr ⊢
      unfold readObject12
      split
      · rename_i h1; simp at h1; exact absurd h1.1 hxl
      · rename_i h1; simp at h1; exact absurd h1.1 hxl
      · rename_i h1; simp only [List.cons.injEq] at h1; obtain ⟨-, h1⟩ := h1; subst h1
        simp only [hr, mkIri_val, Term.lowerTags]
      · rename_i h1; simp at h1
      · rename_i h1; simp at h1
      · rename_i h1 h2 h3 h4 h5; exact absurd rfl (h3 _)
  | .bnode b, f + 1, pos, c, rest, _, _, h => by
      rw [termChars_bnode]
      obtain ⟨p', hp⟩ := readBlankNodeLabel_safe pos b (c :: rest) h
      refine ⟨p', ?_⟩
      simp only [List.cons_append, readObject12, Term.lowerTags]
      rw [hp]
  | .literal wl, f + 1, pos, c, rest, _, hc, h => by
      obtain ⟨p', hp⟩ := readLiteral_safe .rdf12 pos wl c rest hc h
      refine ⟨p', ?_⟩
      simp only [termChars, litChars_eq, List.cons_append, List.append_assoc, readObject12,
        Term.lowerTags] at hp ⊢
      rw [hp]
  | .tripleTerm s p o, f + 1, pos, c, rest, hf, hc, h => by
      simp only [termSafe, Bool.and_eq_true, beq_self_eq_true, true_and] at h
      obtain ⟨⟨hs, hp⟩, ho⟩ := h
      have hf' : o.ttDepth < f := by simp [Term.ttDepth] at hf; omega
      obtain ⟨p2, hp2⟩ := readSubject_safe (pos + 3 + 1) s
        ('<' :: (p.val.toList ++ '>' :: ' ' :: (termChars o ++ ' ' :: ')' :: '>' :: '>' :: ' ' :: c :: rest))) hs
      obtain ⟨p4, hp4⟩ := readPredicate_safe (p2 + 1) p
        (termChars o ++ ' ' :: ')' :: '>' :: '>' :: ' ' :: c :: rest) hp
      obtain ⟨p6, hp6⟩ := readObject12_safe o f (p4 + 1) ')' ('>' :: '>' :: ' ' :: c :: rest) hf'
        (by decide) ho
      obtain ⟨sx, sxs, hsx, hsxw⟩ := subjChars_head s
      obtain ⟨ox, oxs, hox, hoxw⟩ := termChars_head o
      refine ⟨p6 + 1 + 3, ?_⟩
      rw [termChars_triple]
      rw [hsx] at hp2 ⊢
      rw [hox] at hp2 hp4 hp6 ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hp2 hp4 hp6 ⊢
      simp only [readObject12, skipWs_space _ hsxw, hp2,
        skipWs_space _ (show isNtWs '<' = false by decide), hp4, skipWs_space _ hoxw, hp6,
        skipWs_space _ (show isNtWs ')' = false by decide), Term.lowerTags]

end L4Factoidal.RDF
