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
  U+FFFF). The proof reads back the seven two-character ECHAR escapes; a
  dataset with a `\u`-escaped character takes the text path below;
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

/-- `iriPrintSafe` without building the character list: `String.all` walks
the UTF-8 bytes. The check runs over every IRI of the dataset, and through
`String.toList` it cost as much as parsing the Turtle input (callgrind,
`query` COUNT(*), 1,250 paragraphs of `gene.ttl`: `iriPrintSafe` 36.2 percent
of the instructions, the Turtle parse 37.3). -/
def iriPrintSafeFast (s : String) : Bool := s.all IriSafeChar

/-- The compiler calls `iriPrintSafeFast` wherever the source says
`iriPrintSafe`. -/
@[csimp] theorem iriPrintSafe_eq_iriPrintSafeFast : @iriPrintSafe = @iriPrintSafeFast := by
  funext s
  simp [iriPrintSafe, iriPrintSafeFast, String.all_bool_eq]

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
  l.lexicalForm.all lexCharSafe &&
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
  simp only [literalSafe, Bool.and_eq_true, String.all_bool_eq] at h
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

/-! ## No line break inside a term, and the RDF 1.2 object fuel -/

/-- No character of the list is a line feed. -/
def noNl (cs : List Char) : Bool := cs.all (fun c => c != '\n')

theorem noNl_iri (i : WfIri) (h : iriPrintSafe i.val = true) : noNl i.val.toList = true := by
  unfold noNl
  unfold iriPrintSafe at h
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  simp only [IriSafeChar, Bool.and_eq_true, decide_eq_true_eq] at this
  have h1 := this.1.1
  simp only [bne_iff_ne, ne_eq]
  intro hn; subst hn; simp at h1

theorem noNl_bnode (b : String) (h : bnodeLabelSafe b = true) : noNl b.toList = true := by
  unfold bnodeLabelSafe at h
  unfold noNl
  cases hb : b.toList with
  | nil => rfl
  | cons c0 body =>
      rw [hb] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨h0, hbody⟩, -⟩ := h
      simp only [List.all_cons, Bool.and_eq_true]
      constructor
      · simp only [bne_iff_ne, ne_eq]; intro hn; subst hn; simp [isBnodeStartChar] at h0
      · rw [List.all_eq_true] at hbody ⊢
        intro c hc
        have := hbody c hc
        simp only [bne_iff_ne, ne_eq]; intro hn; subst hn; simp [isBnodeChar] at this

theorem noNl_subj (s : Subject) (h : subjectSafe s = true) : noNl (subjChars s) = true := by
  cases s with
  | iri i =>
      have := noNl_iri i h
      simp only [noNl] at this ⊢
      simp [subjChars_iri, this]
  | bnode b =>
      have := noNl_bnode b h
      simp only [noNl] at this ⊢
      simp [subjChars_bnode, this]

theorem noNl_escOf (c : Char) (h : lexCharSafe c = true) : noNl (escOf c).toList = true := by
  unfold lexCharSafe at h
  cases he : canonEscapeChar c with
  | none =>
      simp only [noNl, escOf, he, String.toList_singleton, List.all_cons, List.all_nil,
        Bool.and_true, bne_iff_ne, ne_eq]
      intro hn; subst hn; simp [canonEscapeChar] at he
  | some e =>
      rw [he] at h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((((((h | h) | h) | h) | h) | h) | h) <;> subst h <;> rfl

theorem noNl_lit (wl : WfLiteral) (h : literalSafe .rdf12 wl.val = true) :
    noNl (termChars (.literal wl)) = true := by
  rcases wl with ⟨⟨lex, dt, tag, dir⟩, hwf⟩
  simp only [literalSafe, Bool.and_eq_true, String.all_bool_eq] at h
  obtain ⟨hlex, hrest⟩ := h
  have hesc : noNl (escChars lex) = true := by
    unfold escChars noNl
    rw [List.all_flatMap, List.all_eq_true]
    intro c hc
    rw [List.all_eq_true] at hlex
    exact noNl_escOf c (hlex c hc)
  simp only [noNl] at hesc
  simp only [termChars, litChars_eq, noNl, List.all_cons, List.all_append, hesc]
  cases tag with
  | some t =>
      simp only at hrest
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨c, cs, hlt, -, hall, -, -, -⟩ := langTagSafe_parts hrest.1
      have hlt' : (lowerTagChars t).all (fun c => c != '\n') = true := by
        rw [hlt, List.all_eq_true]
        rw [List.all_eq_true] at hall
        intro x hx
        have := hall x hx
        simp only [bne_iff_ne, ne_eq]; intro hn; subst hn; simp [isLangChar] at this
      cases dir with
      | none => simp [litSuffix, hlt']
      | some d => cases d <;> simp [litSuffix, hlt', dirWord]
  | none =>
      by_cases hdt : dt = xsdString
      · simp [litSuffix, hdt]
      · have hsafe : iriPrintSafe dt.val = true := by
          simp only [hdt, decide_false, Bool.false_or] at hrest; exact hrest
        have := noNl_iri dt hsafe
        simp only [noNl] at this
        simp [litSuffix, hdt, this]

theorem noNl_term : ∀ (t : Term), termSafe .rdf12 t = true → noNl (termChars t) = true
  | .iri i, h => by
      have := noNl_iri i h
      simp only [noNl] at this ⊢
      simp [termChars_iri, this]
  | .bnode b, h => by
      have := noNl_bnode b h
      simp only [noNl] at this ⊢
      simp [termChars_bnode, this]
  | .literal wl, h => noNl_lit wl h
  | .tripleTerm s p o, h => by
      simp only [termSafe, Bool.and_eq_true, beq_self_eq_true, true_and] at h
      obtain ⟨⟨hs, hp⟩, ho⟩ := h
      have h1 := noNl_subj s hs
      have h2 := noNl_iri p hp
      have h3 := noNl_term o ho
      simp only [noNl] at h1 h2 h3 ⊢
      simp [termChars_triple, h1, h2, h3]

theorem lineFuelGo_ge : ∀ (cs : List Char) (acc : Nat), acc ≤ lineFuelGo cs acc
  | [], acc => by simp [lineFuelGo]
  | c :: rest, acc => by
      unfold lineFuelGo
      split
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ acc) (lineFuelGo_ge rest (acc + 1))

theorem lineFuelGo_append : ∀ (xs ys : List Char) (acc : Nat), noNl xs = true →
    lineFuelGo (xs ++ ys) acc = lineFuelGo ys (acc + xs.length)
  | [], ys, acc, _ => by simp
  | x :: xs, ys, acc, h => by
      simp only [noNl, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have hx : (x == '\n') = false := by simp [h.1]
      simp only [List.cons_append, lineFuelGo, hx, Bool.false_eq_true, if_false]
      rw [lineFuelGo_append xs ys (acc + 1) h.2]
      simp only [List.length_cons]
      congr 1
      omega

theorem ttDepth_le_length : ∀ (t : Term), t.ttDepth ≤ (termChars t).length
  | .iri _ => Nat.zero_le _
  | .bnode _ => Nat.zero_le _
  | .literal _ => Nat.zero_le _
  | .tripleTerm s p o => by
      have := ttDepth_le_length o
      rw [termChars_triple]
      simp only [Term.ttDepth, List.length_cons, List.length_append]
      omega

theorem ttDepth_lt_lineFuel (t : Term) (ys : List Char) (h : termSafe .rdf12 t = true) :
    t.ttDepth < lineFuel (termChars t ++ ys) := by
  unfold lineFuel
  rw [lineFuelGo_append _ _ _ (noNl_term t h)]
  have h1 := lineFuelGo_ge ys (1 + (termChars t).length)
  have h2 := ttDepth_le_length t
  omega

/-! ## One line -/

/-- The characters of one quad's canonical line. -/
def quadLine (q : Triple × Option Subject) : List Char :=
  match q.2 with
  | none => (Triple.toCanonicalNTriples q.1).toList
  | some g => (canonNamedLine g q.1).toList

theorem quadLine_none (t : Triple) :
    quadLine (t, none) = subjChars t.s ++ ' ' :: '<' :: (t.p.val.toList ++ '>' :: ' ' ::
      (termChars t.o ++ [' ', '.', '\n'])) := by
  simp [quadLine, Triple.toCanonicalNTriples, subjChars, termChars]

theorem quadLine_some (t : Triple) (g : Subject) :
    quadLine (t, some g) = subjChars t.s ++ ' ' :: '<' :: (t.p.val.toList ++ '>' :: ' ' ::
      (termChars t.o ++ ' ' :: (subjChars g ++ [' ', '.', '\n']))) := by
  simp [quadLine, canonNamedLine, subjChars, termChars]

theorem subjChars_head' (s : Subject) :
    ∃ x xs, subjChars s = x :: xs ∧ objFollow x = true ∧ isNtWs x = false := by
  cases s with
  | iri i => exact ⟨_, _, subjChars_iri i, by decide, by decide⟩
  | bnode b => exact ⟨_, _, subjChars_bnode b, by decide, by decide⟩

theorem readOptGraphLabel_some (pos : Nat) (g : Subject) (rest : List Char)
    (h : subjectSafe g = true) :
    ∃ p', readOptGraphLabel pos (' ' :: (subjChars g ++ ' ' :: rest)) = .ok (some g, p', ' ' :: rest) := by
  obtain ⟨p', hp⟩ := readGraphLabel_safe (pos + 1) g rest h
  refine ⟨p', ?_⟩
  cases g with
  | iri i =>
      rw [subjChars_iri] at hp ⊢
      simp only [List.cons_append, List.append_assoc] at hp ⊢
      simp only [readOptGraphLabel, skipWs_space _ (show isNtWs '<' = false by decide), hp]
  | bnode b =>
      rw [subjChars_bnode] at hp ⊢
      simp only [List.cons_append] at hp ⊢
      simp only [readOptGraphLabel, skipWs_space _ (show isNtWs '_' = false by decide), hp]

theorem readNQuad12_line (pos : Nat) (q : Triple × Option Subject) (rest : List Char)
    (hq : quadSafe .rdf12 q = true) :
    ∃ p', readNQuad12 pos (quadLine q ++ rest) = .ok (q.1.lowerTags, q.2, p', '\n' :: rest) := by
  obtain ⟨⟨s, p, o⟩, g⟩ := q
  simp only [quadSafe, tripleSafe, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨hs, hp⟩, ho⟩, hg⟩ := hq
  obtain ⟨sx, sxs, hsx, hsxw⟩ := subjChars_head s
  obtain ⟨ox, oxs, hox, hoxw⟩ := termChars_head o
  cases g with
  | none =>
      obtain ⟨p2, hp2⟩ := readSubject_safe pos s
        ('<' :: (p.val.toList ++ '>' :: ' ' :: (termChars o ++ ' ' :: '.' :: '\n' :: rest))) hs
      obtain ⟨p4, hp4⟩ := readPredicate_safe (p2 + 1) p (termChars o ++ ' ' :: '.' :: '\n' :: rest) hp
      have hfuel := ttDepth_lt_lineFuel o (' ' :: '.' :: '\n' :: rest) ho
      obtain ⟨p6, hp6⟩ := readObject12_safe o (lineFuel (termChars o ++ ' ' :: '.' :: '\n' :: rest))
        (p4 + 1) '.' ('\n' :: rest) hfuel (by decide) ho
      refine ⟨p6 + 1 + 1, ?_⟩
      rw [quadLine_none]
      rw [hsx] at hp2 ⊢
      rw [hox] at hp2 hp4 hp6 ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hp2 hp4 hp6 ⊢
      simp only [readNQuad12, skipWs_nonWs' _ hsxw, hp2,
        skipWs_space _ (show isNtWs '<' = false by decide), hp4, skipWs_space _ hoxw, hp6,
        skipWs_space _ (show isNtWs '.' = false by decide), readOptGraphLabel,
        skipWs_nonWs' _ (show isNtWs '.' = false by decide)]
      rfl
  | some gr =>
      simp only [Option.all_some] at hg
      obtain ⟨gx, gxs, hgx, hgxf, hgxw⟩ := subjChars_head' gr
      obtain ⟨p2, hp2⟩ := readSubject_safe pos s
        ('<' :: (p.val.toList ++ '>' :: ' ' :: (termChars o ++ ' ' ::
          (subjChars gr ++ ' ' :: '.' :: '\n' :: rest)))) hs
      obtain ⟨p4, hp4⟩ := readPredicate_safe (p2 + 1) p
        (termChars o ++ ' ' :: (subjChars gr ++ ' ' :: '.' :: '\n' :: rest)) hp
      have hfuel := ttDepth_lt_lineFuel o (' ' :: (subjChars gr ++ ' ' :: '.' :: '\n' :: rest)) ho
      rw [hgx] at hfuel
      obtain ⟨p6, hp6⟩ := readObject12_safe o
        (lineFuel (termChars o ++ ' ' :: (gx :: gxs ++ ' ' :: '.' :: '\n' :: rest)))
        (p4 + 1) gx (gxs ++ ' ' :: '.' :: '\n' :: rest) hfuel hgxf ho
      obtain ⟨p7, hp7⟩ := readOptGraphLabel_some p6 gr ('.' :: '\n' :: rest) hg
      refine ⟨p7 + 1 + 1, ?_⟩
      rw [quadLine_some]
      rw [hsx] at hp2 ⊢
      rw [hgx] at hp2 hp4 hp7 ⊢
      rw [hox] at hp2 hp4 hp6 ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hp2 hp4 hp6 hp7 ⊢
      simp only [readNQuad12, skipWs_nonWs' _ hsxw, hp2,
        skipWs_space _ (show isNtWs '<' = false by decide), hp4, skipWs_space _ hoxw, hp6, hp7,
        skipWs_space _ (show isNtWs '.' = false by decide)]
      rfl

theorem readNQuad11_line (pos : Nat) (q : Triple × Option Subject) (rest : List Char)
    (hq : quadSafe .rdf11 q = true) :
    ∃ p', readNQuad11 pos (quadLine q ++ rest) = .ok (q.1.lowerTags, q.2, p', '\n' :: rest) := by
  obtain ⟨⟨s, p, o⟩, g⟩ := q
  simp only [quadSafe, tripleSafe, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨hs, hp⟩, ho⟩, hg⟩ := hq
  obtain ⟨sx, sxs, hsx, hsxw⟩ := subjChars_head s
  obtain ⟨ox, oxs, hox, hoxw⟩ := termChars_head o
  cases g with
  | none =>
      obtain ⟨p2, hp2⟩ := readSubject_safe pos s
        ('<' :: (p.val.toList ++ '>' :: ' ' :: (termChars o ++ ' ' :: '.' :: '\n' :: rest))) hs
      obtain ⟨p4, hp4⟩ := readPredicate_safe (p2 + 1) p (termChars o ++ ' ' :: '.' :: '\n' :: rest) hp
      obtain ⟨p6, hp6⟩ := readObject11_safe (p4 + 1) o '.' ('\n' :: rest) (by decide) ho
      refine ⟨p6 + 1 + 1, ?_⟩
      rw [quadLine_none]
      rw [hsx] at hp2 ⊢
      rw [hox] at hp2 hp4 hp6 ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hp2 hp4 hp6 ⊢
      simp only [readNQuad11, skipWs_nonWs' _ hsxw, hp2,
        skipWs_space _ (show isNtWs '<' = false by decide), hp4, skipWs_space _ hoxw, hp6,
        skipWs_space _ (show isNtWs '.' = false by decide), readOptGraphLabel,
        skipWs_nonWs' _ (show isNtWs '.' = false by decide)]
      rfl
  | some gr =>
      simp only [Option.all_some] at hg
      obtain ⟨gx, gxs, hgx, hgxf, hgxw⟩ := subjChars_head' gr
      obtain ⟨p2, hp2⟩ := readSubject_safe pos s
        ('<' :: (p.val.toList ++ '>' :: ' ' :: (termChars o ++ ' ' ::
          (subjChars gr ++ ' ' :: '.' :: '\n' :: rest)))) hs
      obtain ⟨p4, hp4⟩ := readPredicate_safe (p2 + 1) p
        (termChars o ++ ' ' :: (subjChars gr ++ ' ' :: '.' :: '\n' :: rest)) hp
      obtain ⟨p6, hp6⟩ := readObject11_safe (p4 + 1) o gx (gxs ++ ' ' :: '.' :: '\n' :: rest) hgxf ho
      obtain ⟨p7, hp7⟩ := readOptGraphLabel_some p6 gr ('.' :: '\n' :: rest) hg
      refine ⟨p7 + 1 + 1, ?_⟩
      rw [quadLine_some]
      rw [hsx] at hp2 ⊢
      rw [hgx] at hp2 hp4 hp7 ⊢
      rw [hox] at hp2 hp4 hp6 ⊢
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hp2 hp4 hp6 hp7 ⊢
      simp only [readNQuad11, skipWs_nonWs' _ hsxw, hp2,
        skipWs_space _ (show isNtWs '<' = false by decide), hp4, skipWs_space _ hoxw, hp6, hp7,
        skipWs_space _ (show isNtWs '.' = false by decide)]
      rfl

/-! ## The document -/

theorem quadLine_head (q : Triple × Option Subject) :
    ∃ x xs, quadLine q = x :: xs ∧ (x = '<' ∨ x = '_') := by
  obtain ⟨⟨s, p, o⟩, g⟩ := q
  have hs : ∃ x xs, subjChars s = x :: xs ∧ (x = '<' ∨ x = '_') := by
    cases s with
    | iri i => exact ⟨_, _, subjChars_iri i, Or.inl rfl⟩
    | bnode b => exact ⟨_, _, subjChars_bnode b, Or.inr rfl⟩
  obtain ⟨x, xs, hx, hxx⟩ := hs
  cases g with
  | none => exact ⟨x, _, by rw [quadLine_none, hx, List.cons_append], hxx⟩
  | some gr => exact ⟨x, _, by rw [quadLine_some, hx, List.cons_append], hxx⟩

/-- One statement step of the fold, at a line that starts with a character
that is neither whitespace nor a comment nor a line break. -/
theorem foldQuadLinesAcc_stmt {α : Type} (consume : α → Triple → Option Subject → α)
    (mode : Mode) (f pos : Nat) (x : Char) (xs : List Char) (acc : α)
    (t : Triple) (g : Option Subject) (p' : Nat) (rest : List Char)
    (hx1 : isNtWs x = false) (hx2 : x ≠ '#') (hx3 : x ≠ '\n') (hx4 : x ≠ '\r')
    (hstep : (match mode with
      | .rdf11 => readNQuad11 pos (x :: xs)
      | .rdf12 => readNQuad12 pos (x :: xs)) = .ok (t, g, p', '\n' :: rest)) :
    foldQuadLinesAcc mode consume (f + 1) pos (x :: xs) acc
      = foldQuadLinesAcc mode consume f (p' + 1) rest (consume acc t g) := by
  cases mode with
  | rdf11 =>
      simp only at hstep
      simp only [foldQuadLinesAcc, skipWs_nonWs' _ hx1]
      split
      next h => simp at h
      next h => exact absurd (List.cons.inj h).1 hx2
      next h => exact absurd (List.cons.inj h).1 hx3
      next h => exact absurd (List.cons.inj h).1 hx4
      next =>
        simp only [hstep, skipWs_nonWs' _ (show isNtWs '\n' = false by decide)]
        rfl
  | rdf12 =>
      simp only at hstep
      simp only [foldQuadLinesAcc, skipWs_nonWs' _ hx1]
      split
      next h => simp at h
      next h => exact absurd (List.cons.inj h).1 hx2
      next h => exact absurd (List.cons.inj h).1 hx3
      next h => exact absurd (List.cons.inj h).1 hx4
      next =>
        simp only [hstep, skipWs_nonWs' _ (show isNtWs '\n' = false by decide)]
        rfl

/-- One line of the fold: the canonical line of a safe quad hands the
normalised quad to the consumer and the fold goes on with the next line. -/
theorem foldQuadLinesAcc_line (mode : Mode) {α : Type} (consume : α → Triple → Option Subject → α)
    (f pos : Nat) (q : Triple × Option Subject) (rest : List Char) (acc : α)
    (hq : quadSafe mode q = true) :
    ∃ p', foldQuadLinesAcc mode consume (f + 1) pos (quadLine q ++ rest) acc
      = foldQuadLinesAcc mode consume f p' rest (consume acc q.1.lowerTags q.2) := by
  have hstep : ∃ p', (match mode with
      | .rdf11 => readNQuad11 pos (quadLine q ++ rest)
      | .rdf12 => readNQuad12 pos (quadLine q ++ rest))
        = .ok (q.1.lowerTags, q.2, p', '\n' :: rest) := by
    cases mode
    · exact readNQuad11_line pos q rest hq
    · exact readNQuad12_line pos q rest hq
  obtain ⟨p', hp'⟩ := hstep
  obtain ⟨x, xs, hx, hxx⟩ := quadLine_head q
  rw [hx, List.cons_append] at hp'
  rw [hx, List.cons_append]
  refine ⟨p' + 1, ?_⟩
  rcases hxx with rfl | rfl
  · exact foldQuadLinesAcc_stmt consume mode f pos _ _ acc _ _ p' rest
      (by decide) (by decide) (by decide) (by decide) hp'
  · exact foldQuadLinesAcc_stmt consume mode f pos _ _ acc _ _ p' rest
      (by decide) (by decide) (by decide) (by decide) hp'

theorem foldQuadLinesAcc_doc (mode : Mode) {α : Type} (consume : α → Triple → Option Subject → α) :
    ∀ (qs : List (Triple × Option Subject)) (f pos : Nat) (acc : α),
      qs.length ≤ f → qs.all (quadSafe mode) = true →
      foldQuadLinesAcc mode consume (f + 1) pos (qs.flatMap quadLine) acc
        = .ok (qs.foldl (fun a q => consume a q.1.lowerTags q.2) acc)
  | [], f, pos, acc, _, _ => by
      simp [foldQuadLinesAcc, skipWs, List.span, List.span.loop]
  | _ :: _, 0, _, _, hlen, _ => by simp at hlen
  | q :: qs, f + 1, pos, acc, hlen, hall => by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨p', hp'⟩ := foldQuadLinesAcc_line mode consume (f + 1) pos q (qs.flatMap quadLine) acc hall.1
      rw [List.flatMap_cons, hp']
      exact foldQuadLinesAcc_doc mode consume qs f p' _ (by simp at hlen; omega) hall.2

theorem length_le_flatMap_quadLine : ∀ (qs : List (Triple × Option Subject)),
    qs.length ≤ (qs.flatMap quadLine).length
  | [] => by simp
  | q :: qs => by
      obtain ⟨x, xs, hx, -⟩ := quadLine_head q
      have := length_le_flatMap_quadLine qs
      simp only [List.flatMap_cons, hx, List.length_append, List.length_cons]
      omega

theorem toCanonicalNQuads_toList (ds : Dataset) :
    (Dataset.toCanonicalNQuads ds).toList = ds.quadList.flatMap quadLine := by
  simp [Dataset.toCanonicalNQuads, Graph.toCanonicalNTriples, Dataset.quadList, quadLine,
    String.toList_join, List.flatMap_append, List.flatMap_map, List.flatMap_assoc]

/-! ## The theorem -/

/-- **The canonical N-Quads round trip is `normalizeDataset`**, for every
dataset whose terms pass `roundTripSafe`. -/
theorem parseNQuadsFast_toCanonicalNQuads (ds : Dataset) (mode : Mode)
    (h : roundTripSafe mode ds = true) :
    parseNQuadsFast (Dataset.toCanonicalNQuads ds) mode = .ok (normalizeDataset ds) := by
  unfold parseNQuadsFast normalizeDataset
  simp only [toCanonicalNQuads_toList]
  rw [foldQuadLinesAcc_doc mode addQuadFast ds.quadList _ 0 {}
    (length_le_flatMap_quadLine _) h]
  rfl

/-- What the command line hands to `query`, `update`, `canonicalize` and
`closure`: the normalised dataset when the check passes, the text round trip
otherwise. -/
def datasetForOps (mode : Mode) (ds : Dataset) : Except ParseError Dataset :=
  if roundTripSafe mode ds then .ok (normalizeDataset ds)
  else parseNQuadsFast (Dataset.toCanonicalNQuads ds) mode

/-- `datasetForOps` IS the text round trip, for every dataset. -/
theorem datasetForOps_eq (mode : Mode) (ds : Dataset) :
    datasetForOps mode ds = parseNQuadsFast (Dataset.toCanonicalNQuads ds) mode := by
  unfold datasetForOps
  split
  · rename_i h; rw [parseNQuadsFast_toCanonicalNQuads ds mode h]
  · rfl

end L4Factoidal.RDF
