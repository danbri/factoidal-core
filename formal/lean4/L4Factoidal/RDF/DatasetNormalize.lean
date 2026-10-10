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

end L4Factoidal.RDF
