/-
L4Factoidal.Syntax.NTriples — the N-Triples parser and serialiser.

Port of `formal/fstar/Parser.NTriples.fst`'s triple-level grammar
(`parse_subject` / `parse_object` / `parse_triple` / `parse_ntriples_strict`
/ `parse_ntriples_strict_12`) and of the N-Triples half of
`formal/fstar/RDF.NQuads.Serialize.fst` (`nq_term_to_string` /
`nq_subject_to_string` / `nq_line_for_triple_default_graph`), built on the
character-level readers in `Syntax.Lexing`.

Grammar productions ported (RDF 1.1 N-Triples, https://www.w3.org/TR/n-triples/):
  [1] ntriplesDoc  [2] triple  [3] subject  [4] predicate  [5] object
  [6] literal
plus the RDF 1.2 object-position extension (W3C Working Draft, epic #305):
  triple term `<<( subject predicate object )>>`.

This port ships only the F* source's STRICT entry points
(`parse_ntriples_strict` / `_strict_12`): the WHOLE document either parses
or the whole call reports one `ParseError`. The F* source's LENIENT
`parse_ntriples`/`parse_ntriples_acc` (skip a malformed line, keep going)
and its streaming/count/validate-only variants
(`fold_ntriples`, `count_ntriples`, `validate_*`) are CLI/performance
pragmatics over the same grammar, not additional semantics, and are
deliberately not ported — matching the spec/pragmatics split already
established for the rest of `L4Factoidal` (see `PORT_NOTES.md`).

Also not ported: the RDF 1.2 c14n suite's `extra_whitespace-*` relaxation
(inline whitespace between a closing quote and a following `@lang`/
`^^datatype`) — see the note in `Syntax.Lexing`'s module header.
-/

import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## RDF 1.1 / RDF 1.2 processing mode

Port of the F* source's `rdf_syntax_mode` (`Mode_11` / `Mode_12`), threaded
as an explicit parameter — never a global — through every syntax parser
and serialiser exactly as the F* source's module banner requires. -/

/-- Which grammar to parse/serialise against.
* `.rdf11` — RDF 1.1: rejects the 1.2 lexical forms (`<<( )>>` triple
  terms, `@lang--dir` directional literals) exactly as the 1.1 grammar
  does. This is the default everywhere (the F* source's `Mode_11`).
* `.rdf12` — RDF 1.2: additionally accepts object-position triple terms
  and directional language strings; still rejects the retired RDF-star
  `<< s p o >>` quoted-triple form in both modes. -/
inductive Mode where
  | rdf11
  | rdf12
  deriving DecidableEq, Repr

/-! ## Term/literal construction with well-formedness checks

`readIriRef`/`readStringLiteralQuoted` (`Syntax.Lexing`) hand back plain
`String`s; wrapping them into `RDF.WfIri`/`RDF.WfLiteral` needs the
well-formedness predicates from `RDF.Core`, which is why this lives here
and not in `Syntax.Lexing`. -/

/-- `RDF.isIri` without the character list: `String.contains` reads the
string in place, where `isIri` builds `s.toList` to look for one `:`.
Callgrind, the streamed `l4factoidal parse` of 20,000 N-Triples lines
(2026-10-13): `isIri` was 27 percent of the instructions, nearly all of it
`String.toList` (https://github.com/danbri/factoidal/issues/813). -/
def isIriFast (s : String) : Bool := !s.isEmpty && s.contains ':'

/-- The compiler calls `isIriFast` wherever the source says `isIri`, in this
module and in every module that imports it (all the RDF parsers). -/
@[csimp] theorem isIri_eq_isIriFast : @isIri = @isIriFast := by
  funext s
  simp [isIri, isIriFast, String.contains]

-- Both answers on the edge cases, so a fast form that answered `true` (or
-- `false`) everywhere would not build.
#guard isIriFast "http://e/a" && isIri "http://e/a"
#guard !isIriFast "" && !isIri ""
#guard !isIriFast "relative/path" && !isIri "relative/path"
#guard isIriFast "é:x" && isIri "é:x"

/-- Wrap a raw IRI string as a `WfIri`, or report the failure at `pos`.
Port of `parse_iri`'s `is_iri i` check. -/
def mkIri (pos : Nat) (s : String) : Except ParseError WfIri :=
  if h : isIri s then .ok ⟨s, h⟩
  else .error ⟨s!"invalid IRI (not absolute — missing ':'): <{s}>", pos⟩

/-- Wrap a `Literal` record as a `WfLiteral`, or report the failure at
`pos`. Port of every `parse_literal*` branch's `if literal_wf lit then
... else ParseFail "invalid literal" pos`. The language tag is written in
its canonical (lower-case) form first (`Literal.toWf?`; RDF 1.2 Concepts
§3.4, https://github.com/danbri/factoidal/issues/1001). Every literal of
the N-Triples, N-Quads, Turtle and TriG readers is made here. -/
def mkLiteral (pos : Nat) (l : Literal) : Except ParseError WfLiteral :=
  match Literal.toWf? l with
  | some w => .ok w
  | none => .error ⟨"ill-formed literal (language tag / direction / datatype combination)", pos⟩

/-- A literal that is already well-formed is kept as it is. -/
theorem mkLiteral_of_wf (pos : Nat) (l : Literal) (h : literalWf l = true) :
    mkLiteral pos l = .ok ⟨l, h⟩ := by
  simp [mkLiteral, Literal.toWf?_of_wf h]

/-! ## Literal — [6] literal

`literal ::= STRING_LITERAL_QUOTED ('^^' IRIREF | LANGTAG)?` -/

/-- `'^^' IRIREF` — port of `parse_datatype`. -/
def readDatatype (pos : Nat) : List Char → Except ParseError (WfIri × Nat × List Char)
  | '^' :: '^' :: rest =>
      match readIriRef (pos + 2) rest with
      | .error e => .error e
      | .ok (iriStr, pos', rest') =>
          match mkIri pos iriStr with
          | .error e => .error e
          | .ok wi => .ok (wi, pos', rest')
  | _ => .error ⟨"expected '^^'", pos⟩

/-- `'^^' ws* IRIREF` — the RDF 1.2 form, which admits inline
whitespace between `^^` and the datatype IRI. Port of
`parse_datatype_ws_12`. -/
def readDatatypeWs12 (pos : Nat) : List Char → Except ParseError (WfIri × Nat × List Char)
  | '^' :: '^' :: rest =>
      let (pos2, rest2) := skipWs (pos + 2) rest
      match readIriRef pos2 rest2 with
      | .error e => .error e
      | .ok (iriStr, pos', rest') =>
          match mkIri pos iriStr with
          | .error e => .error e
          | .ok wi => .ok (wi, pos', rest')
  | _ => .error ⟨"expected '^^'", pos⟩

/-- A literal (mode-parametrised): the string body, then optionally a
LANGTAG (with RDF 1.2's `--ltr`/`--rtl` suffix under `.rdf12`) or a
`^^`-datatype. Port of `parse_literal` (`.rdf11`) / `parse_literal_12`
(`.rdf12`).

RDF 1.2 N-Triples and N-Quads admit inline whitespace (space or tab)
between the closing quote and a following `@lang` / `^^datatype`, and
between `^^` and the datatype IRI — the W3C c14n entries
`extra_whitespace-03` (`"Alice" @en`) and `extra_whitespace-04`
(`"2"  ^^  <…integer>`). RDF 1.1 stays byte-strict. The run is consumed
ONLY when a `@` or `^^` really follows; for a plain `xsd:string` the
position BEFORE the run is returned, so the trailing whitespace stays
with the triple parser that skips it before the `.` terminator. -/
def readLiteral (mode : Mode) (pos : Nat) (cs : List Char) :
    Except ParseError (WfLiteral × Nat × List Char) :=
  match readStringLiteralQuoted pos cs with
  | .error e => .error e
  | .ok (lex, pos1, rest1raw) =>
      -- Under `.rdf12`, look PAST a run of space/tab for the `@`/`^^`.
      let (pos1ws, rest1ws) := match mode with
        | .rdf11 => (pos1, rest1raw)
        | .rdf12 => skipWs pos1 rest1raw
      let (pos1, rest1) := match rest1ws with
        | '@' :: _       => (pos1ws, rest1ws)
        | '^' :: '^' :: _ => (pos1ws, rest1ws)
        | _              => (pos1, rest1raw)
      match rest1 with
      | '@' :: _ =>
          match mode with
          | .rdf11 =>
              match readLangTag pos1 rest1 with
              | .error e => .error e
              | .ok (tag, pos2, rest2) =>
                  match mkLiteral pos1
                      { lexicalForm := lex, datatype := rdfLangString,
                        langTag := some tag, direction := none } with
                  | .error e => .error e
                  | .ok wl => .ok (wl, pos2, rest2)
          | .rdf12 =>
              match readLangDir12 pos1 rest1 with
              | .error e => .error e
              | .ok ((tag, dopt), pos2, rest2) =>
                  let dt := match dopt with
                    | none => rdfLangString
                    | some _ => rdfDirLangString
                  let dir := dopt.map (fun b => if b then TextDirection.rtl else TextDirection.ltr)
                  match mkLiteral pos1
                      { lexicalForm := lex, datatype := dt,
                        langTag := some tag, direction := dir } with
                  | .error e => .error e
                  | .ok wl => .ok (wl, pos2, rest2)
      | '^' :: '^' :: _ =>
          match (match mode with
                 | .rdf11 => readDatatype pos1 rest1
                 | .rdf12 => readDatatypeWs12 pos1 rest1) with
          | .error e => .error e
          | .ok (dt, pos2, rest2) =>
              match mkLiteral pos1
                  { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
              | .error e => .error e
              | .ok wl => .ok (wl, pos2, rest2)
      | _ =>
          match mkLiteral pos1
              { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none } with
          | .error e => .error e
          | .ok wl => .ok (wl, pos1, rest1)

/-! ## Subject — [3] subject

`subject ::= IRIREF | BLANK_NODE_LABEL` (same production for the RDF 1.2
triple-term subject slot — RDF 1.2 does not allow a triple term AS a
subject). Port of `parse_subject`. -/

def readSubject (pos : Nat) (cs : List Char) : Except ParseError (Subject × Nat × List Char) :=
  match cs with
  | '<' :: _ =>
      match readIriRef pos cs with
      | .error e => .error e
      | .ok (s, pos', rest') =>
          match mkIri pos s with
          | .error e => .error e
          | .ok wi => .ok (.iri wi, pos', rest')
  | '_' :: ':' :: _ =>
      match readBlankNodeLabel pos cs with
      | .error e => .error e
      | .ok (label, pos', rest') => .ok (.bnode label, pos', rest')
  | _ => .error ⟨"expected subject (IRIREF or BLANK_NODE_LABEL)", pos⟩

/-! ## Predicate — [4] predicate: `predicate ::= IRIREF` -/

def readPredicate (pos : Nat) (cs : List Char) : Except ParseError (WfIri × Nat × List Char) :=
  match readIriRef pos cs with
  | .error e => .error e
  | .ok (s, pos', rest') =>
      match mkIri pos s with
      | .error e => .error e
      | .ok wi => .ok (wi, pos', rest')

/-! ## Object — [5] object (RDF 1.1)

`object ::= IRIREF | BLANK_NODE_LABEL | literal`. Port of `parse_object`. -/

def readObject11 (pos : Nat) (cs : List Char) : Except ParseError (Term × Nat × List Char) :=
  match cs with
  | '<' :: _ =>
      match readIriRef pos cs with
      | .error e => .error e
      | .ok (s, pos', rest') =>
          match mkIri pos s with
          | .error e => .error e
          | .ok wi => .ok (.iri wi, pos', rest')
  | '_' :: ':' :: _ =>
      match readBlankNodeLabel pos cs with
      | .error e => .error e
      | .ok (label, pos', rest') => .ok (.bnode label, pos', rest')
  | '"' :: _ =>
      match readLiteral .rdf11 pos cs with
      | .error e => .error e
      | .ok (wl, pos', rest') => .ok (.literal wl, pos', rest')
  | _ => .error ⟨"expected object (IRIREF, BLANK_NODE_LABEL, or literal)", pos⟩

/-! ## Object — RDF 1.2 extension: `object12 ::= object | tripleTerm`

`tripleTerm ::= '<<(' subject IRIREF object12 ')>>'`. Port of
`parse_object_12_f` / `parse_triple_term_12_f` — the F* source's mutual
recursion collapses into one function with the triple-term case inlined,
since only the OBJECT slot of a triple term recurses (never the subject
or predicate). `fuel` bounds triple-term NESTING depth (one unit per
`<<(` opened) — the one place this port keeps the F* source's fuel style,
because unlike every reader in `Syntax.Lexing` the recursive call here is
not on a direct cons-pattern suffix of the char list (it is reached after
parsing a subject/predicate in between), so plain structural recursion on
the list is not available; structural recursion on `fuel : Nat` is. -/
def readObject12 : Nat → Nat → List Char → Except ParseError (Term × Nat × List Char)
  | 0, pos, _ => .error ⟨"triple-term nesting too deep", pos⟩
  | fuel' + 1, pos, cs =>
      match cs with
      | '<' :: '<' :: '(' :: rest =>
          let (p1, r1) := skipWs (pos + 3) rest
          match readSubject p1 r1 with
          | .error e => .error e
          | .ok (subj, p2, r2) =>
              let (p3, r3) := skipWs p2 r2
              match readPredicate p3 r3 with
              | .error e => .error e
              | .ok (pred, p4, r4) =>
                  let (p5, r5) := skipWs p4 r4
                  match readObject12 fuel' p5 r5 with
                  | .error e => .error e
                  | .ok (obj, p6, r6) =>
                      let (p7, r7) := skipWs p6 r6
                      match r7 with
                      | ')' :: '>' :: '>' :: r8 =>
                          .ok (.tripleTerm subj pred obj, p7 + 3, r8)
                      | _ => .error ⟨"expected ')>>'", p7⟩
      | '<' :: '<' :: _ =>
          .error ⟨"legacy '<< >>' quoted triple is not RDF 1.2 syntax", pos⟩
      | '<' :: _ =>
          (match readIriRef pos cs with
           | .error e => .error e
           | .ok (s, pos', rest') =>
               match mkIri pos s with
               | .error e => .error e
               | .ok wi => .ok (.iri wi, pos', rest'))
      | '_' :: ':' :: _ =>
          (match readBlankNodeLabel pos cs with
           | .error e => .error e
           | .ok (label, pos', rest') => .ok (.bnode label, pos', rest'))
      | '"' :: _ =>
          (match readLiteral .rdf12 pos cs with
           | .error e => .error e
           | .ok (wl, pos', rest') => .ok (.literal wl, pos', rest'))
      | _ =>
          .error ⟨"expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term)", pos⟩

/-! ### Triple terms nested deep: the loop

The definition of `readObject12` above is the SPECIFICATION. It takes one native frame
for each level of nesting, so a triple term nested more than a few thousand levels deep
overflowed the stack (4,510 levels ran under a 512 KB stack and 4,511 overflowed; the
wasm module overflowed its call stack at 300,000 levels). The parser runs the loop that
follows, `readObject12Down`, which keeps the open triple terms in a list.
`readObject12_eq_loop` proves it equal to the specification for every fuel, and
`@[csimp]` makes every caller defined after it run the loop
(https://github.com/danbri/factoidal/issues/867). -/

/-- The result of reading an object. -/
abbrev Object12Result := Except ParseError (Term × Nat × List Char)

/-- The triple terms that are open while the loop reads the object of the innermost one:
the subject and the predicate of each, innermost first. A triple term nested n deep has n
entries here and no native frame. -/
abbrev OpenTerms12 := List (Subject × WfIri)

/-- What the specification does with the result of an object: the innermost open triple
term takes it as its object, skips the white space, reads its closing `)>>` and is itself
the result of the object of the next one out, and so on. An error ends them all, and the
result of the last one is the result. Every call of this function on itself is a tail
call. -/
def closeObject12 : OpenTerms12 → Object12Result → Object12Result
  | _, .error e => .error e
  | [], .ok r => .ok r
  | (subj, pred) :: opens, .ok (obj, p6, r6) =>
      let (p7, r7) := skipWs p6 r6
      match r7 with
      | ')' :: '>' :: '>' :: r8 => closeObject12 opens (.ok (.tripleTerm subj pred obj, p7 + 3, r8))
      | _ => .error ⟨"expected ')>>'", p7⟩

/-- `readObject12` with the open triple terms in a list. A triple term reads its subject and
its predicate, takes one unit of fuel as the specification does, and goes on to its object
by a tail call; an object that is not a triple term is read by the specification, which does
not recurse on it, and `closeObject12` closes the open triple terms. -/
def readObject12Down : Nat → OpenTerms12 → Nat → List Char → Object12Result
  | 0, _, pos, _ => .error ⟨"triple-term nesting too deep", pos⟩
  | fuel' + 1, opens, pos, cs =>
      match cs with
      | '<' :: '<' :: '(' :: rest =>
          let (p1, r1) := skipWs (pos + 3) rest
          match readSubject p1 r1 with
          | .error e => .error e
          | .ok (subj, p2, r2) =>
              let (p3, r3) := skipWs p2 r2
              match readPredicate p3 r3 with
              | .error e => .error e
              | .ok (pred, p4, r4) =>
                  let (p5, r5) := skipWs p4 r4
                  readObject12Down fuel' ((subj, pred) :: opens) p5 r5
      | _ => closeObject12 opens (readObject12 (fuel' + 1) pos cs)

theorem closeObject12_error (opens : OpenTerms12) (e : ParseError) :
    closeObject12 opens (.error e) = .error e := by
  cases opens <;> rfl

theorem closeObject12_nil (r : Object12Result) : closeObject12 [] r = r := by
  cases r <;> rfl

/-- The innermost open triple term closes first, and the others close what it returns. -/
theorem closeObject12_cons (fr : Subject × WfIri) (opens : OpenTerms12) (r : Object12Result) :
    closeObject12 (fr :: opens) r = closeObject12 opens (closeObject12 [fr] r) := by
  rcases fr with ⟨subj, pred⟩
  cases r with
  | error e => simp [closeObject12_error]
  | ok x =>
    rcases x with ⟨obj, p6, r6⟩
    simp only [closeObject12]
    generalize skipWs p6 r6 = w
    rcases w with ⟨p7, r7⟩
    dsimp only
    split <;> simp [closeObject12]

/-- The specification of one nesting level with fuel, its closing step written with
`closeObject12`. -/
theorem readObject12_open (f pos : Nat) (rest : List Char) :
    readObject12 (f + 1) pos ('<' :: '<' :: '(' :: rest) =
      (let (p1, r1) := skipWs (pos + 3) rest
       match readSubject p1 r1 with
       | .error e => .error e
       | .ok (subj, p2, r2) =>
           let (p3, r3) := skipWs p2 r2
           match readPredicate p3 r3 with
           | .error e => .error e
           | .ok (pred, p4, r4) =>
               let (p5, r5) := skipWs p4 r4
               closeObject12 [(subj, pred)] (readObject12 f p5 r5)) := by
  rw [readObject12]
  generalize skipWs (pos + 3) rest = w1
  rcases w1 with ⟨p1, r1⟩
  dsimp only
  cases readSubject p1 r1 with
  | error e => rfl
  | ok x =>
    rcases x with ⟨subj, p2, r2⟩
    dsimp only
    generalize skipWs p2 r2 = w3
    rcases w3 with ⟨p3, r3⟩
    dsimp only
    cases readPredicate p3 r3 with
    | error e => rfl
    | ok y =>
      rcases y with ⟨pred, p4, r4⟩
      dsimp only
      generalize skipWs p4 r4 = w5
      rcases w5 with ⟨p5, r5⟩
      dsimp only
      cases readObject12 f p5 r5 with
      | error e => rfl
      | ok z =>
        rcases z with ⟨obj, p6, r6⟩
        simp only [closeObject12]
        all_goals
          generalize skipWs p6 r6 = w
          rcases w with ⟨p7, r7⟩
          dsimp only
          split <;> simp

/-- The loop, from any list of open triple terms: the specification, and then the open
triple terms closed. By induction on the fuel; each step of the loop takes one unit of it. -/
theorem readObject12Down_eq :
    ∀ (fuel : Nat) (opens : OpenTerms12) (pos : Nat) (cs : List Char),
      readObject12Down fuel opens pos cs = closeObject12 opens (readObject12 fuel pos cs)
  | 0, opens, pos, cs => by
      rw [readObject12Down, readObject12, closeObject12_error]
  | f + 1, opens, pos, cs => by
      unfold readObject12Down
      split
      · rename_i rest
        rw [readObject12_open]
        generalize skipWs (pos + 3) rest = w1
        rcases w1 with ⟨p1, r1⟩
        dsimp only
        cases readSubject p1 r1 with
        | error e => rw [closeObject12_error]
        | ok x =>
          rcases x with ⟨subj, p2, r2⟩
          dsimp only
          generalize skipWs p2 r2 = w3
          rcases w3 with ⟨p3, r3⟩
          dsimp only
          cases readPredicate p3 r3 with
          | error e => rw [closeObject12_error]
          | ok y =>
            rcases y with ⟨pred, p4, r4⟩
            dsimp only
            generalize skipWs p4 r4 = w5
            rcases w5 with ⟨p5, r5⟩
            dsimp only
            rw [readObject12Down_eq f, closeObject12_cons]
      · rfl

/-- `readObject12` as the loop. -/
def readObject12Loop (fuel pos : Nat) (cs : List Char) : Object12Result :=
  readObject12Down fuel [] pos cs

/-- Any call of `readObject12` compiled after this line runs the loop: the readers of
N-Triples and N-Quads 1.2 lines below, and so every caller of them (the batch parsers, the
fast N-Quads reader behind the op `queryDataset`, the streaming readers of the packer). -/
@[csimp] theorem readObject12_eq_loop : @readObject12 = @readObject12Loop := by
  funext fuel pos cs
  rw [readObject12Loop, readObject12Down_eq, closeObject12_nil]

#print axioms readObject12Down_eq
#print axioms readObject12_eq_loop

/-! ### The RDF 1.2 object fuel

`readObject12` takes a fuel that bounds `<<( ... )>>` NESTING, and each level
consumes three characters, so any count of the characters the object can
occupy is a sufficient bound. Until 2026-09-05 the bound was `cs.length`,
which walks the WHOLE remaining input for every statement and is therefore
quadratic in what the caller hands over: in the streaming packer that is a
65,536-character chunk, and `/usr/bin/sample` put 10,159 of 15,405 samples of
a wire-version-10 pack of a 52,428,626-byte skosdex prefix inside that one
`List.length`. Version 10 reads its source as RDF 1.2, so it was the first
route to pay it.

`readTriple12` kept `r5.length + 1` until 2026-10-14: N-Triples in RDF 1.2 mode
was the same quadratic walk. A pack of `.nt` text through the source layer
(`l4sbm11-pack`, which reads RDF 1.2) took 3.0 s of phase 1 for 8.3 MB against
0.48 s for the same quads as N-Quads text (4 workers, 11,000 subjects of
`tests/sbm11/syntax/gen_multi.py`, 2026-10-14). The batch parser
(`parseNTriples`) walked the rest of the whole document for each statement.

An N-Triples or N-Quads statement never spans a raw line break — a literal
carries `\n` escaped, RDF 1.1 N-Triples and N-Quads section 4, and `skipWs` skips
space and tab only — so the characters up to the next line
break bound the object, and counting them is linear in the line rather than
in the document. The bound is only ever LARGER than the nesting depth it must
cover, so no document that parsed before is refused now and no committed byte
changes. -/
def lineFuelGo : List Char → Nat → Nat
  | [], acc => acc
  | c :: rest, acc => if c == '\n' then acc else lineFuelGo rest (acc + 1)

/-- One more than the number of characters before the next line break. -/
def lineFuel (cs : List Char) : Nat := lineFuelGo cs 1

/-! ## Triple — [2] triple: `triple ::= subject predicate object '.'` -/

/-- RDF 1.1 triple. Port of `parse_triple`. -/
def readTriple11 (pos : Nat) (cs : List Char) : Except ParseError (Triple × Nat × List Char) :=
  let (p1, r1) := skipWs pos cs
  match readSubject p1 r1 with
  | .error e => .error e
  | .ok (subj, p2, r2) =>
      let (p3, r3) := skipWs p2 r2
      match readPredicate p3 r3 with
      | .error e => .error e
      | .ok (pred, p4, r4) =>
          let (p5, r5) := skipWs p4 r4
          match readObject11 p5 r5 with
          | .error e => .error e
          | .ok (obj, p6, r6) =>
              let (p7, r7) := skipWs p6 r6
              match r7 with
              | '.' :: r8 => .ok ({ s := subj, p := pred, o := obj }, p7 + 1, r8)
              | _ => .error ⟨"expected '.' terminator", p7⟩

/-- RDF 1.2 triple: the subject and predicate slots are unchanged (RDF 1.2
does not add triple terms there); only the object slot may be a triple
term. Port of `parse_triple_12`. -/
def readTriple12 (pos : Nat) (cs : List Char) : Except ParseError (Triple × Nat × List Char) :=
  let (p1, r1) := skipWs pos cs
  match readSubject p1 r1 with
  | .error e => .error e
  | .ok (subj, p2, r2) =>
      let (p3, r3) := skipWs p2 r2
      match readPredicate p3 r3 with
      | .error e => .error e
      | .ok (pred, p4, r4) =>
          let (p5, r5) := skipWs p4 r4
          match readObject12 (lineFuel r5) p5 r5 with
          | .error e => .error e
          | .ok (obj, p6, r6) =>
              let (p7, r7) := skipWs p6 r6
              match r7 with
              | '.' :: r8 => .ok ({ s := subj, p := pred, o := obj }, p7 + 1, r8)
              | _ => .error ⟨"expected '.' terminator", p7⟩

/-! ## Document — [1] ntriplesDoc

`ntriplesDoc ::= triple? (EOL triple?)*`, plus `#`-comments and blank
lines (RDF 1.1 N-Triples §"Comments"). STRICT: any malformed line aborts
the whole parse with that line's `ParseError` — port of
`parse_ntriples_strict` / `parse_ntriples_strict_12`. `fuel` bounds the
number of lines processed; every branch below strictly shortens the
remaining char list by at least one element before recursing (a comment
or blank line consumes at least its introducing character, a triple
consumes at least its terminating `.`), so `fuel := cs.length + 1`
(the top-level call, mirroring the F* source's `len + 1`) never runs out
before the input does. -/
def parseLinesAcc (mode : Mode) :
    Nat → Nat → List Char → List Triple → Except ParseError (List Triple)
  | 0, pos, _, _ =>
      .error ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
  | fuel' + 1, pos, cs, acc =>
      let (pos1, cs1) := skipWs pos cs
      match cs1 with
      | [] => .ok acc.reverse
      | '#' :: _ =>
          let (pos2, cs2) := skipComment pos1 cs1
          let (pos3, cs3) := skipEol pos2 cs2
          parseLinesAcc mode fuel' pos3 cs3 acc
      | '\n' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          parseLinesAcc mode fuel' pos2 cs2 acc
      | '\r' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          parseLinesAcc mode fuel' pos2 cs2 acc
      | _ =>
          let step := match mode with
            | .rdf11 => readTriple11 pos1 cs1
            | .rdf12 => readTriple12 pos1 cs1
          match step with
          | .error e => .error e
          | .ok (t, pos2, cs2) =>
              let (pos3, cs3) := skipWs pos2 cs2
              let (pos4, cs4) := skipComment pos3 cs3
              let (pos5, cs5) := skipEol pos4 cs4
              parseLinesAcc mode fuel' pos5 cs5 (t :: acc)

/-- Parse a complete N-Triples document. Default mode is RDF 1.1 (`.rdf11`
— the F* source's `Mode_11` default: the RDF 1.2 concrete syntax is still
a W3C Working Draft, so 1.1 stays the normative default). Port of
`parse_ntriples_mode`, restricted to the strict entry points (see module
header). -/
def parseNTriples (s : String) (mode : Mode := .rdf11) : Except ParseError Graph :=
  let cs := s.toList
  parseLinesAcc mode (cs.length + 1) 0 cs []

/-! ## Serialisation

Port of `RDF.NQuads.Serialize.fst`'s N-Triples-shaped renderers
(`nq_term_to_string`, `nq_subject_to_string`,
`nq_line_for_triple_default_graph`) — the EMIT-MINIMAL wire form (escapes
control characters and `"`/`\`, appends `--ltr`/`--rtl` and `<<( )>>` only
for terms that actually need them, so a purely-RDF-1.1 graph serialises
identically regardless of `mode`). The F* source's separate CANONICAL
form (`nq_canon_term`, uppercase `\u00XX` for every C0/DEL byte,
lowercased language tags, U+FFFE/U+FFFF escaping) is a distinct rendering
contract or the RDFC-1.0 c14n suite, not the general wire serialiser this
module ports — ported below, in its own section. -/

/-- Escape a literal's lexical form for embedding in a quoted string:
`\` → `\\`, `"` → `\"`, LF → `\n`, CR → `\r`, TAB → `\t`; every other
character passes through unescaped. Port of `nq_escape_literal`. -/
def escapeLiteral (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c =>
    match c with
    | '\\' => ['\\', '\\']
    | '"'  => ['\\', '"']
    | '\n' => ['\\', 'n']
    | '\r' => ['\\', 'r']
    | '\t' => ['\\', 't']
    | _    => [c]))

/-- Serialise a `Subject` (IRI or blank node). Port of
`nq_subject_to_string`. -/
def Subject.toNTriples : Subject → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b

/-- `" )>>"` written `k` times: the end of `k` open triple terms. -/
def closersStr (k : Nat) : String := String.join (List.replicate k " )>>")

theorem closersStr_zero : closersStr 0 = "" := rfl

theorem closersStr_succ (k : Nat) : closersStr (k + 1) = " )>>" ++ closersStr k := by
  simp [closersStr, List.replicate_succ, String.join_cons]

/-- `acc` followed by the `k` closers, one tail call for each. -/
def appendClosers (acc : String) : Nat → String
  | 0 => acc
  | k + 1 => appendClosers (acc ++ " )>>") k

theorem appendClosers_eq : ∀ (k : Nat) (acc : String), appendClosers acc k = acc ++ closersStr k
  | 0, acc => by simp [appendClosers, closersStr_zero]
  | k + 1, acc => by
      rw [appendClosers, appendClosers_eq k, closersStr_succ, String.append_assoc]

/-- The text of a triple term up to its object, the same in the canonical form and in the
other. -/
def tripleTermOpen (s : Subject) (p : WfIri) : String :=
  "<<( " ++ Subject.toNTriples s ++ " <" ++ p.val ++ "> "

/-- LANGTAG, RDF 1.1 N-Triples production [144s], the characters after `@`:
`[a-zA-Z]+ ('-' [a-zA-Z0-9]+)*`. Each of `subtags` is one subtag: the first
letters only, the others letters and digits, none empty. -/
def langSubtagsGrammar : List String → Bool
  | [] => false
  | first :: rest =>
      !first.isEmpty && first.all isLangStart &&
        rest.all fun st => !st.isEmpty && st.all fun c => isLangChar c && c != '-'

/-- A language tag that the writer of `mode` can write and its reader reads
back: LANGTAG [144s], and in RDF 1.2 mode also every subtag 1 to 8 characters
(BCP 47 section 2.1, the check of the RDF 1.2 reader, `validLangSubtags`).
A tag outside it has no valid rewrite: the writer refuses it with
`langTagError` (https://github.com/danbri/factoidal/issues/986). -/
def langTagWritable (mode : Mode) (tag : String) : Bool :=
  langSubtagsGrammar (tag.splitOn "-") &&
    match mode with
    | .rdf11 => true
    | .rdf12 => validLangSubtags tag.toList 0

/-- The error of a writer for a language tag outside `langTagWritable`; it
names the tag. -/
def langTagError (tag : String) : String :=
  "the language tag \"" ++ tag ++ "\" is not a LANGTAG (RDF 1.1 N-Triples [144s]; RDF 1.2: subtags of 1 to 8 characters), so no writer can state it"

/-- Serialise a `Term` in N-Triples object position, mode-parametrised:
under `.rdf11` a term that needs RDF 1.2 lexical syntax (a triple term or
a directional literal) is a serialisation ERROR (port of the F* source's
`nq_term_to_string_mode`'s `Mode_11` branch returning `None`), never
silently emitted. Under `.rdf12` every term serialises (port of
`nq_term_to_string`, extended with the `<<( )>>` / `--ltr`/`--rtl` forms). -/
def Term.toNTriples (mode : Mode) : Term → Except String String
  | .iri i   => .ok ("<" ++ i.val ++ ">")
  | .bnode b => .ok ("_:" ++ b)
  | .literal wl =>
      let l := wl.val
      let esc := escapeLiteral l.lexicalForm
      match l.langTag with
      | some tag =>
          if !langTagWritable mode tag then .error (langTagError tag) else
          match l.direction with
          | some _ =>
              if mode = .rdf11 then
                .error "RDF 1.2 directional literal requires mode .rdf12"
              else
                let dirSuffix := match l.direction with
                  | some .ltr => "--ltr"
                  | some .rtl => "--rtl"
                  | none => ""
                .ok ("\"" ++ esc ++ "\"@" ++ tag ++ dirSuffix)
          | none => .ok ("\"" ++ esc ++ "\"@" ++ tag)
      | none =>
          if l.datatype = xsdString then .ok ("\"" ++ esc ++ "\"")
          else .ok ("\"" ++ esc ++ "\"^^<" ++ l.datatype.val ++ ">")
  | .tripleTerm s p o =>
      if mode = .rdf11 then .error "RDF 1.2 triple term requires mode .rdf12"
      else
        match Term.toNTriples mode o with
        | .error e => .error e
        | .ok oStr =>
            .ok ("<<( " ++ Subject.toNTriples s ++ " <" ++ p.val ++ "> " ++ oStr ++ " )>>")

/-- A success of the writer of a language-tagged literal is a success past the
check of its tag (`langTagWritable`). -/
theorem ite_error_eq_ok {c : Prop} [Decidable c] {e : String} {r : Except String String} {s : String}
    (h : (if c then Except.error e else r) = .ok s) : r = .ok s := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h
  · rwa [if_neg hc] at h

/-! ### The text of a triple term nested deep

`Term.toNTriples` above is the SPECIFICATION. It takes one native frame for each level
of triple-term nesting, and at each level it copies the text of the levels below
(`"<<( " ++ ... ++ below ++ " )>>"`), so its time is quadratic in the depth: a triple term
nested 300,000 deep took 86.6 s to write, and a stack of 512 KB held 10,151 levels and
overflowed at 10,152 (https://github.com/danbri/factoidal/issues/867). `Term.toNTriplesLoop`
appends to one string and takes no frame for a nesting level; `Term.toNTriples_eq_fast`
proves it equal, and `@[csimp]` makes every caller compiled after it run the loop:
`Triple.toNTriples`, `Graph.toNTriples`, `Dataset.toNQuads`, the stream writers and the
answer of a CONSTRUCT query. The loop is the one of `Term.toCanonicalNTriplesLoop` below,
and uses the same helpers (`tripleTermOpen`, `appendClosers`, `closersStr`, defined above).
The specification fails in three cases only: in `.rdf11` a triple term and a directional
literal, and in both modes a language tag outside `langTagWritable`. The loop fails in the
same three. -/

/-- The text of a term that is not a triple term, written by the specification, and then the
closers of the `k` open triple terms. -/
def toNTriplesClose (mode : Mode) (t : Term) (acc : String) (k : Nat) : Except String String :=
  match Term.toNTriples mode t with
  | .error e => .error e
  | .ok str => .ok (appendClosers (acc ++ str) k)

/-- The loop of `Term.toNTriplesFast`. `acc` is the text so far and `k` the number of triple
terms open in it: a triple term appends its opening and continues with its object (under
`.rdf11` it is the error), a term that is not a triple term appends its text and the `k`
closers. Every call of the loop on itself is a tail call, and `acc` is appended to in
place. -/
def Term.toNTriplesLoop (mode : Mode) : Term → String → Nat → Except String String
  | .tripleTerm s p o, acc, k =>
      if mode = .rdf11 then .error "RDF 1.2 triple term requires mode .rdf12"
      else Term.toNTriplesLoop mode o (acc ++ tripleTermOpen s p) (k + 1)
  | .iri i, acc, k => toNTriplesClose mode (.iri i) acc k
  | .bnode b, acc, k => toNTriplesClose mode (.bnode b) acc k
  | .literal wl, acc, k => toNTriplesClose mode (.literal wl) acc k

theorem toNTriplesClose_eq (mode : Mode) (t : Term) (acc : String) (k : Nat) :
    toNTriplesClose mode t acc k =
      match Term.toNTriples mode t with
      | .error e => .error e
      | .ok str => .ok (acc ++ str ++ closersStr k) := by
  unfold toNTriplesClose
  cases Term.toNTriples mode t with
  | error e => rfl
  | ok str => simp [appendClosers_eq]

/-- The loop, for every state it can be in: the text so far, the specification on the
term, and the closers of the open triple terms; or the error that the specification gives. -/
theorem Term.toNTriplesLoop_eq (mode : Mode) :
    ∀ (t : Term) (acc : String) (k : Nat),
      Term.toNTriplesLoop mode t acc k =
        match Term.toNTriples mode t with
        | .error e => .error e
        | .ok str => .ok (acc ++ str ++ closersStr k)
  | .tripleTerm s p o, acc, k => by
      rw [Term.toNTriplesLoop]
      by_cases hm : mode = .rdf11
      · simp [hm, Term.toNTriples]
      · simp only [hm, if_false]
        rw [Term.toNTriplesLoop_eq mode o]
        simp only [Term.toNTriples, hm, if_false]
        cases Term.toNTriples mode o with
        | error e => rfl
        | ok oStr =>
          simp only [closersStr_succ, tripleTermOpen, String.append_assoc]
  | .iri i, acc, k => by rw [Term.toNTriplesLoop, toNTriplesClose_eq]
  | .bnode b, acc, k => by rw [Term.toNTriplesLoop, toNTriplesClose_eq]
  | .literal wl, acc, k => by rw [Term.toNTriplesLoop, toNTriplesClose_eq]

/-- `Term.toNTriples` as a loop. -/
def Term.toNTriplesFast (mode : Mode) (t : Term) : Except String String :=
  Term.toNTriplesLoop mode t "" 0

theorem Term.toNTriplesFast_eq (mode : Mode) (t : Term) :
    Term.toNTriplesFast mode t = Term.toNTriples mode t := by
  unfold Term.toNTriplesFast
  rw [Term.toNTriplesLoop_eq]
  cases Term.toNTriples mode t with
  | error e => rfl
  | ok s => simp [closersStr_zero]

/-- Any call of the specification compiled after this line runs the loop. -/
@[csimp] theorem Term.toNTriples_eq_fast : @Term.toNTriples = @Term.toNTriplesFast := by
  funext mode t; exact (Term.toNTriplesFast_eq mode t).symm

#print axioms Term.toNTriplesLoop_eq
#print axioms Term.toNTriples_eq_fast

/-- Serialise one `Triple` as an N-Triples line, `" .\n"`-terminated.
Port of `nq_line_for_triple_default_graph`. -/
def Triple.toNTriples (mode : Mode) (t : Triple) : Except String String :=
  match Term.toNTriples mode t.o with
  | .error e => .error e
  | .ok oStr => .ok (Subject.toNTriples t.s ++ " <" ++ t.p.val ++ "> " ++ oStr ++ " .\n")

/-- Serialise a whole graph, one line per triple, input order preserved.
Fails (propagating the first offending triple's message) if any triple
needs RDF 1.2 syntax under `.rdf11`. Not a direct F* port (the F* source
has no single "serialise a whole in-memory graph" entry point at this
layer — callers fold `nq_line_for_triple_default_graph` themselves) but a
straightforward `List.foldl`/`Except` composition of it. -/
def Graph.toNTriples (g : Graph) (mode : Mode := .rdf11) : Except String String :=
  g.foldl (fun acc t =>
    match acc with
    | .error e => .error e
    | .ok s =>
        match Triple.toNTriples mode t with
        | .error e => .error e
        | .ok line => .ok (s ++ line))
    (.ok "")

/-! ### `Graph.toNTriples` one line at a time

`Graph.toNTriples` builds the whole document as one string. A caller that
writes the lines as it goes (the command line's `closure` verb,
https://github.com/danbri/factoidal/issues/758) needs to know, before the
first line, whether some triple fails, because `Graph.toNTriples` then gives
only the error. `Graph.firstNTriplesError` is that error, and
`Graph.toNTriples_eq_lines` proves that the document is the error when there
is one, and otherwise the concatenation of `Triple.toNTriplesLine` over the
triples, in order. -/

/-- The error `Triple.toNTriples` gives on `t`, if any. -/
def Triple.nTriplesError? (mode : Mode) (t : Triple) : Option String :=
  match Triple.toNTriples mode t with
  | .error e => some e
  | .ok _ => none

/-- The N-Triples line of `t`; the empty string when `t` does not serialise
in `mode` (a caller asks `Graph.firstNTriplesError` first). -/
def Triple.toNTriplesLine (mode : Mode) (t : Triple) : String :=
  match Triple.toNTriples mode t with
  | .ok line => line
  | .error _ => ""

/-- The first triple's error, in graph order: the error `Graph.toNTriples`
reports. -/
def Graph.firstNTriplesError (g : Graph) (mode : Mode := .rdf11) : Option String :=
  g.findSome? (Triple.nTriplesError? mode)

private theorem toNTriples_foldl_error (mode : Mode) (l : List Triple) (e : String) :
    l.foldl (fun acc t =>
      match acc with
      | .error e => .error e
      | .ok s =>
          match Triple.toNTriples mode t with
          | .error e => .error e
          | .ok line => .ok (s ++ line)) (Except.error e) = .error e := by
  induction l with
  | nil => rfl
  | cons t rest ih => exact ih

private theorem toNTriples_foldl_ok (mode : Mode) (l : List Triple) (s : String) :
    l.foldl (fun acc t =>
      match acc with
      | .error e => .error e
      | .ok s =>
          match Triple.toNTriples mode t with
          | .error e => .error e
          | .ok line => .ok (s ++ line)) (Except.ok s) =
      match l.findSome? (Triple.nTriplesError? mode) with
      | some e => .error e
      | none => .ok (s ++ String.join (l.map (Triple.toNTriplesLine mode))) := by
  induction l generalizing s with
  | nil => simp [String.append_empty, String.join_nil]
  | cons t rest ih =>
      simp only [List.foldl_cons, List.findSome?_cons, List.map_cons, String.join_cons]
      cases h : Triple.toNTriples mode t with
      | error e =>
          have he : Triple.nTriplesError? mode t = some e := by
            simp [Triple.nTriplesError?, h]
          rw [he]
          exact toNTriples_foldl_error mode rest e
      | ok line =>
          have he : Triple.nTriplesError? mode t = none := by
            simp [Triple.nTriplesError?, h]
          have hl : Triple.toNTriplesLine mode t = line := by
            simp [Triple.toNTriplesLine, h]
          rw [he, hl]
          simp only
          rw [ih (s ++ line)]
          cases rest.findSome? (Triple.nTriplesError? mode) with
          | some e => rfl
          | none => simp [String.append_assoc]

/-- `Graph.toNTriples` is the first triple's error when there is one, and
otherwise the lines of the triples, in order, concatenated. -/
theorem Graph.toNTriples_eq_lines (g : Graph) (mode : Mode) :
    Graph.toNTriples g mode =
      match Graph.firstNTriplesError g mode with
      | some e => .error e
      | none => .ok (String.join (g.map (Triple.toNTriplesLine mode))) := by
  unfold Graph.toNTriples Graph.firstNTriplesError
  rw [toNTriples_foldl_ok]
  cases g.findSome? (Triple.nTriplesError? mode) with
  | some e => rfl
  | none => simp [String.empty_append]

#print axioms Graph.toNTriples_eq_lines

/-! ## Canonical N-Triples (RDF 1.2 N-Triples §canonical form)

https://www.w3.org/TR/rdf12-n-triples/#canonical-ntriples — the form the
W3C `rdf12/rdf-n-triples/c14n` and `rdf12/rdf-n-quads/c14n` suites
compare BYTE FOR BYTE. Port of `RDF.NQuads.Serialize.fst`'s
`nq_canon_*` group (`canon_hex_upper`, `canon_byte_uchar`,
`nq_canon_special_byte`, `nq_canon_escape_byte`, `nq_canon_walk`,
`nq_canon_term`, `nq_canon_line_default`, `canonical_nt_document`).

What canonical form fixes, and what it does NOT:

  * one space between terms, one `" .\n"`-terminated line per triple;
  * the shortest escape for `\b \t \n \f \r \" \\`, an uppercase
    `\u00XX` for every other C0 control and for DEL (U+007F), and
    `￾` / `￿` for the two BMP non-characters;
  * language tags lowercased, the base direction kept as `--ltr` /
    `--rtl`;
  * `xsd:string` written with no datatype;
  * blank-node labels and statement ORDER are preserved. This is
    canonical SERIALISATION, not RDFC-1.0 canonicalisation (which
    relabels blank nodes and sorts — see `RDF/Canonical.lean`).

The F* source walks UTF-8 BYTES; this walks Unicode CHARACTERS. The two
agree: every byte the F* escapes is below 0x80, so it can only be a
one-byte UTF-8 sequence, and the U+FFFE / U+FFFF cases the F* matches as
the byte triples `EF BF BE` / `EF BF BF` are exactly those codepoints. -/

/-- Uppercase hexadecimal digit for a nibble. Port of `canon_hex_upper`. -/
def canonHexUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- `\u00XX` (uppercase hex) for a codepoint below 0x100. Port of
`canon_byte_uchar`. -/
def canonUchar2 (n : Nat) : String :=
  "\\u00" ++ String.ofList [canonHexUpper (n / 16), canonHexUpper (n % 16)]

/-- The canonical escape for one character, `none` when the character
passes through unchanged. Port of `nq_canon_special_byte` +
`nq_canon_escape_byte`, plus the U+FFFE / U+FFFF non-character rule
`nq_canon_walk` applies inline. -/
def canonEscapeChar (c : Char) : Option String :=
  let n := c.toNat
  if n == 0x08 then some "\\b"
  else if n == 0x09 then some "\\t"
  else if n == 0x0A then some "\\n"
  else if n == 0x0C then some "\\f"
  else if n == 0x0D then some "\\r"
  else if n == 0x22 then some "\\\""
  else if n == 0x5C then some "\\\\"
  else if n < 0x20 || n == 0x7F then some (canonUchar2 n)
  else if n == 0xFFFE || n == 0xFFFF then some ("\\u" ++ String.ofList
    [canonHexUpper (n / 4096 % 16), canonHexUpper (n / 256 % 16),
     canonHexUpper (n / 16 % 16), canonHexUpper (n % 16)])
  else none

/-- A literal's lexical form, canonically escaped. Port of
`nq_canon_escape_literal` / `nq_canon_walk`. -/
def canonEscapeLiteral (s : String) : String :=
  String.join (s.toList.map (fun c =>
    match canonEscapeChar c with
    | some e => e
    | none   => String.singleton c))

/-- Canonical form of a term in object position. Port of
`nq_canon_term`. Total: canonical N-Triples IS RDF 1.2, so there is no
mode parameter and no failure case. -/
def Term.toCanonicalNTriples : Term → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .literal wl =>
      let l := wl.val
      let esc := canonEscapeLiteral l.lexicalForm
      match l.langTag with
      | some tag =>
          let dirSuffix := match l.direction with
            | some .ltr => "--ltr"
            | some .rtl => "--rtl"
            | none      => ""
          "\"" ++ esc ++ "\"@" ++ tag.map Char.toLower ++ dirSuffix
      | none =>
          if l.datatype = xsdString then "\"" ++ esc ++ "\""
          else "\"" ++ esc ++ "\"^^<" ++ l.datatype.val ++ ">"
  | .tripleTerm s p o =>
      "<<( " ++ Subject.toNTriples s ++ " <" ++ p.val ++ "> " ++
      Term.toCanonicalNTriples o ++ " )>>"

/-! ### The canonical text of a triple term nested deep

`Term.toCanonicalNTriples` above is the SPECIFICATION. It takes one native frame for
each level of triple-term nesting, and at each level it copies the text of the levels
below (`"<<( " ++ ... ++ below ++ " )>>"`), so its time is quadratic in the depth. A
triple term nested 300,000 deep, read from Turtle, did not finish in 120 s
(https://github.com/danbri/factoidal/issues/865). `Term.toCanonicalNTriplesLoop` appends
to one string and takes no frame for a nesting level; `Term.toCanonicalNTriples_eq_fast`
proves it equal, and `@[csimp]` makes every caller compiled after it run the loop. The
helpers `closersStr`, `appendClosers` and `tripleTermOpen` are defined above `Term.toNTriples`,
which has a loop of the same shape (https://github.com/danbri/factoidal/issues/867). -/

/-- The loop of `Term.toCanonicalNTriplesFast`. `acc` is the text so far and `k` the
number of triple terms open in it: a triple term appends its opening and continues with
its object, a term that is not a triple term appends its text and the `k` closers. Every
call of the loop on itself is a tail call, and `acc` is appended to in place. -/
def Term.toCanonicalNTriplesLoop : Term → String → Nat → String
  | .tripleTerm s p o, acc, k => Term.toCanonicalNTriplesLoop o (acc ++ tripleTermOpen s p) (k + 1)
  | .iri i, acc, k => appendClosers (acc ++ ("<" ++ i.val ++ ">")) k
  | .bnode b, acc, k => appendClosers (acc ++ ("_:" ++ b)) k
  | .literal wl, acc, k =>
      let l := wl.val
      let esc := canonEscapeLiteral l.lexicalForm
      appendClosers
        (acc ++ (match l.langTag with
          | some tag =>
              let dirSuffix := match l.direction with
                | some .ltr => "--ltr"
                | some .rtl => "--rtl"
                | none      => ""
              "\"" ++ esc ++ "\"@" ++ tag.map Char.toLower ++ dirSuffix
          | none =>
              if l.datatype = xsdString then "\"" ++ esc ++ "\""
              else "\"" ++ esc ++ "\"^^<" ++ l.datatype.val ++ ">")) k

/-- The loop, for every state it can be in: the text so far, the specification on the
term, and the closers of the open triple terms. -/
theorem Term.toCanonicalNTriplesLoop_eq :
    ∀ (t : Term) (acc : String) (k : Nat),
      Term.toCanonicalNTriplesLoop t acc k = acc ++ Term.toCanonicalNTriples t ++ closersStr k
  | .tripleTerm s p o, acc, k => by
      rw [Term.toCanonicalNTriplesLoop, Term.toCanonicalNTriplesLoop_eq o, closersStr_succ]
      have : Term.toCanonicalNTriples (.tripleTerm s p o) =
          tripleTermOpen s p ++ Term.toCanonicalNTriples o ++ " )>>" := by
        simp only [Term.toCanonicalNTriples, tripleTermOpen, String.append_assoc]
      rw [this]
      simp only [String.append_assoc]
  | .iri i, acc, k => by
      rw [Term.toCanonicalNTriplesLoop, appendClosers_eq]
      rfl
  | .bnode b, acc, k => by
      rw [Term.toCanonicalNTriplesLoop, appendClosers_eq]
      rfl
  | .literal wl, acc, k => by
      rw [Term.toCanonicalNTriplesLoop, appendClosers_eq]
      rfl

/-- `Term.toCanonicalNTriples` as a loop. -/
def Term.toCanonicalNTriplesFast (t : Term) : String :=
  Term.toCanonicalNTriplesLoop t "" 0

theorem Term.toCanonicalNTriplesFast_eq (t : Term) :
    Term.toCanonicalNTriplesFast t = Term.toCanonicalNTriples t := by
  unfold Term.toCanonicalNTriplesFast
  rw [Term.toCanonicalNTriplesLoop_eq, closersStr_zero]
  simp

/-- Any call of the specification compiled after this line runs the loop: the canonical
line of a triple, and so the N-Quads text that the parse ops answer. -/
@[csimp] theorem Term.toCanonicalNTriples_eq_fast :
    @Term.toCanonicalNTriples = @Term.toCanonicalNTriplesFast := by
  funext t; exact (Term.toCanonicalNTriplesFast_eq t).symm

#print axioms Term.toCanonicalNTriplesLoop_eq
#print axioms Term.toCanonicalNTriples_eq_fast

/-- One canonical line, `" .\n"`-terminated. Port of
`nq_canon_line_default`. -/
def Triple.toCanonicalNTriples (t : Triple) : String :=
  Subject.toNTriples t.s ++ " <" ++ t.p.val ++ "> " ++
  Term.toCanonicalNTriples t.o ++ " .\n"

/-- Canonical N-Triples document: one line per triple, input order.
Port of `canonical_nt_document`. -/
def Graph.toCanonicalNTriples (g : Graph) : String :=
  String.join (g.map Triple.toCanonicalNTriples)

end L4Factoidal.Syntax
