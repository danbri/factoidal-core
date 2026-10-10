/-
L4Factoidal.Syntax.Diagnostics — the diagnostic record of the lenient
(recovery) parse mode, https://github.com/danbri/factoidal/issues/716.

Owner, 2026-10-10, verbatim: "#716 is important for building validators and
for streaming huge datasets through a parser".

A strict parser stops at the first `ParseError` (`Syntax.Lexing`: a message
and a 0-based offset). A lenient parser records the error as a `Diagnostic`,
skips to the next synchronisation point and continues. A validator needs each
diagnostic to carry:

  * `offset` — 0-based, counted in Unicode scalar values from the start of
    the document (the strict parsers' `ParseError.pos`, unchanged);
  * `line` — 1-based; a line ends at each LINE FEED (U+000A). A lone
    CARRIAGE RETURN does not start a line, and a CR LF pair is one line end
    (the LF). This is the convention of the strict-parse error envelope
    (`Wasm/Ops/Parse.lean`, `lineColumnOfOffset`) and of the F* entry
    (`Parser.Diagnostics.position_of_offset`), so the first diagnostic of a
    lenient parse and the error of a strict parse of the same text name the
    same line and column;
  * `column` — 1-based, counted in Unicode scalar values from the start of
    the line;
  * `cls` — a stable error class (`DiagnosticClass`), one constructor per
    kind of error the N-Triples, N-Quads, Turtle and TriG grammars report;
  * `message` — the grammar's own message.

The class is decided from the grammar's message (`classifyParseMessage`), so
the strict parsers and their theorems are unchanged. Every message literal the
four grammars and `Syntax.Lexing` produce is listed in a `#guard` below with
its class; a new message that falls through to `unexpectedToken` is a
deliberate decision, made by adding its guard.

`LinePos` is the line state the lenient parsers carry. It changes only at a
LINE FEED, so a parser can skip advancing it over text that holds none (the
N-Triples and N-Quads lenient walks advance it only over line ends, because
no N-Triples or N-Quads token can contain a raw line break).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

/-! ## Error classes -/

/-- The kind of a syntax error. The names are stable: hosts render them with
`DiagnosticClass.tag` and a validator may filter on them. -/
inductive DiagnosticClass where
  /-- A prefixed name whose prefix no `@prefix` / `PREFIX` declared
  (Turtle and TriG). -/
  | undefinedPrefix
  /-- A relative IRI reference with no base IRI to resolve it against, or
  an IRI that is not absolute. -/
  | relativeIri
  /-- An IRIREF that is not well formed: an unterminated `<…`, or a
  character IRIREF excludes. -/
  | badIri
  /-- A bad escape sequence: `\q`, an incomplete or non-hex `\u` / `\U`,
  a surrogate or out-of-range code point, a backslash at the end of input,
  an escape forbidden in an IRIREF. -/
  | badEscape
  /-- A string literal that does not close on its line (short strings) or
  before the end of input (long strings). -/
  | unterminatedString
  /-- A literal that is not well formed: a bad language tag or base
  direction, a bad numeric or boolean literal, a missing datatype after
  `^^`. -/
  | badLiteral
  /-- A blank node label that is empty or starts with a character
  BLANK_NODE_LABEL excludes. -/
  | badBlankNode
  /-- A prefixed name whose prefix or local part is not well formed. -/
  | badPrefixedName
  /-- A directive that is not well formed or not allowed where it is
  (`@prefix`, `@base`, `@version`, `PREFIX`, `BASE`, `VERSION`). -/
  | badDirective
  /-- A graph label that is not an IRI or blank node, or a TriG graph block
  that is not well formed (`GRAPH` with no name, nested `GRAPH`). -/
  | badGraphName
  /-- RDF 1.2 syntax (triple terms, reified triples, annotations,
  `VERSION`) in an RDF 1.1 document, or the retired `<< s p o >>` form. -/
  | rdf12Syntax
  /-- A collection, blank node property list, annotation block, triple term
  or graph block that is not closed. -/
  | unclosedGroup
  /-- Nesting deeper than the parser's recursion bound. -/
  | nestingLimit
  /-- Any other token where the grammar expects something else (a missing
  `.`, subject, predicate or object). -/
  | unexpectedToken
  /-- A parser invariant failed (fuel exhausted, no progress). Not reachable
  on any input the parsers' fuel arguments cover. -/
  | internal
  /-- Lenient mode only: the `maxErrors` bound was reached and the parse
  stopped. The diagnostic carries the position of the error that was over
  the bound. -/
  | tooManyErrors
  deriving DecidableEq, Repr, Inhabited

/-- The stable name of a class, as hosts render it (JSON `class`). -/
def DiagnosticClass.tag : DiagnosticClass → String
  | .undefinedPrefix    => "undefined-prefix"
  | .relativeIri        => "relative-iri"
  | .badIri             => "bad-iri"
  | .badEscape          => "bad-escape"
  | .unterminatedString => "unterminated-string"
  | .badLiteral         => "bad-literal"
  | .badBlankNode       => "bad-blank-node"
  | .badPrefixedName    => "bad-prefixed-name"
  | .badDirective       => "bad-directive"
  | .badGraphName       => "bad-graph-name"
  | .rdf12Syntax        => "rdf12-syntax"
  | .unclosedGroup      => "unclosed-group"
  | .nestingLimit       => "nesting-limit"
  | .unexpectedToken    => "unexpected-token"
  | .internal           => "internal"
  | .tooManyErrors      => "too-many-errors"

/-- `sub` occurs in `s`. -/
private def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The class of a grammar error, decided from its message. The tests are
ordered: the first that matches decides. -/
def classifyParseMessage (msg : String) : DiagnosticClass :=
  let has := hasSub msg
  if msg.startsWith "undefined prefix" then .undefinedPrefix
  else if msg.startsWith "relative IRI" || msg.startsWith "invalid IRI (not absolute" then
    .relativeIri
  else if has "unterminated string" || has "unterminated long string" ||
      has "unescaped newline" || has "unescaped carriage return" ||
      has "string literal too long" then .unterminatedString
  else if has "escape" || has "backslash at end" then .badEscape
  else if has "unterminated IRIREF" || has "character in IRIREF" ||
      msg.startsWith "expected '<' (IRIREF)" then .badIri
  else if has "VERSION directive" || has "after @prefix" || has "after @base" ||
      has "after @version" || has "directives are not allowed" ||
      msg.startsWith "not a prefix directive" || msg.startsWith "not a base directive" ||
      msg.startsWith "not a version directive" then .badDirective
  else if has "language tag" || has "base direction" || has "ill-formed literal" ||
      has "numeric literal" || has "digit after '.'" || has "boolean literal" ||
      msg == "expected '^^'" || msg == "expected '@'" ||
      msg.startsWith "expected string literal" || msg.startsWith "expected '\"'" then .badLiteral
  else if has "blank node label" || has "'_:'" then .badBlankNode
  else if has "prefixed name" || has "PNAME_NS" then .badPrefixedName
  else if has "graph name" || has "graph label" || has "nested GRAPH" then .badGraphName
  else if has "RDF 1.2" || has "legacy '<< >>'" then .rdf12Syntax
  else if has "unterminated collection" || has "unterminated graph block" ||
      has "closing blank node property list" || has "closing annotation block" ||
      has "closing triple term" || has "closing reified triple" ||
      msg == "expected ')>>'" then .unclosedGroup
  else if has "nesting too deep" || has "recursion limit" then .nestingLimit
  else if has "internal error" || has "fuel exhausted" || has "made no progress" then .internal
  else .unexpectedToken

/-! ## Line state -/

/-- The line state at some offset: the 1-based line number and the offset
of the first character of that line. -/
structure LinePos where
  line : Nat := 1
  lineStart : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Advance over the next `n` characters of `cs`, whose first character is at
offset `off`. Only LINE FEED starts a line. Tail recursive. -/
def LinePos.advance : LinePos → Nat → Nat → List Char → LinePos
  | lp, _, 0, _ => lp
  | lp, _, _ + 1, [] => lp
  | lp, off, n + 1, c :: cs =>
      LinePos.advance (if c == '\n' then { line := lp.line + 1, lineStart := off + 1 } else lp)
        (off + 1) n cs

/-! ## The diagnostic record -/

/-- One recovered syntax error. -/
structure Diagnostic where
  cls : DiagnosticClass
  message : String
  /-- 0-based, Unicode scalar values from the start of the document. -/
  offset : Nat
  /-- 1-based; lines end at LINE FEED. -/
  line : Nat
  /-- 1-based, Unicode scalar values from the start of the line. -/
  column : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The diagnostic for `e`, raised while reading `cs`, whose first character
is at offset `off` on the line state `lp`. The line and column come from
walking `cs` up to `e.pos`. -/
def Diagnostic.ofError (lp : LinePos) (off : Nat) (cs : List Char) (e : ParseError) :
    Diagnostic :=
  let lp' := lp.advance off (e.pos - off) cs
  { cls := classifyParseMessage e.msg, message := e.msg, offset := e.pos,
    line := lp'.line, column := e.pos - lp'.lineStart + 1 }

/-- The final diagnostic of a parse stopped by `maxErrors = m`: the position
of the error over the bound, class `tooManyErrors`. -/
def Diagnostic.overLimit (m : Nat) (d : Diagnostic) : Diagnostic :=
  { d with cls := .tooManyErrors,
           message := s!"parse stopped: more than {m} errors (maxErrors); the next error was: {d.message}" }

/-- `line:column: class: message`, the text form a command line prints. -/
def Diagnostic.render (d : Diagnostic) : String :=
  s!"{d.line}:{d.column}: {d.cls.tag}: {d.message}"

/-! ## Lenient-mode options -/

/-- Options every lenient parser takes. `maxErrors = some m` stops the parse
at the error after the `m`-th, with one `tooManyErrors` diagnostic; `none`
never stops. -/
structure LenientOptions where
  maxErrors : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- One more error may be reported after `n`. -/
def LenientOptions.allows (o : LenientOptions) (n : Nat) : Bool :=
  match o.maxErrors with
  | none => true
  | some m => n < m

/-! ## Build-time checks -/

-- Every message literal of the four grammars and `Syntax.Lexing`, with its
-- class (the list is `grep -ho '⟨s\?!\?"[^"]*"'` over Lexing.lean,
-- NTriples.lean, NQuads.lean, Turtle.lean and TriG.lean, 2026-10-10).
#guard classifyParseMessage "undefined prefix: ex" == .undefinedPrefix
#guard classifyParseMessage "relative IRI <a> with no base to resolve against" == .relativeIri
#guard classifyParseMessage "invalid IRI (not absolute — missing ':'): <a>" == .relativeIri
#guard classifyParseMessage "invalid escape: \\q" == .badEscape
#guard classifyParseMessage "invalid hex digit in \\u escape" == .badEscape
#guard classifyParseMessage "invalid hex digit in \\U escape" == .badEscape
#guard classifyParseMessage "incomplete \\u escape" == .badEscape
#guard classifyParseMessage "incomplete \\U escape" == .badEscape
#guard classifyParseMessage "incomplete \\u escape in IRIREF" == .badEscape
#guard classifyParseMessage "incomplete \\U escape in IRIREF" == .badEscape
#guard classifyParseMessage "invalid escape in IRIREF (only \\u/\\U permitted)" == .badEscape
#guard classifyParseMessage "backslash at end of IRIREF" == .badEscape
#guard classifyParseMessage "backslash at end of string literal" == .badEscape
#guard classifyParseMessage "backslash at end of input" == .badEscape
#guard classifyParseMessage "IRI-forbidden codepoint in \\u escape" == .badEscape
#guard classifyParseMessage "surrogate or out-of-range codepoint U+D800 in escape" == .badEscape
#guard classifyParseMessage "unterminated IRIREF (expected '>')" == .badIri
#guard classifyParseMessage "invalid character in IRIREF" == .badIri
#guard classifyParseMessage "expected '<' (IRIREF)" == .badIri
#guard classifyParseMessage "unterminated string literal" == .unterminatedString
#guard classifyParseMessage "unterminated string literal (expected '\"')" == .unterminatedString
#guard classifyParseMessage "unterminated long string" == .unterminatedString
#guard classifyParseMessage "unescaped newline in string literal" == .unterminatedString
#guard classifyParseMessage "unescaped carriage return in string literal" == .unterminatedString
#guard classifyParseMessage "string literal too long" == .unterminatedString
#guard classifyParseMessage "language tag must start with a letter" == .badLiteral
#guard classifyParseMessage "expected language tag after '@'" == .badLiteral
#guard classifyParseMessage "invalid language tag" == .badLiteral
#guard classifyParseMessage "invalid base direction (expected ltr or rtl)" == .badLiteral
#guard classifyParseMessage "ill-formed literal (language tag / direction / datatype combination)" == .badLiteral
#guard classifyParseMessage "expected numeric literal" == .badLiteral
#guard classifyParseMessage "expected digit after '.'" == .badLiteral
#guard classifyParseMessage "expected boolean literal" == .badLiteral
#guard classifyParseMessage "expected '^^'" == .badLiteral
#guard classifyParseMessage "expected '@'" == .badLiteral
#guard classifyParseMessage "expected string literal" == .badLiteral
#guard classifyParseMessage "expected '\"' (STRING_LITERAL_QUOTED)" == .badLiteral
#guard classifyParseMessage "invalid blank node label start character" == .badBlankNode
#guard classifyParseMessage "empty blank node label" == .badBlankNode
#guard classifyParseMessage "expected '_:' (BLANK_NODE_LABEL)" == .badBlankNode
#guard classifyParseMessage "invalid prefix in prefixed name" == .badPrefixedName
#guard classifyParseMessage "invalid prefixed name local part" == .badPrefixedName
#guard classifyParseMessage "expected prefixed name" == .badPrefixedName
#guard classifyParseMessage "expected ':' in prefixed name" == .badPrefixedName
#guard classifyParseMessage "expected PNAME_NS (prefix followed by ':')" == .badPrefixedName
#guard classifyParseMessage "expected '.' after @prefix directive" == .badDirective
#guard classifyParseMessage "expected '.' after @base directive" == .badDirective
#guard classifyParseMessage "expected '.' after @version directive" == .badDirective
#guard classifyParseMessage "long string not allowed in VERSION directive" == .badDirective
#guard classifyParseMessage "expected string literal in VERSION directive" == .badDirective
#guard classifyParseMessage "directives are not allowed inside a graph block" == .badDirective
#guard classifyParseMessage "not a prefix directive" == .badDirective
#guard classifyParseMessage "not a base directive" == .badDirective
#guard classifyParseMessage "not a version directive" == .badDirective
#guard classifyParseMessage "literals are not allowed as graph names in N-Quads" == .badGraphName
#guard classifyParseMessage "expected graph label (IRIREF or BLANK_NODE_LABEL)" == .badGraphName
#guard classifyParseMessage "expected a graph name after GRAPH" == .badGraphName
#guard classifyParseMessage "expected '{' after graph name" == .badGraphName
#guard classifyParseMessage "expected ']' for anonymous blank node graph name" == .badGraphName
#guard classifyParseMessage "nested GRAPH is not allowed inside a graph block" == .badGraphName
#guard classifyParseMessage "triple term <<( )>> requires RDF 1.2 mode" == .rdf12Syntax
#guard classifyParseMessage "reified triple << >> requires RDF 1.2 mode" == .rdf12Syntax
#guard classifyParseMessage "not RDF 1.2" == .rdf12Syntax
#guard classifyParseMessage "legacy '<< >>' quoted triple is not RDF 1.2 syntax" == .rdf12Syntax
#guard classifyParseMessage "unterminated collection (expected ')')" == .unclosedGroup
#guard classifyParseMessage "unterminated graph block (expected '}')" == .unclosedGroup
#guard classifyParseMessage "expected ']' closing blank node property list" == .unclosedGroup
#guard classifyParseMessage "expected '|}' closing annotation block" == .unclosedGroup
#guard classifyParseMessage "expected ')>>' closing triple term" == .unclosedGroup
#guard classifyParseMessage "expected '>>' closing reified triple" == .unclosedGroup
#guard classifyParseMessage "expected ')>>'" == .unclosedGroup
#guard classifyParseMessage "triple-term nesting too deep" == .nestingLimit
#guard classifyParseMessage "reified-triple nesting too deep" == .nestingLimit
#guard classifyParseMessage "recursion limit in object" == .nestingLimit
#guard classifyParseMessage "recursion limit in collection tail" == .nestingLimit
#guard classifyParseMessage "internal error: parser fuel exhausted (should be unreachable)" == .internal
#guard classifyParseMessage "Turtle statement fuel exhausted" == .internal
#guard classifyParseMessage "Turtle statement made no progress" == .internal
#guard classifyParseMessage "expected '.' terminator" == .unexpectedToken
#guard classifyParseMessage "expected '.' after triple" == .unexpectedToken
#guard classifyParseMessage "expected predicate after subject" == .unexpectedToken
#guard classifyParseMessage "expected subject" == .unexpectedToken
#guard classifyParseMessage "expected subject (IRIREF or BLANK_NODE_LABEL)" == .unexpectedToken
#guard classifyParseMessage "expected object" == .unexpectedToken
#guard classifyParseMessage "expected object (IRIREF, BLANK_NODE_LABEL, or literal)" == .unexpectedToken
#guard classifyParseMessage "expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term)" == .unexpectedToken
#guard classifyParseMessage "collection did not produce a valid subject" == .unexpectedToken
#guard classifyParseMessage "blank node property list not allowed in a triple term" == .unexpectedToken
#guard classifyParseMessage "expected 'a'" == .unexpectedToken
#guard classifyParseMessage "expected '~'" == .unexpectedToken
#guard classifyParseMessage "expected '<<'" == .unexpectedToken
#guard classifyParseMessage "expected reified-triple subject" == .unexpectedToken
#guard classifyParseMessage "collection not allowed in a triple term" == .unexpectedToken
#guard classifyParseMessage "triple term is not allowed as a subject" == .unexpectedToken
#guard classifyParseMessage "empty annotation block" == .unexpectedToken

-- Tags are distinct (a host may key on them).
#guard ([DiagnosticClass.undefinedPrefix, .relativeIri, .badIri, .badEscape,
          .unterminatedString, .badLiteral, .badBlankNode, .badPrefixedName,
          .badDirective, .badGraphName, .rdf12Syntax, .unclosedGroup, .nestingLimit,
          .unexpectedToken, .internal, .tooManyErrors].map DiagnosticClass.tag).eraseDups.length
        == 16

-- Line state: only LF starts a line; CR LF is one line end; lone CR is not.
#guard LinePos.advance {} 0 3 "abc".toList == { line := 1, lineStart := 0 }
#guard LinePos.advance {} 0 3 "ab\ncd".toList == { line := 2, lineStart := 3 }
#guard LinePos.advance {} 0 5 "a\r\nb\nc".toList == { line := 3, lineStart := 5 }
#guard LinePos.advance {} 0 4 "a\rbc".toList == { line := 1, lineStart := 0 }
-- Advancing in two steps is advancing once.
#guard (LinePos.advance (LinePos.advance {} 0 2 "a\nb\nc".toList) 2 3 "b\nc".toList)
        == LinePos.advance {} 0 5 "a\nb\nc".toList
-- Advancing past the end of the list stops at the end.
#guard LinePos.advance {} 0 99 "a\n".toList == { line := 2, lineStart := 2 }

-- A diagnostic's line and column, against `ParseError.pos`.
#guard Diagnostic.ofError {} 0 "ab\ncd".toList ⟨"expected '.' terminator", 4⟩
        == { cls := .unexpectedToken, message := "expected '.' terminator",
             offset := 4, line := 2, column := 2 }
#guard (Diagnostic.ofError {} 0 "ab".toList ⟨"x", 0⟩).column == 1
-- A diagnostic computed from a later start agrees with one from the document start.
#guard Diagnostic.ofError { line := 2, lineStart := 3 } 3 "cd\nef".toList ⟨"expected '.' terminator", 7⟩
        == Diagnostic.ofError {} 0 "ab\ncd\nef".toList ⟨"expected '.' terminator", 7⟩
-- Columns count Unicode scalar values, not bytes.
#guard (Diagnostic.ofError {} 0 "ééx".toList ⟨"x", 2⟩).column == 3

-- maxErrors.
#guard ({} : LenientOptions).allows 1000000
#guard ({ maxErrors := some 2 } : LenientOptions).allows 1
#guard !({ maxErrors := some 2 } : LenientOptions).allows 2
#guard !({ maxErrors := some 0 } : LenientOptions).allows 0
#guard (Diagnostic.overLimit 3 (Diagnostic.ofError {} 0 [] ⟨"expected subject", 0⟩)).cls
        == .tooManyErrors

end L4Factoidal.Syntax
