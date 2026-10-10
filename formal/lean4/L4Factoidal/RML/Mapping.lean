/-
L4Factoidal.RML.Mapping — the RML mapping model and term generation,
ported from `formal/fstar/RML.Mapping.fst` and `RML.Eval.fst`.

Spec: RML-Core (https://w3id.org/rml/core/spec) — logical sources,
term maps, subject/predicate/object maps and referencing object maps.

A term map produces terms from a data record three ways: a CONSTANT,
a REFERENCE to a field, or a TEMPLATE with `{field}` placeholders.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.LangTag
import L4Factoidal.RDF.IriSyntax
import L4Factoidal.XSD.Datatypes
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.RML.Error

namespace L4Factoidal.RML

open L4Factoidal.RDF

/-- The term type a map produces.

    `iri` and `uri` are NOT synonyms, and the F* module records the
    correction: `rml:IRI` applies IRI-safe (RFC 3987) encoding, where
    most non-ASCII stays unencoded, while `rml:URI` applies URI-safe
    (RFC 3986, ASCII-only) percent-encoding. The two are observably
    different — `"Zoë Krüger"` under `rml:URI` becomes
    `"Zo%C3%AB%20Kr%C3%BCger"`, under `rml:IRI` it does not. -/
inductive TermType where
  | iri | uri | unsafeIri | blankNode | literal
deriving Repr, DecidableEq, Inhabited

inductive RefFormulation where
  | jsonPath | xPath | csv | other (s : String)
deriving Repr, DecidableEq, Inhabited

/-- How a term map produces its value. -/
inductive TermMapForm where
  | constant  (t : Term)
  | reference (field : String)
  | template  (raw : String)
  | unknown
deriving Repr

structure TermMap where
  form     : TermMapForm
  termType : Option TermType := none
  datatype : Option String := none
  language : Option String := none
deriving Repr

/-! ## Templates -/

inductive TemplateSegment where
  | literal   (s : String)
  | reference (field : String)
deriving Repr, DecidableEq

/-- Parse `a{field}b`. A backslash escapes a brace, which RML needs
    and RFC 6570 does not — the CSVW template port deliberately has no
    escaping, and these two must not be merged for that reason. -/
def parseTemplate (raw : String) : List TemplateSegment :=
  let rec go (cur : List Char) (acc : List TemplateSegment) (inBrace esc : Bool)
      : List Char → List TemplateSegment
    | [] =>
        if cur.isEmpty then acc
        else acc ++ [if inBrace then .reference (String.ofList cur.reverse)
                     else .literal (String.ofList cur.reverse)]
    | c :: rest =>
        if esc then go (c :: cur) acc inBrace false rest
        else if c == '\\' then go cur acc inBrace true rest
        else if !inBrace && c == '{' then
          let acc := if cur.isEmpty then acc
                     else acc ++ [.literal (String.ofList cur.reverse)]
          go [] acc true false rest
        else if inBrace && c == '}' then
          go [] (acc ++ [.reference (String.ofList cur.reverse)]) false false rest
        else go (c :: cur) acc inBrace false rest
  go [] [] false false raw.toList

/-- A STRICT parse of a string template: the syntax rules of RML-Core,
"Generating values with expressions", string templates.

* a pair of unescaped curly braces encloses a reference expression;
* a curly brace that does not enclose one MUST be escaped by `\`, and
  that includes a brace INSIDE a reference expression;
* a backslash MUST be escaped by another backslash, inside a reference
  expression as well.

`parseTemplate` above is the lenient reader the evaluator uses, and it
accepts every one of these mistakes (a lone `}` is literal text, `\a` is
`a`). The validator calls this one, so that a template the specification
calls invalid is rejected before any record is read. -/
def parseTemplateStrict (raw : String) : Except String (List TemplateSegment) :=
  let rec go (cur : List Char) (acc : List TemplateSegment) (inBrace : Bool)
      : List Char → Except String (List TemplateSegment)
    | [] =>
        if inBrace then .error "unterminated '{' in template"
        else if cur.isEmpty then .ok acc
        else .ok (acc ++ [.literal (String.ofList cur.reverse)])
    | '\\' :: c :: rest =>
        if c == '\\' || c == '{' || c == '}' then go (c :: cur) acc inBrace rest
        else .error s!"backslash must be escaped by a backslash (found '\\{c}')"
    | ['\\'] => .error "template ends with an unescaped backslash"
    | '{' :: rest =>
        if inBrace then .error "unescaped '{' inside a reference expression"
        else
          let acc := if cur.isEmpty then acc
                     else acc ++ [.literal (String.ofList cur.reverse)]
          go [] acc true rest
    | '}' :: rest =>
        if !inBrace then .error "unescaped '}' outside a reference expression"
        else if cur.isEmpty then .error "empty reference expression '{}'"
        else go [] (acc ++ [.reference (String.ofList cur.reverse)]) false rest
    | c :: rest => go (c :: cur) acc inBrace rest
  go [] [] false raw.toList

private def isUnreservedAscii (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') ||
  c == '-' || c == '.' || c == '_' || c == '~'

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)

private def pctEncode (c : Char) : String :=
  String.ofList ((String.mk [c]).toUTF8.toList.flatMap (fun b =>
    ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]))

/-- URI-safe encoding (RFC 3986): ASCII-only, so every non-ASCII
    character is percent-encoded. -/
def encodeUriSafe (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if isUnreservedAscii c then String.mk [c] else pctEncode c)) ""

/-- IRI-safe encoding (RFC 3987): the `iunreserved` set keeps most
    non-ASCII characters as themselves. -/
def encodeIriSafe (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if isUnreservedAscii c || c.toNat > 0x7F then String.mk [c] else pctEncode c)) ""

/-- Expand a template against a record. An ABSENT field makes the
    WHOLE template produce nothing — RML says a term map with an
    unresolved reference generates no term, which is not the same as
    generating an empty string. -/
def expandTemplate (segs : List TemplateSegment) (tt : TermType)
    (lookup : String → Option String) : Option String :=
  segs.foldl (fun acc seg =>
    match acc, seg with
    | none, _ => none
    | some s, .literal l => some (s ++ l)
    | some s, .reference f =>
        match lookup f with
        | none   => none
        | some v => some (s ++ (match tt with
            | .uri        => encodeUriSafe v
            | .unsafeIri  => v
            | _           => encodeIriSafe v))) (some "")

/-! ## Term generation -/

/-- The rule a data error cites. -/
private def termGenerationRules : String :=
  "RML-Core, Generated RDF Term of a Term Map: term generation rules"

/-- Build an IRI term, resolving a RELATIVE result against the base
    IRI when one is in force, and checking the result.

    `rml:baseIRI` is a property of the TRIPLES MAP, and a template
    like `"{$.fname}"` produces a relative reference that means
    nothing without it. Without resolution the term is not an IRI at
    all and the map produces no triple, which is how `RMLTC0026b`
    through `RMLTC0026d` came out empty.

    The check is RML-Core's term generation rule 2 and 3: the value, or
    the value resolved against the base IRI, must be a valid ABSOLUTE
    IRI (`rml:IRI`) or URI (`rml:URI`); otherwise the result is a DATA
    ERROR and not a missing term. `rml:UnsafeIRI` exists to produce an
    IRI that is not percent-encoded, so it keeps the weak test the RDF
    term constructor needs (a scheme and nothing else); the
    specification's own example for it is
    `<http://data.example.com/author/Zoë Krüger>`, which no IRI
    grammar accepts. An EMPTY value is no term, not an error: RML-Core
    calls a null, empty or missing value `Empty`. -/
private def mkIriE (tt : TermType) (base : Option String) (s : String)
    : Except RmlError (Option Term) :=
  if s.isEmpty then .ok none
  else
    let valid : String → Bool := match tt with
      | .uri       => isAbsoluteUri
      | .unsafeIri => isIri
      | _          => isAbsoluteIri
    let abs :=
      if valid s then s
      else match base with
        | none   => s
        | some b => L4Factoidal.Syntax.resolveIri b s
    if h : isIri abs then
      if valid abs then .ok (some (.iri ⟨abs, h⟩))
      else .error (RmlError.data "" termGenerationRules
        s!"'{s}' is not a valid absolute {if tt == .uri then "URI" else "IRI"}, with or without the base IRI")
    else .error (RmlError.data "" termGenerationRules
        s!"'{s}' is not a valid absolute {if tt == .uri then "URI" else "IRI"}, with or without the base IRI")

/-- Build a literal, honouring language then datatype. A language tag
    wins, since RDF 1.1 types every tagged literal `rdf:langString`.

    Two data errors live here, both from rule 5 of the term generation
    rules: a language tag that is not well-formed BCP 47, and a datatype
    override whose lexical form is outside the datatype's lexical space
    ("ill-typed", RML-Core, Datatype-override mapping of source values). -/
private def mkLiteralE (tm : TermMap) (lex : String) : Except RmlError Term :=
  match tm.language with
  | some tag =>
      if isWellFormedLangTag tag then .ok (.literal (Literal.langString lex tag))
      else .error (RmlError.data "" termGenerationRules
        s!"'{tag}' is not a well-formed BCP 47 language tag")
  | none =>
      match tm.datatype with
      | none => .ok (.literal (Literal.string lex))
      | some d =>
          if h : isIri d then
            let dt : WfIri := ⟨d, h⟩
            let illTyped :=
              match L4Factoidal.XSD.builtinOfIri? d with
              | some b => (L4Factoidal.XSD.lexicalMapWs b lex).isNone
              | none   => false
            if illTyped then
              .error (RmlError.data "" "RML-Core, Datatype conversions: ill-typed literal"
                s!"'{lex}' is not in the lexical space of <{d}>")
            else if h2 : (dt != rdfLangString && dt != rdfDirLangString) = true then
              .ok (.literal ⟨{ lexicalForm := lex, datatype := dt, langTag := none,
                               direction := none }, by simpa [literalWf] using h2⟩)
            else .ok (.literal (Literal.string lex))
          else .error (RmlError.data "" termGenerationRules
            s!"'{d}' is not an IRI, so it cannot be a datatype")

/-- The default term type when a map does not state one: a template
    or constant IRI position defaults to `iri`, a reference to
    `literal`. -/
def defaultTermType : TermMapForm → TermType
  | .reference _ => .literal
  | _            => .iri

/-- Generate the term a map produces from one record.

    * `.ok none`     — NO TERM: an unresolved reference, or an empty value;
    * `.ok (some t)` — the term;
    * `.error e`     — a DATA ERROR: a value from which no valid term can
      be built. The error's `site` is empty; the caller knows the
      triples map and fills it in. -/
def generateTermE (base : Option String) (tm : TermMap) (lookup : String → Option String)
    : Except RmlError (Option Term) :=
  let tt := tm.termType.getD (defaultTermType tm.form)
  let fromValue (v : String) : Except RmlError (Option Term) :=
    match tt with
    | .literal   => (mkLiteralE tm v).map some
    | .blankNode => if v.isEmpty then .ok none else .ok (some (.bnode v))
    | .uri       => mkIriE tt base v
    | .unsafeIri => mkIriE tt base v
    | .iri       => mkIriE tt base v
  match tm.form with
  | .constant t => .ok (some t)
  | .unknown    => .ok none
  | .reference f =>
      match lookup f with
      | none   => .ok none
      | some v => fromValue (if tt == .uri then encodeUriSafe v else v)
  | .template raw =>
      match expandTemplate (parseTemplate raw) tt lookup with
      | none   => .ok none
      | some v => fromValue v

/-- `generateTermE` with a data error read as NO TERM. This is the
    reading the evaluator had before data errors existed; it stays for
    callers that only want the terms, and `generateTermE` is the one to
    use when a rejected value must be reported. -/
def generateTerm (base : Option String) (tm : TermMap) (lookup : String → Option String)
    : Option Term :=
  match generateTermE base tm lookup with
  | .ok t    => t
  | .error _ => none

end L4Factoidal.RML
