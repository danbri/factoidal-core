/-
L4Factoidal.OWL.FunctionalSyntax — the OWL 2 Functional-Style Syntax
reader.

Spec: OWL 2 Web Ontology Language Structural Specification and
Functional-Style Syntax (Second Edition), https://www.w3.org/TR/owl2-syntax/
— the grammar productions of sections 2 to 10 (collected in the appendix
of the specification), `ontologyDocument` of section 3.7.

The reader produces `L4Factoidal.OWL.Struct.Ontology`. The RDF graph
comes from `L4Factoidal.OWL.StructureRdf` (OWL 2 Mapping to RDF Graphs
section 2); `parseFunctionalSyntax` composes the two. Nothing in the
reader knows about RDF.

## Grammar covered

The WHOLE grammar of the specification, not the part the test catalogs
happen to use:

    ontologyDocument := { Prefix( name = <IRI> ) } Ontology
    Ontology := 'Ontology' '(' [ ontologyIRI [ versionIRI ] ]
                { Import( IRI ) } { Annotation } { Axiom } ')'
    Axiom: Declaration, the four class axioms, the thirteen object
      property axioms, the six data property axioms, DatatypeDefinition,
      HasKey, the eight assertions, the four annotation axioms
    ClassExpression: the Class IRI and all sixteen Object*/Data*
      constructs (including n-ary DataSomeValuesFrom/DataAllValuesFrom
      and the qualified and unqualified cardinalities)
    DataRange: Datatype, DataIntersectionOf, DataUnionOf,
      DataComplementOf, DataOneOf, DatatypeRestriction
    Literal: "lex"^^Datatype, "lex"@lang, "lex"
    Individual: an IRI or a node ID _:label

An abbreviated IRI `p:local` resolves through the `Prefix` declarations.
The four prefixes `owl`, `rdf`, `rdfs` and `xsd` are implicitly
declared (Structural Specification section 3.7: "The following
prefix declarations are implicitly present in every ontology
document"); an explicit declaration of the same name replaces them.

## What is rejected

Anything outside the grammar is a clean `none`: an unknown keyword, an
unbalanced parenthesis, an undeclared prefix, an IRI that is not an IRI,
fewer operands than a production demands (`ObjectIntersectionOf` needs
two), a trailing token after the closing parenthesis. A reader that
skipped an axiom it did not understand would produce a graph missing an
axiom, and a missing axiom makes an inconsistent ontology look
consistent.

## Termination

Every recursive function takes a fuel argument and is structural on it;
each call consumes at least one token, so the fuel `2 * tokens + 8`
cannot run out on a well-formed document. Exhausted fuel is a parse
failure, never a wrong parse.
-/
import L4Factoidal.OWL.Structure
import L4Factoidal.OWL.StructureRdf

namespace L4Factoidal.OWL.FS

open L4Factoidal.RDF
open L4Factoidal.OWL.Struct

/-! ## Tokens -/

inductive Tok where
  | lp | rp | eq | caret
  /-- `<fullIRI>`, the content between the angle brackets. -/
  | iri  (s : String)
  /-- A keyword, a prefix name, an abbreviated IRI, a node ID or a number. -/
  | name (s : String)
  /-- `"quotedString"`, unescaped. -/
  | str  (s : String)
  /-- `@langTag`, without the `@`. -/
  | lang (s : String)
deriving DecidableEq, Inhabited

/-- A character of a name token: anything except white space and the
delimiters of the grammar. -/
def isNameChar (c : Char) : Bool :=
  !(c.isWhitespace || c == '(' || c == ')' || c == '"' || c == '<' || c == '>' ||
    c == '=' || c == '@' || c == '^')

def isLangChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- The longest run from `i` of characters satisfying `p`, and the index
after it. -/
def takeRun (p : Char → Bool) (cs : Array Char) (i : Nat) : String × Nat :=
  let rec go (j : Nat) (acc : List Char) (fuel : Nat) : List Char × Nat :=
    match fuel with
    | 0 => (acc.reverse, j)
    | f + 1 => match cs[j]? with
      | some c => if p c then go (j + 1) (c :: acc) f else (acc.reverse, j)
      | none   => (acc.reverse, j)
  let (r, j) := go i [] (cs.size + 1)
  (String.ofList r, j)

/-- The content of `<...>` and the index after the closing `>`. -/
def scanAngle (cs : Array Char) (start : Nat) : Option (String × Nat) :=
  let (s, j) := takeRun (fun c => c != '>') cs start
  if cs[j]? == some '>' then some (s, j + 1) else none

/-- The content of `"..."` with the two escapes the grammar allows
(`\"` and `\\`), and the index after the closing quote. -/
def scanQuoted (cs : Array Char) (start : Nat) : Option (String × Nat) :=
  let rec go (j : Nat) (acc : List Char) (fuel : Nat) : Option (String × Nat) :=
    match fuel with
    | 0 => none
    | f + 1 => match cs[j]? with
      | none => none
      | some '"' => some (String.ofList acc.reverse, j + 1)
      | some '\\' =>
          match cs[j + 1]? with
          | some '"'  => go (j + 2) ('"' :: acc) f
          | some '\\' => go (j + 2) ('\\' :: acc) f
          | _ => none
      | some c => go (j + 1) (c :: acc) f
  go start [] (cs.size + 1)

def lexGo (cs : Array Char) : Nat → Nat → Array Tok → Option (Array Tok)
  | 0, _, _ => none
  | f + 1, i, acc =>
    match cs[i]? with
    | none => some acc
    | some c =>
      if c.isWhitespace then lexGo cs f (i + 1) acc
      else if c == '(' then lexGo cs f (i + 1) (acc.push .lp)
      else if c == ')' then lexGo cs f (i + 1) (acc.push .rp)
      else if c == '=' then lexGo cs f (i + 1) (acc.push .eq)
      else if c == '^' then
        if cs[i + 1]? == some '^' then lexGo cs f (i + 2) (acc.push .caret) else none
      else if c == '<' then
        match scanAngle cs (i + 1) with
        | none => none
        | some (s, j) => lexGo cs f j (acc.push (.iri s))
      else if c == '"' then
        match scanQuoted cs (i + 1) with
        | none => none
        | some (s, j) => lexGo cs f j (acc.push (.str s))
      else if c == '@' then
        let (s, j) := takeRun isLangChar cs (i + 1)
        if s.isEmpty then none else lexGo cs f j (acc.push (.lang s))
      else if isNameChar c then
        let (s, j) := takeRun isNameChar cs i
        lexGo cs f j (acc.push (.name s))
      else none

/-- Tokenise a document. `none` on an unterminated string or IRI, a
lone `^` or `@`, or a character outside the grammar. -/
def lex (input : String) : Option (Array Tok) :=
  let cs := input.toList.toArray
  lexGo cs (cs.size + 1) 0 #[]

/-! ## Parser state and leaf productions -/

structure PS where
  toks : Array Tok
  /-- Prefix name (without the colon) to namespace. -/
  pfx  : List (String × String)

def PS.at? (ps : PS) (i : Nat) : Option Tok := ps.toks[i]?

/-- `kw(` at `i`: the index after the opening parenthesis. A keyword
never contains a colon, so it cannot be mistaken for an abbreviated
IRI. -/
def PS.kwAt (ps : PS) (i : Nat) : Option (String × Nat) :=
  match ps.toks[i]?, ps.toks[i + 1]? with
  | some (.name w), some .lp => some (w, i + 2)
  | _, _ => none

def PS.expectRp (ps : PS) (i : Nat) : Option Nat :=
  if ps.toks[i]? == some .rp then some (i + 1) else none

def PS.isRp (ps : PS) (i : Nat) : Bool := ps.toks[i]? == some .rp

def lookupPfx (ps : List (String × String)) (p : String) : Option String :=
  (ps.find? (fun (q, _) => q == p)).map (·.2)

/-- The four implicitly declared prefixes. -/
def defaultPrefixes : List (String × String) :=
  [ ("owl",  "http://www.w3.org/2002/07/owl#"),
    ("rdf",  "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
    ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
    ("xsd",  "http://www.w3.org/2001/XMLSchema#") ]

/-- A well-formed IRI from a string, or `none`. -/
def mkIri (s : String) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

/-- `IRI := fullIRI | abbreviatedIRI`. -/
def parseIri (ps : PS) (i : Nat) : Option (WfIri × Nat) :=
  match ps.toks[i]? with
  | some (.iri s) => (mkIri s).map (fun x => (x, i + 1))
  | some (.name s) =>
      match s.splitOn ":" with
      | pfx :: rest@(_ :: _) =>
          -- `p:local` with the FIRST colon splitting prefix from local
          -- part; a node ID `_:x` is not an IRI.
          if pfx == "_" then none else
          match lookupPfx ps.pfx pfx with
          | none => none
          | some ns => (mkIri (ns ++ String.intercalate ":" rest)).map (fun x => (x, i + 1))
      | _ => none
  | _ => none

/-- Does an IRI start at `i` (as opposed to a keyword or a number)? -/
def PS.iriLike (ps : PS) (i : Nat) : Bool :=
  match ps.toks[i]? with
  | some (.iri _) => true
  | some (.name s) => s.contains ':' && !s.startsWith "_:"
  | _ => false

def parseNat (ps : PS) (i : Nat) : Option (Nat × Nat) :=
  match ps.toks[i]? with
  | some (.name s) =>
      if !s.isEmpty && s.all Char.isDigit then some (s.toNat!, i + 1) else none
  | _ => none

/-- `nodeID`: `_:label`. -/
def parseNodeId (ps : PS) (i : Nat) : Option (String × Nat) :=
  match ps.toks[i]? with
  | some (.name s) =>
      if s.startsWith "_:" && s.length > 2 then some ((s.drop 2).toString, i + 1) else none
  | _ => none

def parseIndividual (ps : PS) (i : Nat) : Option (Individual × Nat) :=
  match parseIri ps i with
  | some (x, j) => some (.named x, j)
  | none => (parseNodeId ps i).map (fun (l, j) => (.anon l, j))

def mkLiteral (lex : String) (dt : WfIri) (tag : Option String) : Option WfLiteral :=
  let l : Literal := { lexicalForm := lex, datatype := dt, langTag := tag, direction := none }
  Literal.toWf? l

/-- `Literal := typedLiteral | stringLiteralNoLanguage |
stringLiteralWithLanguage`. -/
def parseLiteral (ps : PS) (i : Nat) : Option (WfLiteral × Nat) :=
  match ps.toks[i]? with
  | some (.str lex) =>
      match ps.toks[i + 1]? with
      | some .caret =>
          match parseIri ps (i + 2) with
          | none => none
          | some (dt, j) => (mkLiteral lex dt none).map (fun l => (l, j))
      | some (.lang tag) => some (Literal.langString lex tag, i + 2)
      | _ => some (Literal.string lex, i + 1)
  | _ => none

/-- `AnnotationValue := AnonymousIndividual | IRI | Literal`. -/
def parseAnnValue (ps : PS) (i : Nat) : Option (AnnValue × Nat) :=
  match parseIri ps i with
  | some (x, j) => some (.iri x, j)
  | none =>
    match parseNodeId ps i with
    | some (l, j) => some (.anon l, j)
    | none => (parseLiteral ps i).map (fun (l, j) => (.lit l, j))

/-- `ObjectPropertyExpression := ObjectProperty | InverseObjectProperty`. -/
def parseOPE (ps : PS) (i : Nat) : Option (ObjPropExpr × Nat) :=
  match parseIri ps i with
  | some (p, j) => some (.prop p, j)
  | none =>
    match ps.kwAt i with
    | some ("ObjectInverseOf", k) =>
        match parseIri ps k with
        | none => none
        | some (p, j) => (ps.expectRp j).map (fun e => (.inverse p, e))
    | _ => none

/-- Zero or more `ObjectPropertyExpression`s, up to the next `)`. -/
def parseOPEs (ps : PS) : Nat → Nat → List ObjPropExpr → Option (List ObjPropExpr × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseOPE ps i with
      | none => none
      | some (o, j) => parseOPEs ps f j (o :: acc)

/-- Zero or more IRIs, up to the next `)`. -/
def parseIris (ps : PS) : Nat → Nat → List WfIri → Option (List WfIri × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseIri ps i with
      | none => none
      | some (x, j) => parseIris ps f j (x :: acc)

def parseIndividuals (ps : PS) : Nat → Nat → List Individual →
    Option (List Individual × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseIndividual ps i with
      | none => none
      | some (a, j) => parseIndividuals ps f j (a :: acc)

def parseLiterals (ps : PS) : Nat → Nat → List WfLiteral → Option (List WfLiteral × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseLiteral ps i with
      | none => none
      | some (l, j) => parseLiterals ps f j (l :: acc)

/-- `(constrainingFacet restrictionValue)+`, up to the next `)`. -/
def parseFacets (ps : PS) : Nat → Nat → List (WfIri × WfLiteral) →
    Option (List (WfIri × WfLiteral) × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseIri ps i with
      | none => none
      | some (facet, j) =>
        match parseLiteral ps j with
        | none => none
        | some (v, k) => parseFacets ps f k ((facet, v) :: acc)

/-! ## Data ranges, class expressions and annotations (mutually recursive) -/

-- Data ranges, class expressions and annotations recurse into one another.
mutual

def parseDR (ps : PS) : Nat → Nat → Option (DataRange × Nat)
  | 0, _ => none
  | f + 1, i =>
    match parseIri ps i with
    | some (dt, j) => some (.datatype dt, j)
    | none =>
      match ps.kwAt i with
      | some ("DataIntersectionOf", k) =>
          match parseDRs ps f k [] with
          | some (drs, j) =>
              if drs.length < 2 then none
              else (ps.expectRp j).map (fun e => (.intersection drs, e))
          | none => none
      | some ("DataUnionOf", k) =>
          match parseDRs ps f k [] with
          | some (drs, j) =>
              if drs.length < 2 then none
              else (ps.expectRp j).map (fun e => (.union drs, e))
          | none => none
      | some ("DataComplementOf", k) =>
          match parseDR ps f k with
          | some (d, j) => (ps.expectRp j).map (fun e => (.complement d, e))
          | none => none
      | some ("DataOneOf", k) =>
          match parseLiterals ps (ps.toks.size + 1) k [] with
          | some (lits, j) =>
              if lits.isEmpty then none
              else (ps.expectRp j).map (fun e => (.oneOf lits, e))
          | none => none
      | some ("DatatypeRestriction", k) =>
          match parseIri ps k with
          | none => none
          | some (dt, j) =>
            match parseFacets ps (ps.toks.size + 1) j [] with
            | some (fs, j2) =>
                if fs.isEmpty then none
                else (ps.expectRp j2).map (fun e => (.restriction dt fs, e))
            | none => none
      | _ => none

def parseDRs (ps : PS) : Nat → Nat → List DataRange → Option (List DataRange × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseDR ps f i with
      | none => none
      | some (d, j) => parseDRs ps f j (d :: acc)

def parseCE (ps : PS) : Nat → Nat → Option (ClassExpr × Nat)
  | 0, _ => none
  | f + 1, i =>
    match parseIri ps i with
    | some (c, j) => some (.cls c, j)
    | none =>
      match ps.kwAt i with
      | some (w, k) => parseCEBody ps f w k
      | none => none

/-- The constructs `Keyword( ... )`, after the opening parenthesis. -/
def parseCEBody (ps : PS) : Nat → String → Nat → Option (ClassExpr × Nat)
  | 0, _, _ => none
  | f + 1, w, k =>
    if w == "ObjectIntersectionOf" || w == "ObjectUnionOf" then
      match parseCEs ps f k [] with
      | some (ces, j) =>
          if ces.length < 2 then none
          else (ps.expectRp j).map (fun e =>
                 ((if w == "ObjectUnionOf" then ClassExpr.union ces
                   else ClassExpr.intersection ces), e))
      | none => none
    else if w == "ObjectComplementOf" then
      match parseCE ps f k with
      | some (c, j) => (ps.expectRp j).map (fun e => (.complement c, e))
      | none => none
    else if w == "ObjectOneOf" then
      match parseIndividuals ps (ps.toks.size + 1) k [] with
      | some (inds, j) =>
          if inds.isEmpty then none
          else (ps.expectRp j).map (fun e => (.oneOf inds, e))
      | none => none
    else if w == "ObjectSomeValuesFrom" || w == "ObjectAllValuesFrom" then
      match parseOPE ps k with
      | none => none
      | some (o, j) =>
        match parseCE ps f j with
        | none => none
        | some (c, j2) =>
            (ps.expectRp j2).map (fun e =>
              ((if w == "ObjectSomeValuesFrom" then ClassExpr.someValuesFrom o c
                else ClassExpr.allValuesFrom o c), e))
    else if w == "ObjectHasValue" then
      match parseOPE ps k with
      | none => none
      | some (o, j) =>
        match parseIndividual ps j with
        | none => none
        | some (a, j2) => (ps.expectRp j2).map (fun e => (.hasValue o a, e))
    else if w == "ObjectHasSelf" then
      match parseOPE ps k with
      | none => none
      | some (o, j) => (ps.expectRp j).map (fun e => (.hasSelf o, e))
    else if w == "ObjectMinCardinality" || w == "ObjectMaxCardinality" ||
            w == "ObjectExactCardinality" then
      match parseNat ps k with
      | none => none
      | some (n, j) =>
        match parseOPE ps j with
        | none => none
        | some (o, j2) =>
          let build : Option ClassExpr → ClassExpr := fun q =>
            if w == "ObjectMinCardinality" then ClassExpr.minCard n o q
            else if w == "ObjectMaxCardinality" then ClassExpr.maxCard n o q
            else ClassExpr.exactCard n o q
          if ps.isRp j2 then some (build none, j2 + 1)
          else match parseCE ps f j2 with
            | none => none
            | some (c, j3) => (ps.expectRp j3).map (fun e => (build (some c), e))
    else if w == "DataSomeValuesFrom" || w == "DataAllValuesFrom" then
      -- `DPE { DPE } DR`: parse every item as a data range; all but the
      -- last must be plain IRIs (property names).
      match parseDRs ps f k [] with
      | none => none
      | some (items, j) =>
        match items.reverse with
        | [] => none
        | dr :: revProps =>
          let props := revProps.reverse.filterMap (fun d => match d with
            | .datatype p => some p | _ => none)
          if props.length != revProps.length || props.isEmpty then none
          else (ps.expectRp j).map (fun e =>
            ((if w == "DataSomeValuesFrom" then ClassExpr.dataSomeValuesFrom props dr
              else ClassExpr.dataAllValuesFrom props dr), e))
    else if w == "DataHasValue" then
      match parseIri ps k with
      | none => none
      | some (p, j) =>
        match parseLiteral ps j with
        | none => none
        | some (l, j2) => (ps.expectRp j2).map (fun e => (.dataHasValue p l, e))
    else if w == "DataMinCardinality" || w == "DataMaxCardinality" ||
            w == "DataExactCardinality" then
      match parseNat ps k with
      | none => none
      | some (n, j) =>
        match parseIri ps j with
        | none => none
        | some (p, j2) =>
          let build : Option DataRange → ClassExpr := fun q =>
            if w == "DataMinCardinality" then ClassExpr.dataMinCard n p q
            else if w == "DataMaxCardinality" then ClassExpr.dataMaxCard n p q
            else ClassExpr.dataExactCard n p q
          if ps.isRp j2 then some (build none, j2 + 1)
          else match parseDR ps f j2 with
            | none => none
            | some (d, j3) => (ps.expectRp j3).map (fun e => (build (some d), e))
    else none

def parseCEs (ps : PS) : Nat → Nat → List ClassExpr → Option (List ClassExpr × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseCE ps f i with
      | none => none
      | some (c, j) => parseCEs ps f j (c :: acc)

/-- Zero or more `Annotation( ... )` starting at `i`. -/
def parseAnns (ps : PS) : Nat → Nat → List Annotation → Option (List Annotation × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    match ps.kwAt i with
    | some ("Annotation", k) =>
        match parseAnnotationBody ps f k with
        | none => none
        | some (a, j) => parseAnns ps f j (a :: acc)
    | _ => some (acc.reverse, i)

/-- `annotationAnnotations AP av )`, after `Annotation(`. -/
def parseAnnotationBody (ps : PS) : Nat → Nat → Option (Annotation × Nat)
  | 0, _ => none
  | f + 1, k =>
    match parseAnns ps f k [] with
    | none => none
    | some (inner, j) =>
      match parseIri ps j with
      | none => none
      | some (ap, j2) =>
        match parseAnnValue ps j2 with
        | none => none
        | some (v, j3) => (ps.expectRp j3).map (fun e => (.mk inner ap v, e))

end

/-! ## Axioms -/

/-- A fuel large enough for any document: each call consumes a token. -/
def fuelFor (ps : PS) : Nat := 2 * ps.toks.size + 8

/-- Two or more class expressions up to `)`; returns the list. -/
def parseCEsAtLeast (ps : PS) (n : Nat) (i : Nat) : Option (List ClassExpr × Nat) :=
  match parseCEs ps (fuelFor ps) i [] with
  | some (ces, j) => if ces.length < n then none else some (ces, j)
  | none => none

def parseOPEsAtLeast (ps : PS) (n : Nat) (i : Nat) : Option (List ObjPropExpr × Nat) :=
  match parseOPEs ps (fuelFor ps) i [] with
  | some (os, j) => if os.length < n then none else some (os, j)
  | none => none

def parseIrisAtLeast (ps : PS) (n : Nat) (i : Nat) : Option (List WfIri × Nat) :=
  match parseIris ps (fuelFor ps) i [] with
  | some (xs, j) => if xs.length < n then none else some (xs, j)
  | none => none

def parseIndividualsAtLeast (ps : PS) (n : Nat) (i : Nat) : Option (List Individual × Nat) :=
  match parseIndividuals ps (fuelFor ps) i [] with
  | some (xs, j) => if xs.length < n then none else some (xs, j)
  | none => none

/-- Parse `IRI IRI )` and build. -/
def twoIris (ps : PS) (k : Nat) : Option (WfIri × WfIri × Nat) :=
  match parseIri ps k with
  | none => none
  | some (a, j) =>
    match parseIri ps j with
    | none => none
    | some (b, j2) => (ps.expectRp j2).map (fun e => (a, b, e))

def objPropCharOf : String → Option ObjPropChar
  | "FunctionalObjectProperty"        => some .functional
  | "InverseFunctionalObjectProperty" => some .inverseFunctional
  | "ReflexiveObjectProperty"         => some .reflexive
  | "IrreflexiveObjectProperty"       => some .irreflexive
  | "SymmetricObjectProperty"         => some .symmetric
  | "AsymmetricObjectProperty"        => some .asymmetric
  | "TransitiveObjectProperty"        => some .transitive
  | _ => none

/-- `Entity := 'Class' '(' Class ')' | ...` of a declaration. -/
def entityKindOf : String → Option EntityKind
  | "Class"              => some .cls
  | "Datatype"           => some .datatype
  | "ObjectProperty"     => some .objectProperty
  | "DataProperty"       => some .dataProperty
  | "AnnotationProperty" => some .annotationProperty
  | "NamedIndividual"    => some .namedIndividual
  | _ => none

/-- The body of the axiom `w( ... )`, after the opening parenthesis and
with the axiom annotations already read. -/
def parseAxiomBody (ps : PS) (w : String) (anns : List Annotation) (k : Nat) :
    Option (Axiom × Nat) :=
  let f := fuelFor ps
  match w with
  | "Declaration" =>
      match ps.kwAt k with
      | some (ek, k2) =>
        match entityKindOf ek, parseIri ps k2 with
        | some kind, some (x, j) =>
          match ps.expectRp j with
          | some j2 => (ps.expectRp j2).map (fun e => (.declaration anns kind x, e))
          | none => none
        | _, _ => none
      | none => none
  | "SubClassOf" =>
      match parseCE ps f k with
      | none => none
      | some (a, j) =>
        match parseCE ps f j with
        | none => none
        | some (b, j2) => (ps.expectRp j2).map (fun e => (.subClassOf anns a b, e))
  | "EquivalentClasses" =>
      (parseCEsAtLeast ps 2 k).bind (fun (ces, j) =>
        (ps.expectRp j).map (fun e => (.equivalentClasses anns ces, e)))
  | "DisjointClasses" =>
      (parseCEsAtLeast ps 2 k).bind (fun (ces, j) =>
        (ps.expectRp j).map (fun e => (.disjointClasses anns ces, e)))
  | "DisjointUnion" =>
      match parseIri ps k with
      | none => none
      | some (c, j) =>
        (parseCEsAtLeast ps 2 j).bind (fun (ces, j2) =>
          (ps.expectRp j2).map (fun e => (.disjointUnion anns c ces, e)))
  | "SubObjectPropertyOf" =>
      let sub : Option (SubObjProp × Nat) :=
        match ps.kwAt k with
        | some ("ObjectPropertyChain", k2) =>
            (parseOPEsAtLeast ps 2 k2).bind (fun (os, j) =>
              (ps.expectRp j).map (fun e => (SubObjProp.chain os, e)))
        | _ => (parseOPE ps k).map (fun (o, j) => (SubObjProp.single o, j))
      match sub with
      | none => none
      | some (s, j) =>
        match parseOPE ps j with
        | none => none
        | some (sup, j2) => (ps.expectRp j2).map (fun e => (.subObjectPropertyOf anns s sup, e))
  | "EquivalentObjectProperties" =>
      (parseOPEsAtLeast ps 2 k).bind (fun (os, j) =>
        (ps.expectRp j).map (fun e => (.equivalentObjectProperties anns os, e)))
  | "DisjointObjectProperties" =>
      (parseOPEsAtLeast ps 2 k).bind (fun (os, j) =>
        (ps.expectRp j).map (fun e => (.disjointObjectProperties anns os, e)))
  | "InverseObjectProperties" =>
      match parseOPE ps k with
      | none => none
      | some (a, j) =>
        match parseOPE ps j with
        | none => none
        | some (b, j2) => (ps.expectRp j2).map (fun e => (.inverseObjectProperties anns a b, e))
  | "ObjectPropertyDomain" =>
      match parseOPE ps k with
      | none => none
      | some (o, j) =>
        match parseCE ps f j with
        | none => none
        | some (c, j2) => (ps.expectRp j2).map (fun e => (.objectPropertyDomain anns o c, e))
  | "ObjectPropertyRange" =>
      match parseOPE ps k with
      | none => none
      | some (o, j) =>
        match parseCE ps f j with
        | none => none
        | some (c, j2) => (ps.expectRp j2).map (fun e => (.objectPropertyRange anns o c, e))
  | "SubDataPropertyOf" =>
      (twoIris ps k).map (fun (a, b, e) => (.subDataPropertyOf anns a b, e))
  | "EquivalentDataProperties" =>
      (parseIrisAtLeast ps 2 k).bind (fun (xs, j) =>
        (ps.expectRp j).map (fun e => (.equivalentDataProperties anns xs, e)))
  | "DisjointDataProperties" =>
      (parseIrisAtLeast ps 2 k).bind (fun (xs, j) =>
        (ps.expectRp j).map (fun e => (.disjointDataProperties anns xs, e)))
  | "DataPropertyDomain" =>
      match parseIri ps k with
      | none => none
      | some (p, j) =>
        match parseCE ps f j with
        | none => none
        | some (c, j2) => (ps.expectRp j2).map (fun e => (.dataPropertyDomain anns p c, e))
  | "DataPropertyRange" =>
      match parseIri ps k with
      | none => none
      | some (p, j) =>
        match parseDR ps f j with
        | none => none
        | some (d, j2) => (ps.expectRp j2).map (fun e => (.dataPropertyRange anns p d, e))
  | "FunctionalDataProperty" =>
      match parseIri ps k with
      | none => none
      | some (p, j) => (ps.expectRp j).map (fun e => (.functionalDataProperty anns p, e))
  | "DatatypeDefinition" =>
      match parseIri ps k with
      | none => none
      | some (dt, j) =>
        match parseDR ps f j with
        | none => none
        | some (d, j2) => (ps.expectRp j2).map (fun e => (.datatypeDefinition anns dt d, e))
  | "HasKey" =>
      match parseCE ps f k with
      | none => none
      | some (c, j) =>
        if ps.toks[j]? != some .lp then none else
        match parseOPEs ps f (j + 1) [] with
        | none => none
        | some (os, j2) =>
          match ps.expectRp j2 with
          | none => none
          | some j3 =>
            if ps.toks[j3]? != some .lp then none else
            match parseIris ps f (j3 + 1) [] with
            | none => none
            | some (dps, j4) =>
              match ps.expectRp j4 with
              | none => none
              | some j5 => (ps.expectRp j5).map (fun e => (.hasKey anns c os dps, e))
  | "SameIndividual" =>
      (parseIndividualsAtLeast ps 2 k).bind (fun (xs, j) =>
        (ps.expectRp j).map (fun e => (.sameIndividual anns xs, e)))
  | "DifferentIndividuals" =>
      (parseIndividualsAtLeast ps 2 k).bind (fun (xs, j) =>
        (ps.expectRp j).map (fun e => (.differentIndividuals anns xs, e)))
  | "ClassAssertion" =>
      match parseCE ps f k with
      | none => none
      | some (c, j) =>
        match parseIndividual ps j with
        | none => none
        | some (a, j2) => (ps.expectRp j2).map (fun e => (.classAssertion anns c a, e))
  | "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" =>
      match parseOPE ps k with
      | none => none
      | some (o, j) =>
        match parseIndividual ps j with
        | none => none
        | some (a, j2) =>
          match parseIndividual ps j2 with
          | none => none
          | some (b, j3) =>
            (ps.expectRp j3).map (fun e =>
              ((if w == "ObjectPropertyAssertion" then Axiom.objectPropertyAssertion anns o a b
                else Axiom.negativeObjectPropertyAssertion anns o a b), e))
  | "DataPropertyAssertion" | "NegativeDataPropertyAssertion" =>
      match parseIri ps k with
      | none => none
      | some (p, j) =>
        match parseIndividual ps j with
        | none => none
        | some (a, j2) =>
          match parseLiteral ps j2 with
          | none => none
          | some (l, j3) =>
            (ps.expectRp j3).map (fun e =>
              ((if w == "DataPropertyAssertion" then Axiom.dataPropertyAssertion anns p a l
                else Axiom.negativeDataPropertyAssertion anns p a l), e))
  | "AnnotationAssertion" =>
      match parseIri ps k with
      | none => none
      | some (ap, j) =>
        match parseIndividual ps j with
        | none => none
        | some (s, j2) =>
          match parseAnnValue ps j2 with
          | none => none
          | some (v, j3) => (ps.expectRp j3).map (fun e => (.annotationAssertion anns ap s v, e))
  | "SubAnnotationPropertyOf" =>
      (twoIris ps k).map (fun (a, b, e) => (.subAnnotationPropertyOf anns a b, e))
  | "AnnotationPropertyDomain" =>
      (twoIris ps k).map (fun (a, b, e) => (.annotationPropertyDomain anns a b, e))
  | "AnnotationPropertyRange" =>
      (twoIris ps k).map (fun (a, b, e) => (.annotationPropertyRange anns a b, e))
  | _ =>
      match objPropCharOf w with
      | some ch =>
        match parseOPE ps k with
        | none => none
        | some (o, j) => (ps.expectRp j).map (fun e => (.objectPropertyCharacteristic anns ch o, e))
      | none => none

/-- One axiom at `i`. -/
def parseAxiom (ps : PS) (i : Nat) : Option (Axiom × Nat) :=
  match ps.kwAt i with
  | none => none
  | some (w, k) =>
    match parseAnns ps (fuelFor ps) k [] with
    | none => none
    | some (anns, k2) => parseAxiomBody ps w anns k2

/-- Axioms up to the closing `)` of the ontology. -/
def parseAxioms (ps : PS) : Nat → Nat → List Axiom → Option (List Axiom × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    if ps.isRp i then some (acc.reverse, i)
    else match parseAxiom ps i with
      | none => none
      | some (a, j) => parseAxioms ps f j (a :: acc)

/-! ## The document -/

/-- `Prefix( name = <IRI> )` declarations. -/
def parsePrefixes (toks : Array Tok) : Nat → Nat → List (String × String) →
    Option (List (String × String) × Nat)
  | 0, _, _ => none
  | f + 1, i, acc =>
    match toks[i]?, toks[i + 1]?, toks[i + 2]?, toks[i + 3]?, toks[i + 4]?, toks[i + 5]? with
    | some (.name "Prefix"), some .lp, some (.name pn), some .eq, some (.iri ns), some .rp =>
        if pn.endsWith ":" then
          parsePrefixes toks f (i + 6) (((pn.dropEnd 1).toString, ns) :: acc)
        else none
    | some (.name "Prefix"), _, _, _, _, _ => none
    | _, _, _, _, _, _ => some (acc.reverse, i)

/-- An optional IRI: absent when the next token is not IRI-like; a
failure when it is IRI-like but does not resolve (an undeclared
prefix must not be skipped silently). -/
def parseOptIri (ps : PS) (i : Nat) : Option (Option WfIri × Nat) :=
  if ps.iriLike i then
    match parseIri ps i with
    | some (x, j) => some (some x, j)
    | none => none
  else some (none, i)

/-- `{ Import( IRI ) }`. -/
def parseImports (ps : PS) : Nat → Nat → List WfIri → Option (List WfIri × Nat)
  | 0, _, _ => none
  | f + 1, j, acc =>
    match ps.kwAt j with
    | some ("Import", jj) =>
        match parseIri ps jj with
        | none => none
        | some (x, j2) =>
          match ps.expectRp j2 with
          | none => none
          | some j3 => parseImports ps f j3 (x :: acc)
    | _ => some (acc.reverse, j)

/-- Read a whole functional-style syntax document. -/
def parseOntology (input : String) : Option Ontology := do
  let toks ← lex input
  let (declared, i0) ← parsePrefixes toks (toks.size + 1) 0 []
  let ps : PS := { toks := toks, pfx := declared ++ defaultPrefixes }
  let some ("Ontology", k) := ps.kwAt i0 | none
  let (iri, k1) ← parseOptIri ps k
  let (ver, k2) ← (if iri.isSome then parseOptIri ps k1 else some (none, k1))
  let (imps, k3) ← parseImports ps (toks.size + 1) k2 []
  let (anns, k4) ← parseAnns ps (fuelFor ps) k3 []
  let (axs, k5) ← parseAxioms ps (toks.size + 1) k4 []
  let k6 ← ps.expectRp k5
  if k6 == toks.size then
    some { iri := iri, versionIri := ver, imports := imps, annotations := anns, axioms := axs }
  else none

/-- A functional-style syntax document as RDF triples: the reader
followed by the OWL 2 Mapping to RDF Graphs. `none` for anything the
grammar does not accept. -/
def parseFunctionalSyntax (input : String) : Option (List Triple) :=
  (parseOntology input).map Ontology.toGraph

end L4Factoidal.OWL.FS
