/-
L4Factoidal.N3.Parser — the Notation3 reader.

Specification: Notation3 Language § "Grammar" (W3C N3 Community Group,
editor's draft at commit `1d29dea7` of https://github.com/w3c/N3; the EBNF
of the dated report `reports/20230703/n3.ebnf`, productions [1]-[36], which
is the ANTLR grammar `grammar/n3.g4`). Design record:
`docs/designissues/2026-10-28-n3.md`. Tracking:
https://github.com/danbri/factoidal/issues/1165.

## Reuse of the Turtle reader

Notation3 Language § "Relationship to Other Languages": "N3 is a superset of
Turtle". Every terminal of the N3 grammar is a Turtle terminal, so this
reader calls the Turtle reader's functions for all of them
(`Syntax/Turtle.lean`): white space and comments (`tws`), IRIs with base
resolution and prefixed names (`readTurtleIri`), blank node labels
(`readTurtleBnode`), string literals with language tags and datatypes
(`readRdfLiteral`), numeric and boolean literals (`readAnyLiteral`), the
directive keywords and the namespace token (`matchKeyword`, `readPnameNs`,
`readIriRef`), and the parser state with its prefix map, base IRI and
blank-node prefix (`TurtleState`). What this module adds is the N3 grammar
above the terminals:

* [9] `triples ::= subject predicateObjectList?` (a subject may stand alone);
* [12] verbs `has e`, `is e of`, `<- e` (inverse), `=` (`owl:sameAs`),
  `=>` (`log:implies`), `<=` (`log:isImpliedBy`), and `a`;
* [17] paths `e!p` and `e^p`, left to right: each step introduces a fresh
  blank node `b` with the triple `e p b` (`!`) or `b p e` (`^`);
* [18] any term in any position: literals as subjects and predicates, quick
  variables `?x`, lists `( ... )` as terms, graph terms `{ ... }`;
* [21] IRI property lists `[ id <iri> ... ]`;
* [24] statements inside a graph term, the last one without `.`; directives
  inside a graph term.

Kept from the Turtle reader, so that a Turtle document reads the same: a
document is a sequence of statements each ended by `.` ([1]); `@prefix` and
`@base` end with `.`, `PREFIX` and `BASE` do not; `a` is a keyword only when
a name cannot continue (`kwFollows`). Not accepted, as the report removed
them (§ "Changes since the Team Submission"): `@forAll`, `@forSome`,
`@keywords`, and `@a`, `@is`, `@of`, `@has`, `@true`, `@false`.

## Blank-node scope

A `_:x` at the top level keeps its label, as in the Turtle reader. A `_:x`
inside a graph term gets the label `<prefix>f<k>.x`, where `k` numbers the
graph term in document order and `<prefix>` is the document's generated-label
prefix (`TurtleState.bnodePrefix`, which no label of the document begins
with). So two graph terms never share a blank node, and no graph term shares
one with the document (Notation3 Semantics § "Abstract syntax", the
community-group consensus on nested blank nodes).

## Termination and stack

One `mutual` block, well-founded on a fuel argument seeded from the input
length (`parseN3`). Every sequence (statements, `;` and `,` lists, list
members, path steps) is a self tail call. Every nesting step (`{`, `(`, `[`)
increases a depth argument, and a depth above `maxNesting` is an error, so
the native stack depth is bounded by a constant. No `partial def`.
-/
import L4Factoidal.N3.Syntax
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.N3

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- The deepest nesting of `{ }`, `( )` and `[ ]` a document may have. The
suite's `cwm_syntax/too-nested.n3` nests about 1,100 graph terms; a level
takes four native frames of this block, and the wasm build has an 8 MB stack
(`Wasm/build-wasm.sh`). -/
def maxNesting : Nat := 2048

/-- Reader state: the Turtle reader's state (prefixes, base, generated
blank-node counter and prefix, RDF 1.1/1.2 mode), the graph term being read
(`scope`, 0 for the document) and the next graph-term number, and the
triples read so far into the current graph. -/
structure N3State where
  ts        : TurtleState
  scope     : Nat := 0
  nextScope : Nat := 1
  out       : Array N3Triple := #[]

/-- A fresh blank node, from the Turtle reader's counter. -/
def N3State.fresh (st : N3State) : N3Term × N3State :=
  let (b, ts') := st.ts.freshBnode
  (.bnode b, { st with ts := ts' })

def N3State.emit (st : N3State) (t : N3Triple) : N3State := { st with out := st.out.push t }

/-- The label for a written `_:label` in the current scope (module header). -/
def N3State.scopedLabel (st : N3State) (label : String) : String :=
  if st.scope == 0 then label
  else st.ts.bnodePrefix ++ "f" ++ toString st.scope ++ "." ++ label

/-- The term for a written `_:label` in the current scope. -/
def N3State.userBnode (st : N3State) (label : String) : N3Term :=
  .bnode (st.scopedLabel label)

/-- An RDF term the Turtle reader gave, with its written labels scoped (a
generated label, which begins with the generated-label prefix, stays). -/
def N3State.scopeRdf (st : N3State) (t : Term) : Term :=
  if st.scope == 0 then t
  else t.renameBnodes fun b => if b.startsWith st.ts.bnodePrefix then b else st.scopedLabel b

def N3State.scopeRdfSubject (st : N3State) (s : Subject) : Subject :=
  if st.scope == 0 then s
  else s.renameBnodes fun b => if b.startsWith st.ts.bnodePrefix then b else st.scopedLabel b

/-- The RDF triples the Turtle reader gave, scoped, added to the current graph. -/
def N3State.emitRdf (st : N3State) (ts : List Triple) : N3State :=
  ts.foldl (fun acc t =>
    acc.emit (ofRdfSubject (st.scopeRdfSubject t.s), .iri t.p, ofRdfTerm (st.scopeRdf t.o))) st

/-- The parts of an asserted N3 triple as an RDF triple, for an RDF 1.2
annotation: an IRI or blank-node subject, an IRI predicate, an RDF object. -/
def rdfParts : N3Triple → Option (Subject × WfIri × Term)
  | (s, .iri p, o) =>
      let s' : Option Subject := match s with
        | .iri i => some (.iri i) | .bnode b => some (.bnode b) | _ => none
      let o' : Option Term := match o with
        | .iri i => some (.iri i) | .bnode b => some (.bnode b) | .lit l => some (.literal l)
        | .triple a b c => some (.tripleTerm a b c) | _ => none
      match s', o' with
      | some s1, some o1 => some (s1, p, o1)
      | _, _ => none
  | _ => none

/-- A production's result: the value, the state, the position and the rest of
the input. -/
abbrev R (α : Type) := Except ParseError (α × N3State × Nat × List Char)

/-- After a bare keyword, no name continues (the longest-match rule of Turtle
section 6.5, as `readBooleanLiteral` applies it to `true` and `false`). -/
def kwFollows (rest : List Char) : Bool := !(pnCharsFollows rest || pnameNsFollows rest)

/-- A bare word keyword (`a`, `has`, `is`, `of`, `id`) at the head of `cs`:
the rest after it. -/
def keyword (kw : List Char) (cs : List Char) : Option (List Char) :=
  match matchKeyword false kw cs with
  | some rest => if kwFollows rest then some rest else none
  | none => none

#guard (keyword "is".toList "is :p of".toList).isSome
#guard (keyword "is".toList "isA :p".toList).isNone
#guard (keyword "is".toList "is:p".toList).isNone
#guard (keyword "a".toList "a<x>".toList).isSome

/-- [36] `QUICK_VAR_NAME ::= "?" PN_LOCAL`: the name after `?`. -/
def readQuickVar (pos : Nat) (cs : List Char) : Except ParseError (String × Nat × List Char) :=
  match cs with
  | '?' :: rest =>
      let (body, r) := scanNameBody rest
      let (loc, dots) := trimTrailingDots body
      if loc.isEmpty || !validatePnLocal loc true then .error ⟨"invalid quick variable name", pos⟩
      else .ok (String.ofList loc, pos + 1 + loc.length, dots ++ r)
  | _ => .error ⟨"expected quick variable", pos⟩

#guard (readQuickVar 0 "?x :p".toList).toOption.map (·.1) == some "x"
#guard (readQuickVar 0 "?x.".toList).toOption.map (·.1) == some "x"
#guard (readQuickVar 0 "? x".toList).toOption.isNone

/-- What a directive does. -/
inductive Directive where
  | prefix (pfx iri : String)
  | base (iri : String)
  | version

/-- [3] `n3Directive` (`@prefix`, `@base`: `atForm` true, the `.` after it is
read by the statement) and [4] `sparqlDirective` (`PREFIX`, `BASE`, no `.`),
and under RDF 1.2 the Turtle 1.2 `VERSION` directive. The pieces are the
Turtle reader's (`readPrefixDirective`, `readBaseDirective`), without their
`.`, which in N3 the statement reads ([1], [24]). -/
def readDirective (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError ((Directive × Bool) × Nat × List Char) :=
  let pfxBody (atForm : Bool) (kwLen : Nat) (rest : List Char) :
      Except ParseError ((Directive × Bool) × Nat × List Char) :=
    let (p1, r1) := tws (pos + kwLen) rest
    match readPnameNs p1 r1 with
    | .error e => .error e
    | .ok (ns, p2, r2) =>
        let (p3, r3) := tws p2 r2
        match readIriRef p3 r3 with
        | .error e => .error e
        | .ok (raw, p4, r4) =>
            if !isIriReferenceFast raw then .error (notIriReference p3 raw)
            else .ok ((.prefix ns (st.resolve raw), atForm), p4, r4)
  let baseBody (atForm : Bool) (kwLen : Nat) (rest : List Char) :
      Except ParseError ((Directive × Bool) × Nat × List Char) :=
    let (p1, r1) := tws (pos + kwLen) rest
    match readIriRef p1 r1 with
    | .error e => .error e
    | .ok (raw, p2, r2) =>
        if !isIriReferenceFast raw then .error (notIriReference p1 raw)
        else .ok ((.base (st.resolve raw), atForm), p2, r2)
  match matchKeyword false "@prefix".toList cs with
  | some rest => pfxBody true 7 rest
  | none =>
  match matchKeyword true "PREFIX".toList cs with
  | some rest => pfxBody false 6 rest
  | none =>
  match matchKeyword false "@base".toList cs with
  | some rest => baseBody true 5 rest
  | none =>
  match matchKeyword true "BASE".toList cs with
  | some rest => baseBody false 4 rest
  | none =>
    if st.mode == .rdf12 then
      match readVersionDirective pos cs with
      | .ok (p, r) => .ok ((.version, false), p, r)
      | .error e => .error e
    else .error ⟨"not a directive", pos⟩

/-- Apply a directive to the state. -/
def applyDirective (st : N3State) : Directive → N3State
  | .prefix pfx iri => { st with ts := st.ts.bindPrefix pfx iri }
  | .base iri => { st with ts := { st.ts with baseIri := iri } }
  | .version => st

/-- A verb: the predicate term and whether subject and object swap
(`is e of`, `<- e`, `<=` is not swapped: it is the predicate
`log:isImpliedBy`). -/
abbrev Verb := N3Term × Bool

/-- A character that ends a predicate-object list after `;` (Turtle [7], N3
[10]: `(';' (verb objectList)?)*`). -/
def endsPOL (c : Char) : Bool := c == '.' || c == ']' || c == '}'

mutual

/-- [18] `pathItem`. -/
def readPathItem (fuel depth : Nat) (st : N3State) (pos : Nat) (cs : List Char) : R N3Term :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 term", pos⟩
  | f + 1 =>
    match cs with
    | [] => .error ⟨"expected a term", pos⟩
    | '{' :: rest =>
        if depth + 1 > maxNesting then .error ⟨s!"N3 nesting deeper than {maxNesting}", pos⟩
        else
          let sc := st.nextScope
          let inner : N3State := { st with scope := sc, nextScope := sc + 1, out := #[] }
          match readFormulaContent f (depth + 1) inner (pos + 1) rest with
          | .error e => .error e
          | .ok ((), st1, p1, r1) =>
              .ok (.graph st1.out.toList, { st1 with scope := st.scope, out := st.out }, p1, r1)
    | '(' :: rest =>
        if depth + 1 > maxNesting then .error ⟨s!"N3 nesting deeper than {maxNesting}", pos⟩
        else readCollection f (depth + 1) st [] (pos + 1) rest
    | '[' :: rest =>
        if depth + 1 > maxNesting then .error ⟨s!"N3 nesting deeper than {maxNesting}", pos⟩
        else
          let (p1, r1) := tws (pos + 1) rest
          match r1 with
          | ']' :: r2 =>
              let (b, st1) := st.fresh
              .ok (b, st1, p1 + 1, r2)
          | _ =>
            -- [21] iriPropertyList: `[ id iri predicateObjectList ]`.
            let ipl := keyword "id".toList r1
            let headRes : R N3Term :=
              match ipl with
              | some r2 =>
                  let (p2, r2') := tws (p1 + 2) r2
                  match readTurtleIri st.ts p2 r2' with
                  | .error e => .error e
                  | .ok (i, p3, r3) => .ok (.iri i, st, p3, r3)
              | none =>
                  let (b, st1) := st.fresh
                  .ok (b, st1, p1, r1)
            match headRes with
            | .error e => .error e
            | .ok (subj, st1, p2, r2) =>
                let (p3, r3) := tws p2 r2
                match readPOL f (depth + 1) st1 subj false p3 r3 with
                | .error e => .error e
                | .ok ((), st2, p4, r4) =>
                    let (p5, r5) := tws p4 r4
                    match r5 with
                    | ']' :: r6 => .ok (subj, st2, p5 + 1, r6)
                    | _ => .error ⟨"expected ']'", p5⟩
    | '?' :: _ =>
        match readQuickVar pos cs with
        | .error e => .error e
        | .ok (v, p1, r1) => .ok (.var v, st, p1, r1)
    | '_' :: ':' :: _ =>
        match readTurtleBnode pos cs with
        | .error e => .error e
        | .ok (b, p1, r1) => .ok (st.userBnode b, st, p1, r1)
    | '"' :: _ | '\'' :: _ =>
        match readRdfLiteral st.ts pos cs with
        | .error e => .error e
        | .ok (l, p1, r1) => .ok (.lit l, st, p1, r1)
    | '<' :: '<' :: '(' :: rest =>
        -- RDF 1.2 Turtle [30] tripleTerm, read by the Turtle reader.
        if st.ts.mode != .rdf12 then .error ⟨"triple term <<( )>> requires RDF 1.2 mode", pos⟩
        else
          match readTripleTerm f st.ts (pos + 3) rest with
          | .error e => .error e
          | .ok (t, ts1, p1, r1) =>
              let st1 := { st with ts := ts1 }
              match st1.scopeRdf t with
              | .tripleTerm a b c => .ok (.triple a b c, st1, p1, r1)
              | _ => .error ⟨"expected a triple term", pos⟩
    | '<' :: '<' :: _ =>
        -- RDF 1.2 Turtle [27] reifiedTriple, read by the Turtle reader.
        if st.ts.mode != .rdf12 then .error ⟨"reified triple << >> requires RDF 1.2 mode", pos⟩
        else
          match readReifiedTriple f st.ts pos cs with
          | .error e => .error e
          | .ok (o, p1, r1) =>
              let st1 := { st with ts := o.state }
              .ok (ofRdfTerm (st1.scopeRdf o.term), st1.emitRdf o.triples, p1, r1)
    | '<' :: _ =>
        match readTurtleIri st.ts pos cs with
        | .error e => .error e
        | .ok (i, p1, r1) => .ok (.iri i, st, p1, r1)
    | _ =>
        -- Turtle's order: boolean, then numeric, then a prefixed name.
        match readAnyLiteral st.ts pos cs with
        | .ok (l, p1, r1) => .ok (.lit l, st, p1, r1)
        | .error _ =>
            match readTurtleIri st.ts pos cs with
            | .error e => .error e
            | .ok (i, p1, r1) => .ok (.iri i, st, p1, r1)
termination_by fuel

/-- [17] `path`: a path item, then `!` or `^` steps, left to right. -/
def readPath (fuel depth : Nat) (st : N3State) (pos : Nat) (cs : List Char) : R N3Term :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 path", pos⟩
  | f + 1 =>
    match readPathItem f depth st pos cs with
    | .error e => .error e
    | .ok (t, st1, p1, r1) => readPathSteps f depth st1 t p1 r1
termination_by fuel

/-- The `!` and `^` steps after a path item; a tail call per step. -/
def readPathSteps (fuel depth : Nat) (st : N3State) (cur : N3Term) (pos : Nat) (cs : List Char) :
    R N3Term :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 path", pos⟩
  | f + 1 =>
    let (p1, r1) := tws pos cs
    match r1 with
    | '!' :: r2 =>
        let (p2, r2') := tws (p1 + 1) r2
        match readPathItem f depth st p2 r2' with
        | .error e => .error e
        | .ok (pred, st1, p3, r3) =>
            let (b, st2) := st1.fresh
            readPathSteps f depth (st2.emit (cur, pred, b)) b p3 r3
    | '^' :: r2 =>
        let (p2, r2') := tws (p1 + 1) r2
        match readPathItem f depth st p2 r2' with
        | .error e => .error e
        | .ok (pred, st1, p3, r3) =>
            let (b, st2) := st1.fresh
            readPathSteps f depth (st2.emit (b, pred, cur)) b p3 r3
    | _ => .ok (cur, st, pos, cs)
termination_by fuel

/-- [12] `verb` and [14] `predicate`. -/
def readVerb (fuel depth : Nat) (st : N3State) (pos : Nat) (cs : List Char) : R Verb :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 verb", pos⟩
  | f + 1 =>
    let inverse (kwLen : Nat) (rest : List Char) : R Verb :=
      let (p1, r1) := tws (pos + kwLen) rest
      match readPath f depth st p1 r1 with
      | .error e => .error e
      | .ok (t, st1, p2, r2) => .ok ((t, true), st1, p2, r2)
    match cs with
    | '=' :: '>' :: rest => .ok ((.iri logImplies, false), st, pos + 2, rest)
    | '=' :: rest => .ok ((.iri owlSameAs, false), st, pos + 1, rest)
    | '<' :: '=' :: rest =>
        match readIriRef pos cs with
        | .ok _ =>
            match readPath f depth st pos cs with
            | .error e => .error e
            | .ok (t, st1, p1, r1) => .ok ((t, false), st1, p1, r1)
        | .error _ => .ok ((.iri logIsImpliedBy, false), st, pos + 2, rest)
    | '<' :: '-' :: rest =>
        match readIriRef pos cs with
        | .ok _ =>
            match readPath f depth st pos cs with
            | .error e => .error e
            | .ok (t, st1, p1, r1) => .ok ((t, false), st1, p1, r1)
        | .error _ => inverse 2 rest
    | _ =>
      match keyword "a".toList cs with
      | some rest => .ok ((.iri rdfTypeN3, false), st, pos + 1, rest)
      | none =>
      match keyword "has".toList cs with
      | some rest =>
          let (p1, r1) := tws (pos + 3) rest
          match readPath f depth st p1 r1 with
          | .error e => .error e
          | .ok (t, st1, p2, r2) => .ok ((t, false), st1, p2, r2)
      | none =>
      match keyword "is".toList cs with
      | some rest =>
          let (p1, r1) := tws (pos + 2) rest
          match readPath f depth st p1 r1 with
          | .error e => .error e
          | .ok (t, st1, p2, r2) =>
              let (p3, r3) := tws p2 r2
              match keyword "of".toList r3 with
              | some r4 => .ok ((t, true), st1, p3 + 2, r4)
              | none => .error ⟨"expected 'of' after 'is' expression", p3⟩
      | none =>
          match readPath f depth st pos cs with
          | .error e => .error e
          | .ok (t, st1, p1, r1) => .ok ((t, false), st1, p1, r1)
termination_by fuel

/-- [11] `objectList`; a tail call per `,`. -/
def readObjectList (fuel depth : Nat) (st : N3State) (subj : N3Term) (v : Verb)
    (pos : Nat) (cs : List Char) : R Unit :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 object list", pos⟩
  | f + 1 =>
    match readPath f depth st pos cs with
    | .error e => .error e
    | .ok (o, st1, p1, r1) =>
        let asserted : N3Triple := if v.2 then (o, v.1, subj) else (subj, v.1, o)
        let st2 := st1.emit asserted
        let (p2, r2) := tws p1 r1
        -- RDF 1.2 Turtle [33] reifier and [34] annotation, read by the Turtle
        -- reader; the asserted triple must be an RDF triple.
        let annotated : Except ParseError (N3State × Nat × List Char) :=
          match r2 with
          | '~' :: _ | '{' :: '|' :: _ =>
              if st2.ts.mode != .rdf12 then .error ⟨"annotation requires RDF 1.2 mode", p2⟩
              else
                match rdfParts asserted with
                | none => .error ⟨"an annotated triple must be an RDF triple", p2⟩
                | some (bs, bp, bo) =>
                    match readAnnotations f st2.ts bs bp bo p2 r2 none with
                    | .error e => .error e
                    | .ok (ts, ts1, p3, r3) => .ok ({ st2 with ts := ts1 }.emitRdf ts, p3, r3)
          | _ => .ok (st2, p1, r1)
        match annotated with
        | .error e => .error e
        | .ok (st3, p3, r3) =>
            let (p4, r4) := tws p3 r3
            match r4 with
            | ',' :: r5 =>
                let (p5, r5') := tws (p4 + 1) r5
                readObjectList f depth st3 subj v p5 r5'
            | _ => .ok ((), st3, p3, r3)
termination_by fuel

/-- [10] `predicateObjectList`; a tail call per `;`. With `more`, the input
starts at a `;` (a repeated `;`). -/
def readPOL (fuel depth : Nat) (st : N3State) (subj : N3Term) (more : Bool)
    (pos : Nat) (cs : List Char) : R Unit :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 predicate-object list", pos⟩
  | f + 1 =>
    let afterSemi (st1 : N3State) (p : Nat) (r : List Char) : R Unit :=
      let (p1, r1) := tws (p + 1) r
      match r1 with
      | [] => .ok ((), st1, p1, r1)
      | c :: _ =>
          if c == ';' then readPOL f depth st1 subj true p1 r1
          else if endsPOL c then .ok ((), st1, p1, r1)
          else readPOL f depth st1 subj false p1 r1
    if more then
      match cs with
      | ';' :: r => afterSemi st pos r
      | _ => .ok ((), st, pos, cs)
    else
      match readVerb f depth st pos cs with
      | .error e => .error e
      | .ok (v, st1, p1, r1) =>
          let (p2, r2) := tws p1 r1
          match readObjectList f depth st1 subj v p2 r2 with
          | .error e => .error e
          | .ok ((), st2, p3, r3) =>
              let (p4, r4) := tws p3 r3
              match r4 with
              | ';' :: r5 => afterSemi st2 p4 r5
              | _ => .ok ((), st2, p3, r3)
termination_by fuel

/-- [22] `collection`, after its `(`; a tail call per member. -/
def readCollection (fuel depth : Nat) (st : N3State) (accRev : List N3Term)
    (pos : Nat) (cs : List Char) : R N3Term :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 list", pos⟩
  | f + 1 =>
    let (p1, r1) := tws pos cs
    match r1 with
    | ')' :: r2 => .ok (.list accRev.reverse, st, p1 + 1, r2)
    | [] => .error ⟨"expected ')'", p1⟩
    | _ =>
        match readPath f depth st p1 r1 with
        | .error e => .error e
        | .ok (t, st1, p2, r2) => readCollection f depth st1 (t :: accRev) p2 r2
termination_by fuel

/-- [9] `triples ::= subject predicateObjectList?`. -/
def readTriples (fuel depth : Nat) (st : N3State) (pos : Nat) (cs : List Char) : R Unit :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 statement", pos⟩
  | f + 1 =>
    match readPath f depth st pos cs with
    | .error e => .error e
    | .ok (subj, st1, p1, r1) =>
        let (p2, r2) := tws p1 r1
        match r2 with
        | [] => .ok ((), st1, p2, r2)
        | c :: _ =>
            if c == '.' || c == '}' then .ok ((), st1, p2, r2)
            else readPOL f depth st1 subj false p2 r2
termination_by fuel

/-- [23] `formula` content after `{`, up to and including `}`: [24]
`formulaContent ::= n3Statement ('.' formulaContent?)? | sparqlDirective
formulaContent?`. A tail call per statement. -/
def readFormulaContent (fuel depth : Nat) (st : N3State) (pos : Nat) (cs : List Char) : R Unit :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 graph term", pos⟩
  | f + 1 =>
    let (p1, r1) := tws pos cs
    -- After a statement: `.` and more content, or the closing `}`.
    let afterStmt (st1 : N3State) (p : Nat) (r : List Char) : R Unit :=
      let (p2, r2) := tws p r
      match r2 with
      | '.' :: r3 => readFormulaContent f depth st1 (p2 + 1) r3
      | '}' :: r3 => .ok ((), st1, p2 + 1, r3)
      | _ => .error ⟨"expected '.' or '}' in graph term", p2⟩
    match r1 with
    | '}' :: r2 => .ok ((), st, p1 + 1, r2)
    | [] => .error ⟨"expected '}'", p1⟩
    | _ =>
        match readDirective st.ts p1 r1 with
        | .ok ((d, atForm), p2, r2) =>
            let st1 := applyDirective st d
            if atForm then afterStmt st1 p2 r2
            else readFormulaContent f depth st1 p2 r2
        | .error _ =>
            match readTriples f depth st p1 r1 with
            | .error e => .error e
            | .ok ((), st1, p2, r2) => afterStmt st1 p2 r2
termination_by fuel

end

/-- [1] `n3Doc ::= (n3Statement '.' | sparqlDirective)*`; a tail call per
statement. The triples of the document accumulate in `st.out`. -/
def readDocument (fuel : Nat) (st : N3State) (pos : Nat) (cs : List Char) :
    Except ParseError N3State :=
  match fuel with
  | 0 => .error ⟨"recursion limit in N3 document", pos⟩
  | f + 1 =>
    let (p1, r1) := tws pos cs
    let needDot (st1 : N3State) (p : Nat) (r : List Char) : Except ParseError N3State :=
      let (p2, r2) := tws p r
      match r2 with
      | '.' :: r3 => readDocument f st1 (p2 + 1) r3
      | _ => .error ⟨"expected '.' after statement", p2⟩
    match r1 with
    | [] => .ok st
    | _ =>
        match readDirective st.ts p1 r1 with
        | .ok ((d, atForm), p2, r2) =>
            let st1 := applyDirective st d
            if atForm then needDot st1 p2 r2 else readDocument f st1 p2 r2
        | .error _ =>
            match readTriples (8 * f + 64) 0 st p1 r1 with
            | .error e => .error e
            | .ok ((), st1, p2, r2) =>
                if p2 ≤ p1 then .error ⟨"no progress", p1⟩ else needDot st1 p2 r2

/-- What the reader gives: the document's triples, in document order, and the
prefix map at the end of the document (most recent binding first). -/
structure N3Document where
  triples  : N3Graph
  prefixes : List (String × String)
  /-- The prefix of the labels the reader generated; no label of the document
  begins with it (`TurtleState.bnodePrefix`). -/
  bnodePrefix : String
  /-- How many labels the reader generated. -/
  bnodeCount : Nat

/-- Read a Notation3 document. `base` is the retrieval IRI. `mode` is the RDF
version: `.rdf11` reads the N3 grammar over the RDF 1.1 Turtle terminals;
`.rdf12` also reads the RDF 1.2 Turtle productions: language tags with a
direction (`@en--ltr`), `VERSION`, triple terms `<<( s p o )>>`, reified
triples `<< s p o ~r >>`, reifiers `~r` and annotations `{| ... |}`, each by
the Turtle reader's own function (decision 3 of the design record). The empty prefix
`:` is bound to `<#>` (the retrieval IRI with the fragment `#`) until the
document binds it: the convention of cwm and of the Team Submission, which
the suite's Approved tests use (decision 2 of `docs/designissues/2026-10-28-n3.md`;
the report's grammar does not say). -/
def parseN3 (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError N3Document :=
  let cs := text.toList
  let ts := (TurtleState.initChars cs base mode).bindPrefix "" (resolveIri (base.getD "") "#")
  match readDocument (cs.length + 2) { ts } 0 cs with
  | .error e => .error e
  | .ok st => .ok { triples := st.out.toList, prefixes := st.ts.prefixes,
                    bnodePrefix := st.ts.bnodePrefix, bnodeCount := st.ts.bnodeCounter }

end L4Factoidal.N3
