/-
L4Factoidal.Syntax.TriG — the TriG 1.1 parser.

Port of `formal/fstar/Parser.TriG.fst`, built ON TOP of
`Syntax.Turtle`: TriG is Turtle plus graph blocks, and every production
below `[5g] wrappedGraph` is Turtle's, reused verbatim rather than
re-implemented (RDF 1.1 TriG §1: "TriG is an extension of Turtle").

Grammar productions ported (RDF 1.1 TriG, https://www.w3.org/TR/trig/):

  [1g] trigDoc        ::= (directive | block)*
  [2g] block          ::= triplesOrGraph | wrappedGraph | triples2
                        | 'GRAPH' labelOrSubject wrappedGraph
  [3g] triplesOrGraph ::= labelOrSubject (wrappedGraph | predicateObjectList '.')
  [4g] triples2       ::= blankNodePropertyList predicateObjectList? '.'
                        | collection predicateObjectList '.'
  [5g] wrappedGraph   ::= '{' triplesBlock? '}'
  [6g] triplesBlock   ::= triples ('.' triplesBlock?)?
  [7g] labelOrSubject ::= iri | BlankNode

plus the four Turtle directives ([4] prefixID, [5] base, [5s]
sparqlPrefix, [6s] sparqlBase), which in TriG are legal ONLY at the top
level — a directive inside a graph block is a syntax error, and so is a
nested `GRAPH`. Both rejections are the F* source's
(`is_directive_at` / `is_graph_keyword` guards in `parse_graph_body`)
and both are exercised by the suite's `trig-syntax-bad-*` files.

The ambiguity that shapes the whole parser is `[3g] triplesOrGraph`:
after reading an IRI or blank node at the start of a statement, a `{`
makes it a GRAPH NAME and anything else makes it a SUBJECT. This port
resolves it exactly as the F* source does — read the label, skip
whitespace, look at the next character — rather than by backtracking.

Departure from the F* source, stated: `parse_graph_body` there performs
ERROR RECOVERY (skip the offending line, set `has_error`, keep going)
and the strict entry point later turns `has_error` into `None`. This
port fails at the first error and returns that error's message and
position directly. The accept/reject verdict is identical — a document
with any error is rejected either way — and the diagnostic is better,
so the recovery machinery (a CLI affordance, like the lenient Turtle
entry points) is not ported.
-/

import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NQuadsFastTheorems

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Dataset assembly -/

/-- Add a statement's triples to the default graph or to a named graph,
creating the named graph if it does not exist yet. Port of
`trig_dataset_add_triples` / `trig_dataset_add`; the graph-name key is
the `Subject` the `[7g] labelOrSubject` production yields — an IRI or a
blank node, per RDF 1.1 Concepts §4 — stored as-is, the same key
N-Quads uses. -/
def addTriplesTo (ds : Dataset) (gname : Option Subject) (ts : List Triple) : Dataset :=
  ts.foldl (fun d t => addQuad d t gname) ds

/-! ## Keyword and directive lookahead

TriG needs three lookaheads that Turtle does not: is a `GRAPH` keyword
here, is a directive here, and is the next character the `{` that turns
a label into a graph name. Ports of `is_graph_keyword` /
`is_at_directive` / `is_sparql_directive` / `is_directive_at`. -/

/-- Is `GRAPH` (any case) the token at this position? A keyword only
when what follows cannot continue a name — otherwise `graph:x` would be
read as the keyword followed by `:x`. Port of `is_graph_keyword`. -/
def isGraphKeyword (cs : List Char) : Bool :=
  match matchKeyword true "GRAPH".toList cs with
  | none      => false
  | some rest =>
      match rest with
      | []     => true
      | c :: _ => !(isPnChars c || c == ':')

/-- Is a Turtle directive (`@prefix`, `@base`, `PREFIX`, `BASE`) the
token at this position? Used only to REJECT one inside a graph block.
Port of `is_directive_at`. -/
def isDirectiveAt (cs : List Char) : Bool :=
  let ci (kw : String) : Bool :=
    match matchKeyword true kw.toList cs with
    | none      => false
    | some rest => match rest with
                   | []     => true
                   | c :: _ => !(isPnChars c || c == ':')
  (matchKeyword false "@prefix".toList cs).isSome ||
  (matchKeyword false "@base".toList cs).isSome ||
  (matchKeyword false "@version".toList cs).isSome ||
  ci "PREFIX" || ci "BASE" || ci "VERSION"

/-! ## [7g] labelOrSubject -/

/-- `labelOrSubject ::= iri | BlankNode` — the token that may turn out
to be a graph name (if `{` follows) or a subject (if it does not).
Handles `_:label`, the anonymous `[]`, an IRIREF, and a prefixed name.
Port of `parse_trig_graph_name`. -/
def readLabelOrSubject (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (Subject × TurtleState × Nat × List Char) :=
  match cs with
  | '_' :: ':' :: _ =>
      (match readTurtleBnode pos cs with
       | .error e => .error e
       | .ok (b, pos', rest) => .ok (.bnode b, st, pos', rest))
  | '[' :: rest =>
      let (p2, r2) := tws (pos + 1) rest
      (match r2 with
       | ']' :: r3 =>
           let (b, st') := st.freshBnode
           .ok (.bnode b, st', p2 + 1, r3)
       | _ => .error ⟨"expected ']' for anonymous blank node graph name", p2⟩)
  | _ =>
      match readTurtleIri st pos cs with
      | .error e => .error e
      | .ok (i, pos', rest) => .ok (.iri i, st, pos', rest)

/-! ## [5g] wrappedGraph — `'{' triplesBlock? '}'`

The body is a run of Turtle statements. `Syntax.Turtle.readStatement`
already accepts `}` in place of the final `.` (the F* source's issue
#434 behaviour), so the last statement of a block may omit its dot, per
`[6g] triplesBlock`'s optional tail.

Cost, repaired 2026-10-10. The reader used to compute `r1.length` (the whole
remaining input) at every statement, for the fuel of `readStatement` and for the
no-progress guard; it appended `acc ++ ts` per statement; and it added each
triple to the dataset with `addQuad`, whose `Graph.add` is a linear scan. A TriG
document of 10,000 triples took 6.3 s and one of 40,000 triples 108 s, against
0.14 s and 0.87 s in the F* engine
(`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`). The repaired
reader follows `Syntax.Turtle.parseStatements`:

* the fuel is the input length plus 2 at the start and declines once per
  statement; it is never less than the remaining length plus 2, because every
  statement consumes at least one character, so it cannot bind earlier than the
  old fuel did;
* the no-progress guard compares absolute positions (`p2 ≤ p1`);
* the triples of a block collect newest first and are reversed once;
* the dataset is built with the `FastDataset` accumulator of
  `Syntax.NQuadsFast`, whose agreement with `addQuad` is
  `addQuadFast_toDataset` (`NQuadsFastTheorems.lean`); `addTriplesToFast_toDataset`
  below lifts it to a statement.

The superseded reader is kept at the end of this file as `parseTriGSpec`, and
`#guard`s compare the two on every branch. -/

/-- Parse a graph block's body up to and including its closing `}`.
`pos`/`cs` start just AFTER the opening `{`. `accRev` holds the triples read so
far, newest first; the result is in source order. Port of `parse_graph_body`,
minus its error recovery (module header). -/
def readGraphBody : Nat → TurtleState → Nat → List Char → List Triple →
    Except ParseError (List Triple × TurtleState × Nat × List Char)
  | 0,        st, pos, cs, accRev => .ok (accRev.reverse, st, pos, cs)
  | fuel + 1, st, pos, cs, accRev =>
      let (p1, r1) := tws pos cs
      match r1 with
      | []        => .error ⟨"unterminated graph block (expected '}')", p1⟩
      | '}' :: r2 => .ok (accRev.reverse, st, p1 + 1, r2)
      | _ =>
          if isDirectiveAt r1 then
            .error ⟨"directives are not allowed inside a graph block", p1⟩
          else if isGraphKeyword r1 then
            .error ⟨"nested GRAPH is not allowed inside a graph block", p1⟩
          else
            match readStatement fuel st p1 r1 with
            | .error e => .error e
            | .ok (ts, st', p2, r2) =>
                let nextAcc := ts.reverse ++ accRev
                if p2 ≤ p1 then .ok (nextAcc.reverse, st', p2, r2)
                else readGraphBody fuel st' p2 r2 nextAcc

/-! ## [2g] block — one top-level TriG statement -/

/-- Parse one top-level TriG statement, returning the graph it belongs
to (`none` = default graph) and its triples. `fuel` is the caller's remaining
statement budget (see the cost note above). Port of `parse_trig_statement`. -/
def readTriGStatement (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError ((Option Subject × List Triple) × TurtleState × Nat × List Char) :=
  let (p1, r1) := tws pos cs
  match r1 with
  | [] => .ok ((none, []), st, p1, [])
  | _ =>
    match readPrefixDirective st p1 r1 with
    | .ok ((pfx, iri), p2, r2) =>
        .ok ((none, []), { st with prefixes := (pfx, iri) :: st.prefixes }, p2, r2)
    | .error _ =>
      match readBaseDirective st p1 r1 with
      | .ok (b, p2, r2) => .ok ((none, []), { st with baseIri := b }, p2, r2)
      | .error _ =>
        -- RDF 1.2 TriG [3] directive additionally admits `version`
        -- (`@version "…" .` / `VERSION "…"`), top level only, `.rdf12` only.
        match (if st.mode == .rdf12 then readVersionDirective p1 r1
               else .error ⟨"not RDF 1.2", p1⟩) with
        | .ok (p2, r2) => .ok ((none, []), st, p2, r2)
        | .error _ =>
        match r1 with
        -- [5g] a bare wrappedGraph: the DEFAULT graph.
        | '{' :: r2 =>
            (match readGraphBody fuel st (p1 + 1) r2 [] with
             | .error e => .error e
             | .ok (ts, st', p3, r3) => .ok ((none, ts), st', p3, r3))
        | _ =>
          -- `GRAPH labelOrSubject wrappedGraph`
          if isGraphKeyword r1 then
            let (p2, r2) := tws (p1 + 5) (r1.drop 5)
            match readLabelOrSubject st p2 r2 with
            | .error _ => .error ⟨"expected a graph name after GRAPH", p2⟩
            | .ok (g, st2, p3, r3) =>
                let (p4, r4) := tws p3 r3
                match r4 with
                | '{' :: r5 =>
                    (match readGraphBody fuel st2 (p4 + 1) r5 [] with
                     | .error e => .error e
                     | .ok (ts, st3, p6, r6) => .ok ((some g, ts), st3, p6, r6))
                | _ => .error ⟨"expected '{' after graph name", p4⟩
          else
            -- [3g] triplesOrGraph: read the label, then let the next
            -- character decide between wrappedGraph and subject.
            match readLabelOrSubject st p1 r1 with
            | .error _ =>
                -- [4g] triples2 and every other Turtle statement shape
                -- (`[ … ]` property lists, collections as subject).
                (match readStatement fuel st p1 r1 with
                 | .error e => .error e
                 | .ok (ts, st', p2, r2) => .ok ((none, ts), st', p2, r2))
            | .ok (lbl, st2, p2, r2) =>
                let (p3, r3) := tws p2 r2
                match r3 with
                | '{' :: r4 =>
                    (match readGraphBody fuel st2 (p3 + 1) r4 [] with
                     | .error e => .error e
                     | .ok (ts, st3, p5, r5) => .ok ((some lbl, ts), st3, p5, r5))
                | _ =>
                    match readPredicateObjectList fuel st2 lbl p3 r3 with
                    | .error e => .error e
                    | .ok (ts, st3, p4, r4) =>
                        let (p5, r5) := tws p4 r4
                        match r5 with
                        | '.' :: r6 => .ok ((none, ts), st3, p5 + 1, r6)
                        | []        => .ok ((none, ts), st3, p5, r5)
                        | '}' :: _  => .ok ((none, ts), st3, p5, r5)
                        | _ => .error ⟨"expected '.' after triple", p5⟩

/-! ## [1g] trigDoc -/

/-- Add a statement's triples to a dataset under construction: the
`FastDataset` twin of `addTriplesTo`. -/
def addTriplesToFast (ds : FastDataset) (gname : Option Subject) (ts : List Triple) :
    FastDataset :=
  ts.foldl (fun d t => addQuadFast d t gname) ds

/-- `trigDoc ::= (directive | block)*`. STRICT, with a no-progress guard
(same shape as `Syntax.Turtle.parseStatements`). The fuel starts above the
document's character count and declines once per completed statement. Port of
`parse_trig_doc`. -/
def parseTriGStatements : Nat → TurtleState → Nat → List Char → FastDataset →
    Except ParseError (FastDataset × TurtleState)
  | 0,        st, _,   _,  ds => .ok (ds, st)
  | fuel + 1, st, pos, cs, ds =>
      let (p1, r1) := tws pos cs
      match r1 with
      | [] => .ok (ds, st)
      | _ =>
          match readTriGStatement fuel st p1 r1 with
          | .error e => .error e
          | .ok ((gname, ts), st', p2, r2) =>
              let ds' := addTriplesToFast ds gname ts
              if p2 ≤ p1 then .ok (ds', st')
              else parseTriGStatements fuel st' p2 r2 ds'

/-- Parse a complete TriG document into a `Dataset`. `base` is the
retrieval IRI (the W3C suite uses
`http://www.w3.org/2013/TriGTests/<file>`); `mode` defaults to RDF 1.1.
Port of `parse_trig_with_base_strict_mode`. -/
def parseTriG (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError Dataset :=
  let cs := text.toList
  match parseTriGStatements (cs.length + 2) (TurtleState.init text base mode) 0 cs {} with
  | .error e    => .error e
  | .ok (ds, _) => .ok ds.toDataset

/-- Adding a statement's triples with the indexed accumulator denotes adding
them with `addQuad`, whenever the accumulator satisfies its invariant. -/
theorem addTriplesToFast_toDataset (gname : Option Subject) (ts : List Triple) :
    ∀ ds : FastDataset, ds.Inv →
      (addTriplesToFast ds gname ts).Inv
      ∧ (addTriplesToFast ds gname ts).toDataset = addTriplesTo ds.toDataset gname ts := by
  induction ts with
  | nil => intro ds h; exact ⟨h, rfl⟩
  | cons t ts ih =>
      intro ds h
      have h1 := FastDataset.add_inv (t := t) (gopt := gname) h
      have h2 := ih (addQuadFast ds t gname) h1
      refine ⟨h2.1, ?_⟩
      show (addTriplesToFast (addQuadFast ds t gname) gname ts).toDataset
          = addTriplesTo (addQuad ds.toDataset t gname) gname ts
      rw [h2.2, addQuadFast_toDataset t gname h]

/-! ## The superseded reader, kept as the record (2026-10-10)

The functions in this section are the TriG statement reader as it was before
its quadratic costs were removed: `List.length` of the remainder at every
statement, `acc ++ ts` per statement, and `addQuad` (a `Graph.add` scan) per
triple. The engine does not call them. The `#guard`s at the end of the file
compare the repaired reader with them on documents that exercise every branch. -/

/-- Parse a graph block's body up to and including its closing `}`.
`pos`/`cs` start just AFTER the opening `{`. Port of
`parse_graph_body`, minus its error recovery (module header). -/
def readGraphBodySpec : Nat → TurtleState → Nat → List Char → List Triple →
    Except ParseError (List Triple × TurtleState × Nat × List Char)
  | 0,        st, pos, cs, acc => .ok (acc, st, pos, cs)
  | fuel + 1, st, pos, cs, acc =>
      let (p1, r1) := tws pos cs
      match r1 with
      | []        => .error ⟨"unterminated graph block (expected '}')", p1⟩
      | '}' :: r2 => .ok (acc, st, p1 + 1, r2)
      | _ =>
          if isDirectiveAt r1 then
            .error ⟨"directives are not allowed inside a graph block", p1⟩
          else if isGraphKeyword r1 then
            .error ⟨"nested GRAPH is not allowed inside a graph block", p1⟩
          else
            match readStatement (r1.length + 2) st p1 r1 with
            | .error e => .error e
            | .ok (ts, st', p2, r2) =>
                if r2.length ≥ r1.length then .ok (acc ++ ts, st', p2, r2)
                else readGraphBodySpec fuel st' p2 r2 (acc ++ ts)

/-- Parse one top-level TriG statement, returning the graph it belongs
to (`none` = default graph) and its triples. Port of
`parse_trig_statement`. -/
def readTriGStatementSpec (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError ((Option Subject × List Triple) × TurtleState × Nat × List Char) :=
  let (p1, r1) := tws pos cs
  match r1 with
  | [] => .ok ((none, []), st, p1, [])
  | _ =>
    match readPrefixDirective st p1 r1 with
    | .ok ((pfx, iri), p2, r2) =>
        .ok ((none, []), { st with prefixes := (pfx, iri) :: st.prefixes }, p2, r2)
    | .error _ =>
      match readBaseDirective st p1 r1 with
      | .ok (b, p2, r2) => .ok ((none, []), { st with baseIri := b }, p2, r2)
      | .error _ =>
        -- RDF 1.2 TriG [3] directive additionally admits `version`
        -- (`@version "…" .` / `VERSION "…"`), top level only, `.rdf12` only.
        match (if st.mode == .rdf12 then readVersionDirective p1 r1
               else .error ⟨"not RDF 1.2", p1⟩) with
        | .ok (p2, r2) => .ok ((none, []), st, p2, r2)
        | .error _ =>
        match r1 with
        -- [5g] a bare wrappedGraph: the DEFAULT graph.
        | '{' :: r2 =>
            (match readGraphBodySpec (r2.length + 2) st (p1 + 1) r2 [] with
             | .error e => .error e
             | .ok (ts, st', p3, r3) => .ok ((none, ts), st', p3, r3))
        | _ =>
          -- `GRAPH labelOrSubject wrappedGraph`
          if isGraphKeyword r1 then
            let (p2, r2) := tws (p1 + 5) (r1.drop 5)
            match readLabelOrSubject st p2 r2 with
            | .error _ => .error ⟨"expected a graph name after GRAPH", p2⟩
            | .ok (g, st2, p3, r3) =>
                let (p4, r4) := tws p3 r3
                match r4 with
                | '{' :: r5 =>
                    (match readGraphBodySpec (r5.length + 2) st2 (p4 + 1) r5 [] with
                     | .error e => .error e
                     | .ok (ts, st3, p6, r6) => .ok ((some g, ts), st3, p6, r6))
                | _ => .error ⟨"expected '{' after graph name", p4⟩
          else
            -- [3g] triplesOrGraph: read the label, then let the next
            -- character decide between wrappedGraph and subject.
            match readLabelOrSubject st p1 r1 with
            | .error _ =>
                -- [4g] triples2 and every other Turtle statement shape
                -- (`[ … ]` property lists, collections as subject).
                (match readStatement (r1.length + 2) st p1 r1 with
                 | .error e => .error e
                 | .ok (ts, st', p2, r2) => .ok ((none, ts), st', p2, r2))
            | .ok (lbl, st2, p2, r2) =>
                let (p3, r3) := tws p2 r2
                match r3 with
                | '{' :: r4 =>
                    (match readGraphBodySpec (r4.length + 2) st2 (p3 + 1) r4 [] with
                     | .error e => .error e
                     | .ok (ts, st3, p5, r5) => .ok ((some lbl, ts), st3, p5, r5))
                | _ =>
                    match readPredicateObjectList (r3.length + 2) st2 lbl p3 r3 with
                    | .error e => .error e
                    | .ok (ts, st3, p4, r4) =>
                        let (p5, r5) := tws p4 r4
                        match r5 with
                        | '.' :: r6 => .ok ((none, ts), st3, p5 + 1, r6)
                        | []        => .ok ((none, ts), st3, p5, r5)
                        | '}' :: _  => .ok ((none, ts), st3, p5, r5)
                        | _ => .error ⟨"expected '.' after triple", p5⟩

/-- `trigDoc ::= (directive | block)*`. STRICT, with a no-progress guard
(same shape as `Syntax.Turtle.parseStatements`). Port of
`parse_trig_doc`. -/
def parseTriGStatementsSpec : Nat → TurtleState → Nat → List Char → Dataset →
    Except ParseError (Dataset × TurtleState)
  | 0,        st, _,   _,  ds => .ok (ds, st)
  | fuel + 1, st, pos, cs, ds =>
      let (p1, r1) := tws pos cs
      match r1 with
      | [] => .ok (ds, st)
      | _ =>
          match readTriGStatementSpec st p1 r1 with
          | .error e => .error e
          | .ok ((gname, ts), st', p2, r2) =>
              let ds' := addTriplesTo ds gname ts
              if r2.length ≥ r1.length then .ok (ds', st')
              else parseTriGStatementsSpec fuel st' p2 r2 ds'

/-- Parse a complete TriG document into a `Dataset`. `base` is the
retrieval IRI (the W3C suite uses
`http://www.w3.org/2013/TriGTests/<file>`); `mode` defaults to RDF 1.1.
Port of `parse_trig_with_base_strict_mode`. -/
def parseTriGSpec (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError Dataset :=
  let cs := text.toList
  match parseTriGStatementsSpec (cs.length + 2) (TurtleState.init text base mode) 0 cs Dataset.empty with
  | .error e    => .error e
  | .ok (ds, _) => .ok ds

/-- `parseTriG`, also returning the prefix map in force at the end of the
document, most recent binding first (see `parseTurtleWithPrefixes`). -/
def parseTriGWithPrefixes (text : String) (base : Option String := none)
    (mode : Mode := .rdf11) : Except ParseError (Dataset × List (String × String)) :=
  let cs := text.toList
  match parseTriGStatements (cs.length + 2) (TurtleState.init text base mode) 0 cs {} with
  | .error e     => .error e
  | .ok (ds, st) => .ok (ds.toDataset, st.prefixes)


/-! ## The repaired reader agrees with the superseded one

Each document exercises one branch of the reader: a default-graph block, a
named graph by IRI, by `GRAPH`, by prefixed name, by blank node and by `[]`,
a graph name used twice, a duplicate triple inside a graph, a duplicate across
two blocks of the same graph, plain triples next to blocks, directives, a
directive inside a block, a nested `GRAPH`, a missing `}`, a missing `.`, and
an empty document. The comparison is the whole `Except` value, so error
messages and offsets must agree as well. -/

private def trigDocs : List String :=
  [ "",
    "# comment only\n",
    "<http://e/a> <http://e/p> <http://e/b> .",
    "{ <http://e/a> <http://e/p> <http://e/b> . <http://e/a> <http://e/p> <http://e/c> }",
    "<http://e/g> { <http://e/a> <http://e/p> <http://e/b> . <http://e/a> <http://e/p> <http://e/b> . }",
    "GRAPH <http://e/g> { <http://e/a> <http://e/p> <http://e/b> }",
    "@prefix e: <http://e/> . e:g { e:a e:p e:b ; e:q \"x\"@en , \"y\" . } e:h { e:c e:p e:d }",
    "@prefix e: <http://e/> . e:g { e:a e:p e:b } e:g { e:a e:p e:b . e:a e:p e:c }",
    "@prefix e: <http://e/> . _:g { e:a e:p e:b } [] { e:a e:p e:c } e:a e:p e:b .",
    "@prefix e: <http://e/> . e:a e:p [ e:q e:r ] . e:g { e:b e:p ( 1 2 3 ) }",
    "@prefix e: <http://e/> . e:g { e:a e:p e:b } e:a e:p \"1\"^^<http://www.w3.org/2001/XMLSchema#integer>, \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> .",
    "BASE <http://e/> PREFIX e: <http://e/> GRAPH e:g { <a> e:p <b> }",
    "@prefix e: <http://e/> . e:g { @prefix f: <http://f/> . }",
    "@prefix e: <http://e/> . e:g { GRAPH e:h { e:a e:p e:b } }",
    "@prefix e: <http://e/> . e:g { e:a e:p e:b",
    "@prefix e: <http://e/> . e:g { e:a e:p e:b } e:a e:p",
    "@prefix e: <http://e/> . GRAPH { e:a e:p e:b }",
    "{ }",
    "<http://e/g> { }",
    "VERSION \"1.2\" PREFIX p: <http://a/> p:g { p:s p:p p:o ~ p:r . }" ]

private def sameResult : Except ParseError Dataset → Except ParseError Dataset → Bool
  | .ok a,    .ok b    => decide (a = b)
  | .error a, .error b => decide (a = b)
  | _,        _        => false

private def sameTriG (d : String) (mode : Mode) : Bool :=
  sameResult (parseTriG d none mode) (parseTriGSpec d none mode)

#guard trigDocs.all (fun d => sameTriG d .rdf11)
#guard trigDocs.all (fun d => sameTriG d .rdf12)

/-! The comparison has teeth: the documents above parse to different datasets
(so an implementation that returned one dataset for every input would fail) and
several are rejected (so one that accepted every input would fail too). -/

#guard (trigDocs.filter (fun d => (parseTriG d none .rdf11).toOption.isSome)).length ≥ 10
#guard (trigDocs.filter (fun d => (parseTriG d none .rdf11).toOption.isNone)).length ≥ 5
#guard (match parseTriG trigDocs[7]! none .rdf11 with
        | .ok ds => ds.named.map (fun ng => ng.graph.length)
        | .error _ => []) == [2]
#guard (match parseTriG trigDocs[4]! none .rdf11 with
        | .ok ds => ds.named.map (fun ng => ng.graph.length)
        | .error _ => []) == [1]
#guard (match parseTriG trigDocs[8]! none .rdf11 with
        | .ok ds => (ds.named.length, ds.default.length)
        | .error _ => (0, 0)) == (2, 1)


/-! `parseTriGWithPrefixes` (the npm prefixes envelope) runs the same reader
as `parseTriG`; on every document above it gives the same dataset or error. -/
#guard trigDocs.all (fun d =>
  sameResult ((parseTriGWithPrefixes d none .rdf11).map Prod.fst) (parseTriG d none .rdf11))
#guard trigDocs.all (fun d =>
  sameResult ((parseTriGWithPrefixes d none .rdf12).map Prod.fst) (parseTriG d none .rdf12))

end L4Factoidal.Syntax
