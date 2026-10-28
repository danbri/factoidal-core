/-
L4Factoidal.SPARQLRL.Parser — the SPARQL-RL grammar
(`third_party/testing/sparql-rl/spec/sparql-rl-grammar.bnf`, productions
[1]-[125], an LL(1) grammar) to the abstract syntax of `SPARQLRL/Syntax.lean`.

Draft: https://w3c.github.io/data-shapes/sparql12-rl/ § "SPARQL-RL Grammar".
Issue: https://github.com/danbri/factoidal/issues/1099.

## Reuse of the SPARQL 1.2 parser

* Terminals: `SPARQL.tokenize12`, the SPARQL 1.2 tokenizer. SPARQL-RL's
  terminals [126]-[160] are SPARQL 1.2's. The SPARQL-RL keywords that SPARQL
  does not have (`RULE`, `SET`, `IMPORTS`) arrive as bare-word `pname` tokens
  (a real prefixed name always contains `:`), and are matched without case,
  as the grammar's note 2 asks. `:=` arrives as the two tokens `:` and `=`.
* Expressions [107]-[125]: `SPARQL.pExpr` / `SPARQL.pPrimaryExpr`. The
  SPARQL-RL expression grammar is a subset of SPARQL 1.2's; the tokens that
  only SPARQL has (`EXISTS`, `BOUND`, `COALESCE`, `RAND`, the hash functions,
  the aggregates) are rejected after the call (`exprTokensOk`).
* Terms: the SPARQL parser's literal and IRI constructors (`mkTypedLit?`,
  `mkLangLit`, `mkDirLangLit`, `resolvePnameIri`, `mkIri?`).

The triples grammar is written here, once, for the three areas the draft
separates (data blocks, head templates, body patterns; CHANGES.md
2026-07-07), with a `Mode` flag: data has no variables and no paths, a head
template has variables and no paths, a body pattern has variables and the
paths `/` and `^` only. A path is expanded to triple patterns with fresh
variables (draft § "Relationship between SPARQL-RL and SPARQL": "These can be
expanded into triple patterns").

Reification follows SPARQL 1.2 / Turtle 1.2: `<< s p o ~r >>` stands for `r`
with `r rdf:reifies <<( s p o )>>`; `s p o ~r {| q z |}` asserts `s p o`,
`r rdf:reifies <<( s p o )>>` and `r q z`; an annotation block without a
reifier gets a fresh blank node. Collections are `rdf:first`/`rdf:rest` lists.

`BASE` is applied by a pass over the token stream before the grammar
(`resolveBases`): each `BASE` resolves against the previous one, and every
later relative IRI reference resolves against the base in scope at its
position (draft § "IRI References").

## Termination

The grammar is one `mutual` block, structurally recursive on a fuel
argument, as `SPARQL/Parser.lean` is. The seed is proportional to the token
count (`parseRuleSet`). No `partial def`.
-/
import L4Factoidal.SPARQLRL.Syntax
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQLRL

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Syntax

/-- Which of the three triple areas is being parsed. -/
inductive Mode where
  | data
  | template
  | pattern
  deriving DecidableEq, Repr

/-- Parser state: the SPARQL parser context (prefixes), the counter for fresh
names, and the triples emitted so far by the current triples block. -/
structure PSt where
  pst : PState := { v12 := true }
  n   : Nat := 0
  out : Array STriple := #[]

/-- A fresh blank node (template, data) or variable (pattern). -/
def PSt.fresh (ps : PSt) (m : Mode) : STerm × PSt :=
  let nm := ".n" ++ toString ps.n
  ((if m == .pattern then .var nm else .bnode nm), { ps with n := ps.n + 1 })

def PSt.emit (ps : PSt) (t : STriple) : PSt := { ps with out := ps.out.push t }

/-- A user blank-node label: a variable in a body pattern, else a blank node. -/
def userBnode (m : Mode) (label : String) : STerm :=
  if m == .pattern then .var (".b" ++ label) else .bnode label

def kwIs (t : Token) (w : String) : Bool :=
  match t with
  | .pname s => stringUpper s == w
  | _ => false

/-- A real prefixed name (it has a colon), as opposed to a bare word. -/
def isPname (s : String) : Bool := s.toList.contains ':'

def iriT (i : WfIri) : STerm := .iri i
def rdfTypeT : STerm := .iri rdfTypeIri
def rdfFirstT : STerm := .iri rdfFirstIri
def rdfRestT : STerm := .iri rdfRestIri
def rdfNilT : STerm := .iri rdfNilIri
def rdfReifiesT : STerm := .iri rdfReifiesIri

def xsdT (s : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ s

/-- An IRI token (already resolved against the base) or a prefixed name. -/
def iriOf (ps : PSt) (ts : TStream) : Except ParseError (Option (STerm × TStream)) :=
  match peekTok ts with
  | .iri s =>
      match mkIri? s with
      | some i => .ok (some (.iri i, advTok ts))
      | none => pErr s!"not an absolute IRI: {s}" ts
  | .pname pn =>
      if !isPname pn then .ok none
      else match resolvePnameIri ps.pst pn with
        | some i => .ok (some (.iri i, advTok ts))
        | none => pErr s!"undefined prefix in {pn}" ts
  | _ => .ok none

def numLit (lex dt : String) (ts : TStream) : Except ParseError STerm :=
  match mkTypedLit? lex (xsdT dt) with
  | some l => .ok (.lit l)
  | none => pErr "invalid numeric literal" ts

/-- [97] RDFLiteral after its string: `@lang`, `@lang--dir`, `^^iri`, or none. -/
def litSuffix (ps : PSt) (s : String) (ts : TStream) : Except ParseError (STerm × TStream) :=
  match peekTok ts with
  | .langtag t => .ok (.lit (mkLangLit s t), advTok ts)
  | .langdir t d => .ok (.lit (mkDirLangLit s t d), advTok ts)
  | .hathat => do
      let ts1 := advTok ts
      match ← iriOf ps ts1 with
      | some (.iri dt, ts2) =>
          match mkTypedLit? s dt.val with
          | some l => .ok (.lit l, ts2)
          | none => pErr "invalid datatype" ts1
      | _ => pErr "expected a datatype IRI after ^^" ts1
  | _ => .ok (.lit (mkPlainLit s), ts)

/-- A single-token term (or a signed number, or `[]`): Var, iri, RDFLiteral,
NumericLiteral, BooleanLiteral, BlankNode. `none` when the next token starts
none of them. A variable in `Mode.data` is an error (grammar note 4). -/
def pAtom (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (Option (STerm × PSt × TStream)) := do
  match ← iriOf ps ts with
  | some (t, ts1) => return some (t, ps, ts1)
  | none =>
  match peekTok ts with
  | .var v =>
      if m == .data then pErr "a variable is not allowed in a DATA block" ts
      else return some (.var v, ps, advTok ts)
  | .str s => do
      let (t, ts1) ← litSuffix ps s (advTok ts)
      return some (t, ps, ts1)
  | .integer n => return some (← numLit n "integer" ts, ps, advTok ts)
  | .decimal d => return some (← numLit d "decimal" ts, ps, advTok ts)
  | .double d => return some (← numLit d "double" ts, ps, advTok ts)
  | .plus | .minusOp =>
      let sign := if peekTok ts == .plus then "+" else "-"
      let ts1 := advTok ts
      match peekTok ts1 with
      | .integer n => return some (← numLit (sign ++ n) "integer" ts1, ps, advTok ts1)
      | .decimal d => return some (← numLit (sign ++ d) "decimal" ts1, ps, advTok ts1)
      | .double d => return some (← numLit (sign ++ d) "double" ts1, ps, advTok ts1)
      | _ => pErr "expected a number after the sign" ts1
  | .trueKw => return some (.lit (mkTypedLiteral "true" xsdBoolean), ps, advTok ts)
  | .falseKw => return some (.lit (mkTypedLiteral "false" xsdBoolean), ps, advTok ts)
  | .bnode b => return some (userBnode m b, ps, advTok ts)
  | .lbracket =>
      let ts1 := advTok ts
      if peekTok ts1 == .rbracket then
        let (t, ps1) := ps.fresh m
        return some (t, ps1, advTok ts1)
      else return none
  | _ => return none

/-- [87] Verb / [33] VerbData without paths: Var (not in data), iri, `a`. -/
def pSimpleVerb (m : Mode) (ps : PSt) (ts : TStream) : Except ParseError (STerm × TStream) := do
  match ← iriOf ps ts with
  | some r => return r
  | none =>
  match peekTok ts with
  | .a => return (rdfTypeT, advTok ts)
  | .var v =>
      if m == .data then pErr "a variable is not allowed in a DATA block" ts
      else return (.var v, advTok ts)
  | _ => pErr "expected a predicate" ts

/-- [80] ReifierId: Var (not in data), iri, BlankNode; `none` when absent. -/
def pReifierId (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (Option (STerm × PSt × TStream)) := do
  match peekTok ts with
  | .var _ | .bnode _ | .lbracket => pAtom m ps ts
  | _ =>
    match ← iriOf ps ts with
    | some (t, ts1) => return some (t, ps, ts1)
    | none => return none

/-! ## Paths — [88]-[92] -/

/-- A SPARQL-RL path: an IRI, an inverse, a sequence. -/
inductive SPath where
  | pred (p : STerm)
  | inv (p : SPath)
  | seq (a b : SPath)
  deriving Repr, Inhabited

/-- Expand a path between two terms into triple patterns, appended to `acc`,
with fresh variables for the intermediate nodes of a sequence. The parser
builds a sequence `p1/p2/.../pn` right-nested (`pPathSeqRest`), so the walk
along it is a tail call; only the first part of a `.seq` takes a frame, and
that part is a sequence only inside parentheses, so the depth is the
parenthesis nesting of the path (at most `maxNesting`). -/
def expandPathAcc (ps : PSt) (acc : Array STriple) : SPath → STerm → STerm → Array STriple × PSt
  | .pred p, s, o => (acc.push ⟨s, p, o⟩, ps)
  | .inv q, s, o => expandPathAcc ps acc q o s
  | .seq a b, s, o =>
      let (v, ps1) := ps.fresh .pattern
      let (acc2, ps2) := expandPathAcc ps1 acc a s v
      expandPathAcc ps2 acc2 b v o

def expandPath (ps : PSt) (q : SPath) (s o : STerm) : List STriple × PSt :=
  let (ts, ps1) := expandPathAcc ps #[] q s o
  (ts.toList, ps1)

/-- The sequence of the parts `p1 ... pn` (given reversed, `pn` first),
right-nested: `p1/(p2/(.../pn))`. A tail call per part. -/
def seqOfRev : SPath → List SPath → SPath
  | acc, [] => acc
  | acc, p :: ps => seqOfRev (.seq p acc) ps

mutual
/-- [89] Path / [90] PathSequence. -/
def pPath (fuel : Nat) (ps : PSt) (ts : TStream) : Except ParseError (SPath × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 => do
    let (a, ts1) ← pPathEltOrInverse f ps ts
    pPathSeqRest f ps a [] ts1

/-- `( '/' PathEltOrInverse )*`. `last` is the latest part, `prev` the parts
before it (reversed). A tail call per `/`. -/
def pPathSeqRest (fuel : Nat) (ps : PSt) (last : SPath) (prev : List SPath) (ts : TStream) :
    Except ParseError (SPath × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    if peekTok ts == .slash then do
      let (b, ts1) ← pPathEltOrInverse f ps (advTok ts)
      pPathSeqRest f ps b (last :: prev) ts1
    else .ok (seqOfRev last prev, ts)

/-- [91] PathEltOrInverse. -/
def pPathEltOrInverse (fuel : Nat) (ps : PSt) (ts : TStream) :
    Except ParseError (SPath × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    if peekTok ts == .caret then do
      let (a, ts1) ← pPathElt f ps (advTok ts)
      .ok (.inv a, ts1)
    else pPathElt f ps ts

/-- [92] PathElt ::= iri | 'a' | '(' Path ')'. -/
def pPathElt (fuel : Nat) (ps : PSt) (ts : TStream) : Except ParseError (SPath × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 => do
    match ← iriOf ps ts with
    | some (t, ts1) => .ok (.pred t, ts1)
    | none =>
      match peekTok ts with
      | .a => .ok (.pred rdfTypeT, advTok ts)
      | .lparen => do
          let (p, ts1) ← pPath f ps (advTok ts)
          if peekTok ts1 == .rparen then .ok (p, advTok ts1)
          else pErr "expected ')' in a path" ts1
      | _ => pErr "expected a path" ts
end

/-- A parsed verb: a simple predicate, or a path that is more than an IRI. -/
inductive VerbR where
  | simple (p : STerm)
  | path (p : SPath)
  deriving Inhabited

/-- The tokens that start a verb in each mode. -/
def startsVerb (m : Mode) : Token → Bool
  | .a | .iri _ => true
  | .pname s => isPname s
  | .var _ => m != .data
  | .caret | .lparen => m == .pattern
  | _ => false

/-- The tokens that start a triples block ([29], [52], [66]). -/
def startsTriple : Token → Bool
  | .var _ | .iri _ | .str _ | .integer _ | .decimal _ | .double _
  | .plus | .minusOp | .trueKw | .falseKw | .bnode _
  | .lbracket | .lparen | .ttOpen | .ttBareOpen => true
  | .pname s => isPname s
  | _ => false

/-- Emit the triples of one object for a verb. -/
def emitObject (ps : PSt) (s : STerm) (v : VerbR) (o : STerm) : PSt :=
  match v with
  | .simple p => ps.emit ⟨s, p, o⟩
  | .path q =>
      let (ts, ps1) := expandPath ps q s o
      ts.foldl PSt.emit ps1

/-! ## Triples — [29]-[86] -/

mutual
/-- [48] TripleTermData / [84] TripleTerm, after `<<(`. -/
def pTripleTerm (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (STerm × PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 => do
    let (s, ps1, ts1) ← pTTComp f m ps ts
    let (p, ts2) ← pSimpleVerb m ps1 ts1
    let (o, ps3, ts3) ← pTTComp f m ps1 ts2
    if peekTok ts3 == .ttClose then .ok (.triple s p o, ps3, advTok ts3)
    else pErr "expected ')>>'" ts3

/-- [85]/[86] TripleTermSubject/Object: Var, iri, literal, BlankNode, TripleTerm. -/
def pTTComp (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (STerm × PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    if peekTok ts == .ttOpen then pTripleTerm f m ps (advTok ts)
    else do
      match ← pAtom m ps ts with
      | some r => .ok r
      | none => pErr "expected a triple-term component" ts

/-- [81] ReifiedTriple, after `<<`: `<< s p o ~r? >>` is `r`, with the
triple `r rdf:reifies <<( s p o )>>`. -/
def pReified (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (STerm × PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 => do
    let (s, ps1, ts1) ← pRTComp f m ps ts
    let (p, ts2) ← pSimpleVerb m ps1 ts1
    let (o, ps3, ts3) ← pRTComp f m ps1 ts2
    let (r, ps4, ts4) ←
      if peekTok ts3 == .tilde then do
        match ← pReifierId m ps3 (advTok ts3) with
        | some x => pure x
        | none => let (r, ps') := ps3.fresh m; pure (r, ps', advTok ts3)
      else let (r, ps') := ps3.fresh m; pure (r, ps', ts3)
    if peekTok ts4 == .ttBareClose then
      .ok (r, ps4.emit ⟨r, rdfReifiesT, .triple s p o⟩, advTok ts4)
    else pErr "expected '>>'" ts4

/-- [82]/[83] ReifiedTripleSubject/Object. -/
def pRTComp (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (STerm × PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .ttBareOpen => pReified f m ps (advTok ts)
    | .ttOpen => pTripleTerm f m ps (advTok ts)
    | _ => do
      match ← pAtom m ps ts with
      | some r => .ok r
      | none => pErr "expected a reified-triple component" ts

/-- [36] GraphNodeData / [58] GraphNodeTemplate / [78] GraphNodePattern. -/
def pGraphNode (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (STerm × PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .lbracket =>
        if peekTok (advTok ts) == .rbracket then
          let (b, ps1) := ps.fresh m
          .ok (b, ps1, advTok (advTok ts))
        else do
          let (b, ps1) := ps.fresh m
          let (ps2, ts2) ← pPLNE f m ps1 b (advTok ts)
          if peekTok ts2 == .rbracket then .ok (b, ps2, advTok ts2)
          else pErr "expected ']'" ts2
    | .lparen =>
        if peekTok (advTok ts) == .rparen then .ok (rdfNilT, ps, advTok (advTok ts))
        else pCollection f m ps [] (advTok ts)
    | .ttBareOpen => pReified f m ps (advTok ts)
    | .ttOpen => pTripleTerm f m ps (advTok ts)
    | _ => do
      match ← pAtom m ps ts with
      | some r => .ok r
      | none => pErr "expected an RDF term" ts

/-- [39]/[61]/[75] Collection, after `(`, at least one member. -/
def pCollection (fuel : Nat) (m : Mode) (ps : PSt) (acc : List STerm) (ts : TStream) :
    Except ParseError (STerm × PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    if peekTok ts == .rparen && !acc.isEmpty then
      -- link the members: b1 first x1; b1 rest b2; ...; bn rest nil
      let items := acc.reverse
      let (cells, ps1) := items.foldl (fun (cs, p) _ =>
        let (b, p') := p.fresh m
        (cs ++ [b], p')) (([] : List STerm), ps)
      let ps2 := (items.zip cells).zipIdx.foldl (fun p ((x, b), i) =>
        let nxt := cells.getD (i + 1) rdfNilT
        (p.emit ⟨b, rdfFirstT, x⟩).emit ⟨b, rdfRestT, nxt⟩) ps1
      .ok (cells.headD rdfNilT, ps2, advTok ts)
    else do
      let (x, ps1, ts1) ← pGraphNode f m ps ts
      pCollection f m ps1 (x :: acc) ts1

/-- [53] TriplesSameSubjectTemplate / [68] TriplesSameSubjectPattern /
[30] TriplesSameSubjectData. -/
def pTSS (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .lbracket =>
        if peekTok (advTok ts) == .rbracket then
          let (b, ps1) := ps.fresh m
          pPLNE f m ps1 b (advTok (advTok ts))
        else do
          let (b, ps1, ts1) ← pGraphNode f m ps ts
          if startsVerb m (peekTok ts1) then pPLNE f m ps1 b ts1 else .ok (ps1, ts1)
    | .lparen =>
        if peekTok (advTok ts) == .rparen then
          pPLNE f m ps rdfNilT (advTok (advTok ts))
        else do
          let (b, ps1, ts1) ← pCollection f m ps [] (advTok ts)
          if startsVerb m (peekTok ts1) then pPLNE f m ps1 b ts1 else .ok (ps1, ts1)
    | .ttBareOpen => do
        let (r, ps1, ts1) ← pReified f m ps (advTok ts)
        if startsVerb m (peekTok ts1) then pPLNE f m ps1 r ts1 else .ok (ps1, ts1)
    | .ttOpen => do
        let (t, ps1, ts1) ← pTripleTerm f m ps (advTok ts)
        pPLNE f m ps1 t ts1
    | _ => do
        match ← pAtom m ps ts with
        | some (s, ps1, ts1) => pPLNE f m ps1 s ts1
        | none => pErr "expected a triple" ts

/-- [32]/[55]/[70] PropertyListNotEmpty. -/
def pPLNE (fuel : Nat) (m : Mode) (ps : PSt) (subj : STerm) (ts : TStream) :
    Except ParseError (PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 => do
    let (v, ts1) ← pVerb f m ps ts
    let (ps2, ts2) ← pObjectList f m ps subj v ts1
    pPLRest f m ps2 subj ts2

/-- `( ';' ( Verb ObjectList )? )*`. -/
def pPLRest (fuel : Nat) (m : Mode) (ps : PSt) (subj : STerm) (ts : TStream) :
    Except ParseError (PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    if peekTok ts == .semi then
      let ts1 := advTok ts
      if startsVerb m (peekTok ts1) then do
        let (v, ts2) ← pVerb f m ps ts1
        let (ps3, ts3) ← pObjectList f m ps subj v ts2
        pPLRest f m ps3 subj ts3
      else pPLRest f m ps subj ts1
    else .ok (ps, ts)

/-- A verb: [33] VerbData, [87] Verb, or [70] `VerbPath | Var`. -/
def pVerb (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (VerbR × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    match m, peekTok ts with
    | .pattern, .var v => .ok (.simple (.var v), advTok ts)
    | .pattern, _ => do
        let (p, ts1) ← pPath f ps ts
        match p with
        | .pred t => .ok (.simple t, ts1)
        | q => .ok (.path q, ts1)
    | _, _ => do
        let (p, ts1) ← pSimpleVerb m ps ts
        .ok (.simple p, ts1)

/-- [34]/[56]/[71] ObjectList. -/
def pObjectList (fuel : Nat) (m : Mode) (ps : PSt) (subj : STerm) (v : VerbR) (ts : TStream) :
    Except ParseError (PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 => do
    let (o, ps1, ts1) ← pGraphNode f m ps ts
    let ps2 := emitObject ps1 subj v o
    let (ps3, ts3) ← pAnnotation f m ps2 subj v o none ts1
    if peekTok ts3 == .comma then pObjectList f m ps3 subj v (advTok ts3)
    else .ok (ps3, ts3)

/-- [40]/[62]/[76] Annotation: `( Reifier | AnnotationBlock )*`. `pending` is
a reifier not yet used by an annotation block. -/
def pAnnotation (fuel : Nat) (m : Mode) (ps : PSt) (s : STerm) (v : VerbR) (o : STerm)
    (pending : Option STerm) (ts : TStream) : Except ParseError (PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    | .tilde | .annotOpen =>
      match v with
      | .path _ => pErr "an annotation needs a simple predicate, not a path" ts
      | .simple p =>
        let tt := STerm.triple s p o
        if peekTok ts == .tilde then do
          let (r, ps1, ts1) ←
            match ← pReifierId m ps (advTok ts) with
            | some x => pure x
            | none => let (r, ps') := ps.fresh m; pure (r, ps', advTok ts)
          pAnnotation f m (ps1.emit ⟨r, rdfReifiesT, tt⟩) s v o (some r) ts1
        else do
          let (r, ps1) :=
            match pending with
            | some r => (r, ps)
            | none =>
                let (r, ps') := ps.fresh m
                (r, ps'.emit ⟨r, rdfReifiesT, tt⟩)
          let (ps2, ts2) ← pPLNE f m ps1 r (advTok ts)
          if peekTok ts2 == .annotClose then pAnnotation f m ps2 s v o none (advTok ts2)
          else pErr "expected '|}'" ts2
    | _ => .ok (ps, ts)

/-- [29] DataTriplesBlock / [52] TriplesBlockTemplate / [66] TriplesBlockPattern. -/
def pTriplesBlock (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 => do
    let (ps1, ts1) ← pTSS f m ps ts
    if peekTok ts1 == .dot then
      let ts2 := advTok ts1
      if startsTriple (peekTok ts2) then pTriplesBlock f m ps1 ts2 else .ok (ps1, ts2)
    else .ok (ps1, ts1)
end

/-! ## Rule bodies — [14]-[28] -/

/-- Tokens of SPARQL 1.2 expressions that the SPARQL-RL grammar [107]-[125]
does not have. -/
def notSrlExprToken : Token → Bool
  | .exists | .bound | .coalesce | .rand
  | .md5 | .sha1 | .sha256 | .sha384 | .sha512
  | .count | .sum | .minKw | .maxKw | .avg | .sample | .groupConcat => true
  | _ => false

/-- The tokens an expression consumed: `ts` minus its suffix `rest`. -/
def consumed (ts rest : TStream) : List Token :=
  (ts.take (ts.length - rest.length)).map PosToken.tok

def exprVarsOf (toks : List Token) : List String :=
  addVars [] (toks.filterMap fun t => match t with | .var v => some v | _ => none)

/-- The fuel given to each `SPARQL.pExpr` call. -/
def exprFuel : Nat := 10000

/-- `:=` — the tokens `:` and `=`. -/
def colonEq (ts : TStream) : Option TStream :=
  match peekTok ts with
  | .pname ":" => if peekTok (advTok ts) == .eq then some (advTok (advTok ts)) else none
  | _ => none

/-- [16] Filter ::= 'FILTER' Constraint, after `FILTER`. -/
def pFilter (ps : PSt) (ts : TStream) : Except ParseError (Elt × TStream) := do
  match peekTok ts with
  | .var _ | .str _ | .integer _ | .decimal _ | .double _ | .trueKw | .falseKw =>
      pErr "FILTER needs a bracketed expression or a function call" ts
  | _ => pure ()
  let (e, ts1) ← pPrimaryExpr exprFuel ps.pst ts
  let toks := consumed ts ts1
  if toks.any notSrlExprToken then pErr "this SPARQL function is not in SPARQL-RL" ts
  else .ok (.filter e (exprVarsOf toks), ts1)

/-- [21] Assignment ::= 'SET' '(' Var ':=' Expression ')', after `SET`. -/
def pAssign (ps : PSt) (ts : TStream) : Except ParseError (Elt × TStream) := do
  let (_, ts1) ← expectTok .lparen ts
  match peekTok ts1 with
  | .var v =>
    match colonEq (advTok ts1) with
    | none => pErr "expected ':='" (advTok ts1)
    | some ts2 => do
      let (e, ts3) ← pExpr exprFuel ps.pst ts2
      let toks := consumed ts2 ts3
      if toks.any notSrlExprToken then pErr "this SPARQL function is not in SPARQL-RL" ts2
      else
        let (_, ts4) ← expectTok .rparen ts3
        .ok (.assign v e (exprVarsOf toks), ts4)
  | _ => pErr "expected a variable after SET (" ts1

/-- [26] AggregationAssignment ::= Var ':=' AggregationFunction. -/
def pAggAssign (ts : TStream) : Except ParseError ((String × AggFn) × TStream) := do
  match peekTok ts with
  | .var v =>
    match colonEq (advTok ts) with
    | none => pErr "expected ':='" (advTok ts)
    | some ts1 =>
      let fnTok := peekTok ts1
      let (_, ts2) ← expectTok .lparen (advTok ts1)
      match fnTok with
      | .count =>
          let (dist, ts3) := if peekTok ts2 == .distinct then (true, advTok ts2) else (false, ts2)
          let (arg, ts4) ← match peekTok ts3 with
            | .star => pure (none, advTok ts3)
            | .var a => pure (some a, advTok ts3)
            | _ => pErr "expected a variable or '*' in COUNT" ts3
          let (_, ts5) ← expectTok .rparen ts4
          .ok ((v, .count dist arg), ts5)
      | .minKw | .maxKw | .sum =>
          match peekTok ts2 with
          | .var a =>
              let (_, ts3) ← expectTok .rparen (advTok ts2)
              let fn := match fnTok with
                | .minKw => AggFn.min a
                | .maxKw => AggFn.max a
                | _ => AggFn.sum a
              .ok ((v, fn), ts3)
          | _ => pErr "expected a variable in the aggregation function" ts2
      | _ => pErr "expected COUNT, MIN, MAX or SUM" ts1
  | _ => pErr "expected an aggregation assignment" ts

def pAggList (fuel : Nat) (acc : List (String × AggFn)) (ts : TStream) :
    Except ParseError (List (String × AggFn) × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    if peekTok ts == .rbracket && !acc.isEmpty then .ok (acc.reverse, advTok ts)
    else do
      let (a, ts1) ← pAggAssign ts
      pAggList f (a :: acc) ts1

def pVarList (fuel : Nat) (acc : List String) (ts : TStream) : List String × TStream :=
  match fuel, peekTok ts with
  | f + 1, .var v => pVarList f (acc ++ [v]) (advTok ts)
  | _, _ => (acc, ts)

/-- Where a sequence of rule elements sits: a rule body [14], a negation body
[19] (filters only), or a group pattern [23] (filters and assignments). -/
inductive SeqCtx where
  | body
  | neg
  | group
  deriving DecidableEq

/-- A sequence of rule elements up to (not including) the closing `}`.
`triplesOk` says whether a `BodyTriplesBlock` may start here. -/
def pEltSeq (fuel : Nat) (ctx : SeqCtx) (ps : PSt) (acc : List Elt) (triplesOk : Bool)
    (ts : TStream) : Except ParseError (List Elt × PSt × TStream) :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    let tok := peekTok ts
    let skipDot (t : TStream) : TStream := if peekTok t == .dot then advTok t else t
    if triplesOk && startsTriple tok then do
      let (ps1, ts1) ← pTriplesBlock f .pattern { ps with out := #[] } ts
      pEltSeq f ctx { ps1 with out := #[] } (acc ++ ps1.out.toList.map Elt.triple) false ts1
    else
      match tok with
      | .rbrace => .ok (acc, ps, ts)
      | .filterKw => do
          let (e, ts1) ← pFilter ps (advTok ts)
          pEltSeq f ctx ps (acc ++ [e]) true (skipDot ts1)
      | .notKw =>
          if ctx != .body then pErr "NOT is allowed only at the top of a rule body" ts
          else do
            let ts1 := advTok ts
            let (evaldata, ts2) :=
              if peekTok ts1 == .data then (false, advTok ts1) else (true, ts1)
            let (_, ts3) ← expectTok .lbrace ts2
            let (inner, ps4, ts4) ← pEltSeq f .neg ps [] true ts3
            let (_, ts5) ← expectTok .rbrace ts4
            pEltSeq f ctx ps4 (acc ++ [.neg evaldata inner]) true (skipDot ts5)
      | .group =>
          if ctx != .body then pErr "GROUP is allowed only at the top of a rule body" ts
          else do
            let ts1 := advTok ts
            let (keys, ts2) ←
              if peekTok ts1 == .by then
                let (ks, t) := pVarList f [] (advTok ts1)
                if ks.isEmpty then pErr "GROUP BY needs at least one variable" t
                else pure (ks, t)
              else pure ([], ts1)
            let (_, ts3) ← expectTok .lbrace ts2
            let (pat, ps4, ts4) ← pEltSeq f .group ps [] true ts3
            let (_, ts5) ← expectTok .rbrace ts4
            let (_, ts6) ← expectTok .lbracket ts5
            let (aggs, ts7) ←
              if peekTok ts6 == .rbracket then pure ([], advTok ts6)
              else pAggList f [] ts6
            pEltSeq f ctx ps4 (acc ++ [.group keys pat aggs]) true (skipDot ts7)
      | _ =>
          if kwIs tok "SET" then
            if ctx == .neg then pErr "SET is not allowed in NOT" ts
            else do
              let (e, ts1) ← pAssign ps (advTok ts)
              pEltSeq f ctx ps (acc ++ [e]) true (skipDot ts1)
          else pErr "unexpected token in a rule body" ts

/-- `'{' TriplesBlock? '}'` in data or template mode. -/
def pTripleBraces (fuel : Nat) (m : Mode) (ps : PSt) (ts : TStream) :
    Except ParseError (List STriple × PSt × TStream) := do
  let (_, ts1) ← expectTok .lbrace ts
  if peekTok ts1 == .rbrace then .ok ([], ps, advTok ts1)
  else
    let (ps2, ts2) ← pTriplesBlock fuel m { ps with out := #[] } ts1
    let (_, ts3) ← expectTok .rbrace ts2
    .ok (ps2.out.toList, { ps2 with out := #[] }, ts3)

/-- [11] Rule, after `RULE`. -/
def pRule (fuel : Nat) (ps : PSt) (ts : TStream) : Except ParseError (Rule × PSt × TStream) := do
  let (id, ts1) ← match ← iriOf ps ts with
    | some (.iri i, t) => pure (some i.val, t)
    | _ => pure (none, ts)
  let (head, ps2, ts2) ← pTripleBraces fuel .template ps ts1
  let (_, ts3) ← expectTok .whereKw ts2
  let (evaldata, ts4) := if peekTok ts3 == .data then (false, advTok ts3) else (true, ts3)
  let (_, ts5) ← expectTok .lbrace ts4
  let (body, ps6, ts6) ← pEltSeq fuel .body ps2 [] true ts5
  let (_, ts7) ← expectTok .rbrace ts6
  .ok ({ id, head, body, evaldata }, ps6, ts7)

/-- [1]-[10]: the rule set, a sequence of prologue items, rules and data
blocks. -/
def pRuleSet (fuel : Nat) (ps : PSt) (rs : RuleSet) (ts : TStream) :
    Except ParseError RuleSet :=
  match fuel with
  | 0 => pErr "recursion limit" ts
  | f + 1 =>
    let tok := peekTok ts
    match tok with
    | .eof => .ok { rs with rules := rs.rules.reverse }
    | .baseKw =>
        match peekTok (advTok ts) with
        | .iri s => if isIri s then pRuleSet f ps rs (advTok (advTok ts))
                    else pErr "BASE needs an absolute IRI" (advTok ts)
        | _ => pErr "expected an IRI after BASE" (advTok ts)
    | .prefixKw =>
        let ts1 := advTok ts
        match peekTok ts1, peekTok (advTok ts1) with
        | .pname pn, .iri iri =>
            let (pfx, loc) := splitPname pn
            if !isPname pn || loc.length > 0 then pErr "expected PNAME_NS after PREFIX" ts1
            else if !isIri iri then pErr "PREFIX needs an absolute IRI" (advTok ts1)
            else
              let pst := ps.pst
              pRuleSet f { ps with pst := { pst with prefixes := (pfx, iri) :: pst.prefixes } }
                rs (advTok (advTok ts1))
        | _, _ => pErr "expected PNAME_NS IRIREF after PREFIX" ts1
    | .versionKw =>
        match peekTok (advTok ts) with
        | .str _ => pRuleSet f ps rs (advTok (advTok ts))
        | _ => pErr "expected a string after VERSION" (advTok ts)
    | .data => do
        let (ts3, ps3, tsRest) ← pTripleBraces f .data ps (advTok ts)
        pRuleSet f ps3 { rs with data := rs.data ++ ts3 } tsRest
    | _ =>
      if kwIs tok "IMPORTS" then do
        match ← iriOf ps (advTok ts) with
        | some (.iri i, ts1) => pRuleSet f ps { rs with imports := rs.imports ++ [i.val] } ts1
        | _ => pErr "expected an IRI after IMPORTS" (advTok ts)
      else if kwIs tok "RULE" then do
        let (r, ps1, ts1) ← pRule f ps (advTok ts)
        pRuleSet f ps1 { rs with rules := r :: rs.rules } ts1
      else pErr "expected RULE, DATA, PREFIX, BASE, VERSION or IMPORTS" ts

/-- Apply `BASE` to the token stream (see the module header). -/
def resolveBases (base : Option String) (ts : TStream) : TStream :=
  -- state: the base in scope, whether the previous token was BASE, the output
  let step : Option String × Bool × Array PosToken → PosToken →
      Option String × Bool × Array PosToken := fun (b, afterBase, acc) pt =>
    match pt.tok with
    | .baseKw => (b, true, acc.push pt)
    | .iri s =>
        let s' := if isIri s then s else resolveAgainst? b s
        -- the IRI after BASE becomes the base from here on
        ((if afterBase then some s' else b), false, acc.push { pt with tok := .iri s' })
    | _ => (b, false, acc.push pt)
  (ts.foldl step (base, false, #[])).2.2.toList

/-- The position of the end token; the SPARQL tokenizer stops with an end
token at a character it does not know, so an end token before the end of the
text is a lexical error. -/
def lastPos : TStream → Nat
  | [] => 0
  | [pt] => pt.pos
  | _ :: rest => lastPos rest

/-! ## Nesting bound

The grammar's recursion is one frame (a few) per level of bracket nesting:
`[ ]` property lists, `( )` collections and path groups, `<<( )>>` triple
terms, `<< >>` reified triples, `{| |}` annotation blocks, `{ }` blocks.
`parseRuleSet` refuses a document whose brackets nest deeper than
`maxNesting` before the grammar runs, so every recursion over the parsed
terms, paths and rule elements has a constant depth bound (the triple-term
depth of an `STerm` is at most `maxNesting + 1`). The count is over all
bracket tokens, including those of expressions, so it can refuse, never
accept, more than the grammar's own nesting. -/

/-- The deepest bracket nesting a SPARQL-RL document may have. -/
def maxNesting : Nat := 64

def opensLevel : Token → Bool
  | .lbracket | .lparen | .lbrace | .ttOpen | .ttBareOpen | .annotOpen => true
  | _ => false

def closesLevel : Token → Bool
  | .rbracket | .rparen | .rbrace | .ttClose | .ttBareClose | .annotClose => true
  | _ => false

/-- The position of the first token that opens a level deeper than `limit`,
starting at depth `d`; `none` when the nesting stays at most `limit`. A tail
call per token. -/
def nestingExcess (limit : Nat) (d : Nat) : TStream → Option Nat
  | [] => none
  | pt :: rest =>
      if opensLevel pt.tok then
        if d + 1 > limit then some pt.pos else nestingExcess limit (d + 1) rest
      else if closesLevel pt.tok then nestingExcess limit (d - 1) rest
      else nestingExcess limit d rest

/-- Parse a SPARQL-RL document. `base` is the base IRI from outside the
document (the retrieval URL), if any. -/
def parseRuleSet (text : String) (base : Option String := none) :
    Except ParseError RuleSet :=
  let toks := tokenize12 text
  match firstInvalidToken toks with
  | some e => .error e
  | none =>
    if lastPos toks < text.length then .error ⟨"unexpected character", lastPos toks⟩
    else match nestingExcess maxNesting 0 toks with
    | some pos => .error ⟨s!"brackets nest more than {maxNesting} levels", pos⟩
    | none =>
      let toks := resolveBases base toks
      pRuleSet (8 * toks.length + 64) {} {} toks

end L4Factoidal.SPARQLRL
