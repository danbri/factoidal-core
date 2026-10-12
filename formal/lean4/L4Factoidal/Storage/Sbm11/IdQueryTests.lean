/-
L4Factoidal.Storage.Sbm11.IdQueryTests — the FILTER, ORDER BY and printer
shortcuts of the id query path against the reference evaluator (stage 4,
https://github.com/danbri/factoidal/issues/790; record
docs/designissues/2026-10-12-sbm11-stage4.md section 3).

One theorem and sample tests:

  * `ebvOrFalse_evalIn_and`: a FILTER of `a && b` keeps a row exactly when
    the FILTERs of `a` and of `b` both keep it, so the id path evaluates the
    conjuncts one by one.
  * `#guard`s: on sample terms (IRIs, blank nodes, simple, `xsd:string`,
    language-tagged and typed literals, inline and dictionary integers,
    booleans, doubles), each shortcut gives the reference evaluator's answer:
    `=` with an IRI, string or language-tagged constant is term identity;
    the key-byte string tests equal `STRSTARTS` / `STRENDS` / `CONTAINS`;
    the id order of blank nodes and IRIs and the value order of inline
    integers equal `sparqlOrderValue`; the key printer prints `jsonOfTerm`.

A shortcut that disagrees with the reference evaluator on one of these
terms fails the build.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.TermKey
import L4Factoidal.Storage.Sbm11.Dict

namespace L4Factoidal.Storage.Sbm11.IdQueryTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL (Expr EvalEnv Binding ebv ebvOrFalse boolAnd CompOp)
open L4Factoidal.Storage.Sbm11.IdQuery

/-- A FILTER over `a && b` keeps a row exactly when both conjuncts do. -/
theorem ebvOrFalse_evalIn_and (env : EvalEnv) (mu : Binding) (a b : Expr) :
    ebvOrFalse (Expr.evalIn env mu (.and a b)) =
      (ebvOrFalse (Expr.evalIn env mu a) && ebvOrFalse (Expr.evalIn env mu b)) := by
  rw [Expr.evalIn]
  unfold ebvOrFalse
  generalize ebv (Expr.evalIn env mu a) = x
  generalize ebv (Expr.evalIn env mu b) = y
  rcases x with _ | ⟨_ | _⟩ <;> rcases y with _ | ⟨_ | _⟩ <;> rfl

/-! ## Sample terms -/

def xsdT (s : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ s

def lit? (lex dt : String) (lang : Option String) : Option Term :=
  L4Factoidal.Storage.Sbm11.mkLit lex dt lang none

def iri? (s : String) : Option Term :=
  if h : isIri s = true then some (.iri ⟨s, h⟩) else none

/-- Terms as the packer stores them (language tags in lower case). -/
def samples : List Term :=
  ([iri? "http://ex.org/a", iri? "http://ex.org/b", iri? "http://ex.org/aa", iri? "http://ex.org/é",
    some (.bnode "b1"), some (.bnode "b2"),
    lit? "Alice" (xsdT "string") none, lit? "Al" (xsdT "string") none, lit? "" (xsdT "string") none,
    lit? "Alice" rdfLangString.val (some "en"), lit? "Alice" rdfLangString.val (some "fr"),
    lit? "Ali\"ce\n" rdfLangString.val (some "en-gb"),
    lit? "72" (xsdT "int") none, lit? "72" (xsdT "integer") none, lit? "072" (xsdT "integer") none,
    lit? "-3" (xsdT "integer") none, lit? "71" (xsdT "short") none, lit? "72.0" (xsdT "decimal") none,
    lit? "7.2E1" (xsdT "double") none, lit? "true" (xsdT "boolean") none, lit? "1" (xsdT "boolean") none,
    lit? "Alice" "http://ex.org/dt" none, lit? "abc" (xsdT "int") none]).filterMap id

/-- Constants of `=` whose answer is term identity (`eqByTermConst?`). -/
def eqConsts : List Expr :=
  samples.filterMap fun t => match t with
    | .iri i => some (.iri i)
    | .literal l => if l.val.direction.isNone && (l.val.langTag.isSome || l.val.datatype == xsdString)
        then some (.lit l) else none
    | _ => none

def mu (t : Term) : Binding := [("v", t)]

/- `?v = c` and `c = ?v` keep a row exactly when `?v` is the term `c`. -/
#guard eqConsts.all fun c =>
  match eqByTermConst? c with
  | none => false
  | some ct => samples.all fun t =>
      refFilter (.compare .eq (.var "v") c) (mu t) == (t == ct) &&
      refFilter (.compare .eq c (.var "v")) (mu t) == (t == ct)

/- `sameTerm(?v, c)` keeps a row exactly when `?v` is the term `c`, for every
   constant that is not an integer, decimal, double or boolean literal. For
   those the reference evaluator does not give term identity: `Expr.evalIn`
   reads a bound numeric or boolean literal as its value (`literalPromote`),
   and `sameTerm` then answers false for `?v` bound to "72"^^xsd:integer and
   the constant "72"^^xsd:integer, and true for "01"^^xsd:integer against
   "1"^^xsd:integer (W3C sparql10 expr-builtin sameTerm-simple expects 14
   rows; the reference answers 18). The id path answers by id equality, RDF
   term identity (SPARQL 1.1 section 17.4.1.8); record section 3. -/
def promoted (t : Term) : Bool :=
  match t with
  | .literal l => l.val.datatype.val.startsWith "http://www.w3.org/2001/XMLSchema#" &&
      l.val.datatype != xsdString
  | _ => false

#guard (samples.filter (!promoted ·)).all fun ct =>
  match sameTermConst? (match ct with | .iri i => .iri i | .literal l => .lit l | _ => .var "none") with
  | none => (match ct with | .bnode _ => true | _ => false)
  | some c => samples.all fun t =>
      refFilter (.sameTerm (.var "v") (match c with | .iri i => .iri i | .literal l => .lit l | _ => .var "x"))
        (mu t) == (t == c)

def needles : List String := ["A", "Al", "Alice", "ce", "li", "", "\"ce\n", "x"]

def strExpr (k : Nat) (n : String) : Expr :=
  let l : Expr := match lit? n (xsdT "string") none with
    | some (.literal w) => .lit w
    | _ => .var "bad"
  match k with
  | 0 => .strStarts (.var "v") l
  | 1 => .strEnds (.var "v") l
  | _ => .contains (.var "v") l

/- The key-byte string tests equal the reference evaluator wherever they
    answer (keys of class 3 and 4). -/
#guard samples.all fun t =>
  match L4Factoidal.Storage.Sbm11.termKeyBytes? t with
  | none => true
  | some key => needles.all fun n => [0, 1, 2].all fun k =>
      match strTestKey key k n.toUTF8 with
      | some r => r == refFilter (strExpr k n) (mu t)
      | none => key.get! 0 != 3 && key.get! 0 != 4

/- A key of class 3 or 4 starts with `[class] ++ n` (n without 0x00)
    exactly when STRSTARTS of its term and `n` is true: the rank-range test
    of `FKind.strRange`. -/
#guard samples.all fun t =>
  match L4Factoidal.Storage.Sbm11.termKeyBytes? t with
  | none => true
  | some key =>
    if key.get! 0 == 3 || key.get! 0 == 4 then
      needles.all fun n =>
        let p := (ByteArray.mk #[key.get! 0]) ++ n.toUTF8
        let starts := p.size ≤ key.size && key.extract 0 p.size == p
        starts == refFilter (strExpr 0 n) (mu t)
    else true

/- Blank nodes and IRIs: the order of their dictionary keys (class byte,
    then UTF-8) is `sparqlOrderValue`. -/
#guard samples.all fun a => samples.all fun b =>
  match a, b with
  | .iri _, .iri _ | .bnode _, .bnode _ | .iri _, .bnode _ | .bnode _, .iri _ =>
    match L4Factoidal.Storage.Sbm11.termKeyBytes? a, L4Factoidal.Storage.Sbm11.termKeyBytes? b with
    | some ka, some kb =>
      let byKey : Int := match (L4Factoidal.Storage.Sbm11.Dict.cmpBytesAt ka kb : Ordering) with
        | Ordering.lt => -1 | Ordering.eq => 0 | Ordering.gt => 1
      byKey == L4Factoidal.SPARQL.sparqlOrderValue (orderValue a) (orderValue b)
    | _, _ => false
  | _, _ => true

/- Inline integers: bits 55..0 of the id order the values as
    `sparqlOrderValue` does. -/
#guard samples.all fun a => samples.all fun b =>
  match L4Factoidal.Storage.Sbm11.inlineCode? a, L4Factoidal.Storage.Sbm11.inlineCode? b with
  | some x, some y =>
    if x / L4Factoidal.Storage.Sbm11.two60 == L4Factoidal.Storage.Sbm11.tagInt &&
        y / L4Factoidal.Storage.Sbm11.two60 == L4Factoidal.Storage.Sbm11.tagInt then
      let kx := x % L4Factoidal.Storage.Sbm11.two56
      let ky := y % L4Factoidal.Storage.Sbm11.two56
      let byKey : Int := if kx < ky then -1 else if kx == ky then 0 else 1
      byKey == L4Factoidal.SPARQL.sparqlOrderValue (orderValue a) (orderValue b)
    else true
  | _, _ => true

/- The key printer prints what `jsonOfTerm` prints. -/
#guard samples.all fun t =>
  match L4Factoidal.Storage.Sbm11.termKeyBytes? t with
  | none => true
  | some key =>
    match keyJson key ByteArray.empty with
    | some out => out.data == (L4Factoidal.SPARQL.jsonOfTerm t).toString.toUTF8.data
    | none => true

#print axioms ebvOrFalse_evalIn_and

end L4Factoidal.Storage.Sbm11.IdQueryTests
