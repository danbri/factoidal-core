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
    The samples include RDF 1.2 triple terms (dictionary class 7,
    https://github.com/danbri/factoidal/issues/792 item 1): for them `=` with
    such a constant is false, the string tests and the key printer give no
    answer (the reference evaluator and `jsonOfTerm` decide), and a
    triple-term pattern is a constant of the id path only without a variable
    or a blank node inside (`argOfObject`).

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

/-- `<<( s p o )>>` with an IRI subject and predicate. -/
def tt? (s p : String) (o : Option Term) : Option Term :=
  match iri? s, iri? p, o with
  | some (.iri si), some (.iri pi), some ot => some (.tripleTerm (.iri si) pi ot)
  | _, _, _ => none

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
    lit? "Alice" "http://ex.org/dt" none, lit? "abc" (xsdT "int") none,
    tt? "http://ex.org/a" "http://ex.org/p" (iri? "http://ex.org/b"),
    tt? "http://ex.org/a" "http://ex.org/p" (lit? "Alice" rdfLangString.val (some "en")),
    tt? "http://ex.org/a" "http://ex.org/p" (lit? "72" (xsdT "integer") none),
    tt? "http://ex.org/a" "http://ex.org/p"
      (tt? "http://ex.org/b" "http://ex.org/q" (lit? "Alice" (xsdT "string") none)),
    some (.tripleTerm (.bnode "b1") ⟨"http://ex.org/p", rfl⟩ (.bnode "b2"))]).filterMap id

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
  | none => (match ct with | .bnode _ | .tripleTerm _ _ _ => true | _ => false)
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

/- A class-7 key has no shape in the key printer: `appendIdJsonM` prints a
    triple term (tag 9) by `jsonOfTerm` of the decoded term, whose SPARQL 1.2
    JSON form is `"type":"triple"`. -/
#guard samples.all fun t =>
  match t, L4Factoidal.Storage.Sbm11.termKeyBytes? t with
  | .tripleTerm _ _ _, some key =>
    (keyJson key ByteArray.empty).isNone &&
      ((L4Factoidal.SPARQL.jsonOfTerm t).toString.splitOn "\"type\":\"triple\"").length ≥ 2
  | .tripleTerm _ _ _, none => false
  | _, _ => true

/-! ## Triple-term patterns in the object position (`argOfObject`) -/

open L4Factoidal.SPARQL (PatternTerm)

def pIri (s : String) : PatternTerm :=
  if h : isIri s = true then .iri ⟨s, h⟩ else .var "bad"

def argTerm? : Except String Arg → Option Term
  | .ok (.term t) => some t
  | _ => none

def argRefused : Except String Arg → Bool
  | .error _ => true
  | _ => false

-- a ground triple term is the constant it denotes, nested ones too
#guard argTerm? (argOfObject (.tripleTerm (pIri "http://ex.org/a") (pIri "http://ex.org/p")
    (pIri "http://ex.org/b"))) == tt? "http://ex.org/a" "http://ex.org/p" (iri? "http://ex.org/b")
#guard (match lit? "Alice" (xsdT "string") none with
  | some (.literal l) =>
    argTerm? (argOfObject (.tripleTerm (pIri "http://ex.org/a") (pIri "http://ex.org/p")
      (.tripleTerm (pIri "http://ex.org/b") (pIri "http://ex.org/q") (.literal l)))) ==
    tt? "http://ex.org/a" "http://ex.org/p"
      (tt? "http://ex.org/b" "http://ex.org/q" (lit? "Alice" (xsdT "string") none))
  | _ => false)
-- a variable or a blank node anywhere inside, a literal subject, a blank-node
-- subject: refused (the reference evaluator answers)
#guard argRefused (argOfObject (.tripleTerm (pIri "http://ex.org/a") (pIri "http://ex.org/p") (.var "o")))
#guard argRefused (argOfObject (.tripleTerm (.var "s") (pIri "http://ex.org/p") (pIri "http://ex.org/b")))
#guard argRefused (argOfObject (.tripleTerm (pIri "http://ex.org/a") (.var "p") (pIri "http://ex.org/b")))
#guard argRefused (argOfObject (.tripleTerm (.bnode "x") (pIri "http://ex.org/p") (pIri "http://ex.org/b")))
#guard argRefused (argOfObject (.tripleTerm (pIri "http://ex.org/a") (pIri "http://ex.org/p")
    (.tripleTerm (pIri "http://ex.org/b") (pIri "http://ex.org/q") (.var "deep"))))
#guard (match lit? "x" (xsdT "string") none with
  | some (.literal l) =>
    argRefused (argOfObject (.tripleTerm (.literal l) (pIri "http://ex.org/p") (pIri "http://ex.org/b")))
  | _ => false)
-- the subject and predicate positions take no triple term
#guard argRefused (argOfTerm (.tripleTerm (pIri "http://ex.org/a") (pIri "http://ex.org/p")
    (pIri "http://ex.org/b")))
#guard (match argOfSubject (.tripleTerm (pIri "http://ex.org/a") (pIri "http://ex.org/p")
    (pIri "http://ex.org/b")) with | .error _ => true | _ => false)
-- every other object is `argOfTerm`
#guard argTerm? (argOfObject (pIri "http://ex.org/b")) == iri? "http://ex.org/b"

/-! ## `dateCmp`: an `xsd:date` literal compared with a constant on the key
bytes (issue 948, d14) -/

/-- Stored terms for the date comparison: the samples, admitted dates, and
    dates outside the admitted set (timezone, negative year, five-digit year,
    year 0000, a day that does not exist, a leap day, a `dateTime`, another
    datatype). -/
def dateSamples : List Term :=
  samples ++ ([lit? "2020-01-01" (xsdT "date") none, lit? "2021-06-30" (xsdT "date") none,
    lit? "1500-04-23" (xsdT "date") none, lit? "1799-12-31" (xsdT "date") none,
    lit? "1800-01-01" (xsdT "date") none, lit? "0001-01-01" (xsdT "date") none,
    lit? "2000-02-29" (xsdT "date") none, lit? "1999-12-31Z" (xsdT "date") none,
    lit? "1800-01-01+14:00" (xsdT "date") none, lit? "1800-01-01-14:00" (xsdT "date") none,
    lit? "-0044-03-15" (xsdT "date") none, lit? "12020-01-01" (xsdT "date") none,
    lit? "0000-01-01" (xsdT "date") none, lit? "2001-02-29" (xsdT "date") none,
    lit? "2020-13-01" (xsdT "date") none, lit? "2020-01-01T10:00:00" (xsdT "dateTime") none,
    lit? "2020-01-01" "http://ex.org/dt" none, lit? "" (xsdT "date") none]).filterMap id

/-- Constants: three admitted dates, then refused ones (timezone, negative
    year, five-digit year, a `dateTime`, an unknown datatype, a number). -/
def dateConsts : List WfLiteral :=
  (([lit? "2020-06-01" (xsdT "date") none, lit? "1800-01-01" (xsdT "date") none,
    lit? "2000-02-29" (xsdT "date") none,
    lit? "1800-01-01Z" (xsdT "date") none, lit? "-0044-03-15" (xsdT "date") none,
    lit? "12020-01-01" (xsdT "date") none, lit? "2020-01-01T10:00:00" (xsdT "dateTime") none,
    lit? "2020-01-01" "http://ex.org/dt" none, lit? "72" (xsdT "integer") none]).filterMap id).filterMap
    fun t => match t with | .literal l => some l | _ => none

def dateExpr (op : CompOp) (swap : Bool) (c : WfLiteral) : Expr :=
  if swap then .compare op (.lit c) (.var "v") else .compare op (.var "v") (.lit c)

def relOps : List CompOp := [.lt, .gt, .le, .ge]

/- Wherever the compiled conjunct answers on a stored key, the answer is the
   reference evaluator's (the theorem is
   `DateKeyFilterTheorems.dateCmp_fast_eq_ref`; this runs it on the samples). -/
#guard dateConsts.all fun c => relOps.all fun op => [false, true].all fun swap =>
  match dateCmpOf? (dateExpr op swap c) with
  | some (.dateCmp v o sw pre kc e) => dateSamples.all fun t =>
    match L4Factoidal.Storage.Sbm11.termKeyBytes? t with
    | none => true
    | some key =>
      match L4Factoidal.Storage.Sbm11.DateKey.dateCmpKey? o sw pre kc key 0 key.size with
      | some r => v == "v" && r == refFilter e (mu t)
      | none => true
  | _ => true

/- The test decides keys (it is not vacuous): 3 admitted constants, 7 admitted
   stored dates, 4 operators, 2 orders: 168 decided keys. -/
#guard (dateConsts.filter fun c => (L4Factoidal.Storage.Sbm11.DateKey.dateConst? c).isSome).length == 3
#guard (dateConsts.foldl (fun n c => n + relOps.foldl (fun n op => n + [false, true].foldl (fun n swap =>
    match dateCmpOf? (dateExpr op swap c) with
    | some (.dateCmp _ o sw pre kc _) => n + (dateSamples.filter fun t =>
        match L4Factoidal.Storage.Sbm11.termKeyBytes? t with
        | some key => (L4Factoidal.Storage.Sbm11.DateKey.dateCmpKey? o sw pre kc key 0 key.size).isSome
        | none => false).length
    | _ => n) 0) 0) 0) == 168

/- A key outside the admitted set is not decided: a timezone, a negative or
   five-digit year, year 0000, a day that does not exist, another datatype. -/
#guard (match dateConsts[1]? with
  | some c => match L4Factoidal.Storage.Sbm11.DateKey.dateConst? c with
    | some (pre, kc) => ([lit? "1800-01-01+14:00" (xsdT "date") none, lit? "-0044-03-15" (xsdT "date") none,
        lit? "12020-01-01" (xsdT "date") none, lit? "0000-01-01" (xsdT "date") none,
        lit? "2001-02-29" (xsdT "date") none, lit? "2020-01-01" "http://ex.org/dt" none].filterMap id).all
        fun t => match L4Factoidal.Storage.Sbm11.termKeyBytes? t with
          | some key => (L4Factoidal.Storage.Sbm11.DateKey.dateCmpKey? .lt false pre kc key 0 key.size).isNone
          | none => false
    | none => false
  | none => false)

/- Two keys on which the lexical order and the XSD order differ, so the key
   bytes must not decide them: `"12020-01-01" < "1800-01-01"` is true in code
   point order and false in the value space; `"1800-01-01Z" > "1800-01-01"` is
   true in code point order, and the value space leaves the pair incomparable
   (no implicit timezone, the +-14:00 window), so the FILTER is false. -/
#guard (match dateConsts[1]?, lit? "12020-01-01" (xsdT "date") none, lit? "1800-01-01Z" (xsdT "date") none with
  | some c, some t1, some t2 =>
    !refFilter (dateExpr .lt false c) (mu t1) && !refFilter (dateExpr .gt false c) (mu t2)
  | _, _, _ => false)

/- `=` and `!=` are not compiled to `dateCmp` (they compare `xsd:date` literals
   by lexical form); the relational operators are, for admitted constants only. -/
#guard dateConsts.all fun c =>
  (dateCmpOf? (dateExpr .eq false c)).isNone && (dateCmpOf? (dateExpr .ne true c)).isNone &&
  (dateCmpOf? (dateExpr .lt false c)).isSome == (L4Factoidal.Storage.Sbm11.DateKey.dateConst? c).isSome &&
  (dateCmpOf? (dateExpr .ge true c)).isSome == (L4Factoidal.Storage.Sbm11.DateKey.dateConst? c).isSome

#print axioms ebvOrFalse_evalIn_and

end L4Factoidal.Storage.Sbm11.IdQueryTests
