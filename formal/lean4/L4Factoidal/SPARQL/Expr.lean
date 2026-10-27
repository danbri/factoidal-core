/-
L4Factoidal.SPARQL.Expr — the SPARQL 1.1 expression language: the
expression AST (§17/§18.2), effective boolean value (§17.2.2), the
value space evaluation returns, and the total evaluator for the §17.4
operator and function library.

Port of `formal/fstar/SPARQL11.Algebra.fst` Part 3 (`expr`, `comp_op`,
`arith_op`, `aggregate_fn`), the `eval_result` value type with
`ebv_checked` / `er_to_term` / `er_to_string` / `er_string_info`, the
scaled-decimal numeric model (`parse_to_scaled`,
`parse_double_to_scaled`, `format_scaled_value`, `format_as_double`,
`numeric_compare`, `value_compare`, `add_scaled`,
`format_numeric_result`), the `fn_*` accessor family, and the
`eval_expr_with_base` / `eval_coalesce_with_base` / `eval_in_with_base`
/ `eval_concat_with_base` evaluator clique.

WHAT THIS FILE IMPLEMENTS (SPARQL 1.1 Query, W3C Rec. 21 March 2013):
  * §17.2.2 effective boolean value — `ebv`, the operand-mapping table
    with the SPARQL 1.2 malformed-lexical error policy (see `ebv`);
  * §17.3 the error-tolerant / error-preserving `&&`, `||`, `!` tables;
  * §17.4.1 functional forms: BOUND, IF, COALESCE, IN, NOT IN, `=`,
    `!=`, `<`, `>`, `<=`, `>=`, sameTerm;
  * §17.4.2 term-accessor / test forms: isIRI, isBlank, isLiteral,
    isNumeric, STR, LANG, DATATYPE, IRI, STRDT, STRLANG, plus the RDF
    1.2 direction family hasLANG, hasLANGDIR, LANGDIR, STRLANGDIR
    (RDF 1.2 Concepts §3.3);
  * §17.4.3 string functions: STRLEN, SUBSTR, UCASE, LCASE, STRSTARTS,
    STRENDS, CONTAINS, STRBEFORE, STRAFTER, CONCAT, ENCODE_FOR_URI,
    langMatches;
  * §17.4.4 numeric functions ABS, ROUND, CEIL, FLOOR and the §17.4.1
    arithmetic operators `+ - * /` over the promoted numeric types;
  * §17.4.5 the xsd:dateTime component accessors YEAR … SECONDS;
  * SPARQL 1.2 triple-term builtins TRIPLE/SUBJECT/PREDICATE/OBJECT/
    isTRIPLE (Query WD §17.4).

ALSO IMPLEMENTED, each as a total function of explicit inputs:
  * §17.4.4.7–11 hash builtins MD5 / SHA1 / SHA256 / SHA384 / SHA512 —
    pure Lean digests (`Crypto/MD5.lean`, `Crypto/SHA1.lean`,
    `Crypto/SHA2.lean`; see `skills/crypto-policy/SKILL.md`, tier 1:
    hashes over public data), lowercase hex, where the F* tree assumes
    them (`assume val hash_*`);
  * §17.4.5.7/8 TIMEZONE and TZ (`dtTimezone`, `dtTz`, ports of the F*
    `dt_timezone`/`dt_tz`);
  * §17.5 XSD constructor functions `xsd:integer` / `decimal` / `float`
    / `double` / `string` / `boolean` and, for any other XSD datatype
    IRI, a typed literal (`evalXsdCast`, port of `eval_xsd_cast`);
  * §17.4.2.9/12/13 BNODE() / BNODE(str) / UUID() / STRUUID() — FRESH
    values derived deterministically from the (row, call-site) freshness
    context the caller injects (`Binding.withFreshnessCtx`, the F*
    `fx_ctx_put` design), so a query's result is reproducible;
    §17.4.4.3 RAND() is the F* tree's fixed `0.5` (a double in [0, 1)),
    stated plainly: not random;
  * §17.4.2.8 IRI()/URI() resolves a relative reference against the
    query's BASE, carried in `EvalEnv.base` (RFC 3986, `Syntax/
    IriResolve.lean`).

WHAT THIS FILE DELIBERATELY DOES NOT EVALUATE (each returns the
constructor-level `EvalResult.error`, which IS an operator's spec
behaviour when it cannot produce a value — never `sorry`, never a
`partial def`):
  * (closed 2026-08-22) `Expr.regex` / `Expr.replace` — REGEX and
    REPLACE (§17.4.3.14/§17.4.3.15) now run on the pure XPath engine
    `L4Factoidal.Regex` (the port of the F* derivative engine; see
    `regexCore` / `replaceCore`).
  * `Expr.existsPat` / `Expr.notExistsPat` — §18.6 EXISTS needs pattern
    evaluation against the active graph and the dataset, which sits
    above expressions. The pattern layer (`Query.lean`,
    `substituteExistentials`) replaces every EXISTS sub-expression by
    its boolean BEFORE an expression reaches this evaluator, exactly as
    the F* `substitute_existentials` does; an EXISTS that reaches this
    layer un-substituted is the error the F* evaluator also returns
    here (`E_Exists _ -> ER_Error`). Design record: `SPARQL/Exists.lean`.
  * `Expr.aggregate` — aggregates are evaluated in the §18.5.1
    aggregation context over a solution GROUP, not per solution
    mapping. The F* arm is `E_Aggregate _ _ _ -> ER_Error` for exactly
    this reason; the port keeps that.
  * `Expr.now` — §17.4.5.1 reads a clock. Modelled purely: the
    timestamp is an INPUT, `EvalEnv.now`; with none supplied the result
    is an error rather than an ambient effect.
  * §17.6 extension functions and every unrecognised `functionCall`
    IRI — offered to `EvalEnv.ext`; an unregistered IRI is a type
    error, which is precisely what §17.6 requires.

DEVIATIONS FROM THE F* SOURCE, each one the W3C expected file's side
(the F* runner's row comparison, `bin/w3c-runner/w3c_runner.ml`
`binding_row_matches_with`, ignores an actual binding the expected row
lacks, which hides these in the F* scores; this port's harness does
not):
  * STRDT's first argument must be a simple / `xsd:string` literal
    (§17.4.2.3; W3C `strdt01`/`strdt03`); the F* accepts any value.
  * IF propagates a type error in its condition (§17.4.1.2; W3C
    `if02`); the F* folds the error to `false`.
  * CONCAT, STRBEFORE and STRAFTER require STRING literal arguments
    (§17.4.3.1 argument compatibility; W3C `concat02`,
    `strbefore01a`, `strafter01a`); the F* accepts promoted numbers.
  * STRBEFORE/STRAFTER: a simple-literal first argument with a
    language-tagged second argument is NOT compatible (§17.4.3.1 lists
    exactly three compatible pairs; W3C `strbefore02`/`strafter02`);
    the F* compatibility predicate has a fourth, permissive clause.
  * `xsd:decimal` of a STRING requires an xsd:decimal lexical form (no
    exponent; W3C `cast-decimal` rows `s03`, `s07`, `s10`); the F*
    accepts E-notation strings there.

Readability contract (as elsewhere in this port): every definition
cites the spec section it implements, and names track the spec's
vocabulary rather than implementation jargon.
-/
import L4Factoidal.RDF.TermIdentity
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.Fn.String
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.MD5
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Regex.XPath
import L4Factoidal.XSD.Datatypes
import L4Factoidal.Regex.Profiles
import L4Factoidal.XSD.Lexical
import L4Factoidal.Fn.Comparison
import L4Factoidal.Fn.Numeric
import L4Factoidal.Fn.Cast
import L4Factoidal.Fn.Arithmetic
import L4Factoidal.Fn.NumericUnary
import L4Factoidal.Fn.String

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Datatype IRIs this file needs beyond `RDF.Core`'s set -/

/-- `xsd:float` — in `is_numeric_datatype`'s set alongside integer,
decimal and double (SPARQL 1.1 §17.1 operand types). -/
def xsdFloat : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#float", rfl⟩

/-- `xsd:dateTime` — the operand type of the §17.4.5 accessors. -/
def xsdDateTime : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTime", rfl⟩

/-- `xsd:date` — compared by value under `=` (the `XsdDateOperations`
extension of the W3C SPARQL tests). -/
def xsdDate : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#date", rfl⟩

/-- `xsd:dayTimeDuration` — the result type of §17.4.5.7 TIMEZONE. -/
def xsdDayTimeDuration : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#dayTimeDuration", rfl⟩

/-- The XML Schema namespace, for §17.5 constructor-function dispatch. -/
def xsdNamespace : String := "http://www.w3.org/2001/XMLSchema#"

/-- The XPath functions namespace the F* evaluator dispatches RAND(),
UUID(), STRUUID() and BNODE() on (the parser maps those keywords to
`functionCall` with these IRIs). -/
def fnNamespace : String := "http://www.w3.org/2005/xpath-functions#"

/-- SPARQL §17.1 includes integer-derived types; lexical validity is separate. -/
abbrev isNumericDatatype := Fn.Numeric.isDatatype

/-! ### The types derived from `xsd:integer`

SPARQL 1.1 §17.1 counts as numeric the "types derived from xsd:integer
and xsd:decimal". XSD 1.1 Part 2 §3.4 has twelve built-in types derived
from `xsd:integer`, and none derived from `xsd:decimal` other than
`xsd:integer` itself.

A value of a derived type is kept as its TERM (`EvalResult.term`), so
DATATYPE, STR, sameTerm and an assignment see the literal as written.
Only the numeric operators read its value, through `numericView`. A
literal whose lexical form is not in the type's lexical space, or whose
value is outside the type's bounds, is ill-typed and has no value: it
stays a term, so a relational operator or arithmetic on it is a type
error. The lexical form is read without whitespace processing (RDF 1.1
Semantics §7, the rule `RDF/Datatypes.lean` applies), so
`" 72"^^xsd:int` is ill-typed.
https://github.com/danbri/factoidal/issues/782 -/

/-- XSD 1.1 Part 2 §3.4.14-§3.4.26: the built-in type a datatype IRI
names, when that type is derived from `xsd:integer`. A direct match on
the IRI: every relational operator on a literal asks this, and
`XSD.builtinOfIri?` searches a list. `NumericDerivedTests` checks this
table against `XSD.derivedFrom` for every built-in. -/
def integerDerivedBuiltinOfIri? : String → Option XSD.Builtin
  | "http://www.w3.org/2001/XMLSchema#long" => some .long
  | "http://www.w3.org/2001/XMLSchema#int" => some .int
  | "http://www.w3.org/2001/XMLSchema#short" => some .short
  | "http://www.w3.org/2001/XMLSchema#byte" => some .byte
  | "http://www.w3.org/2001/XMLSchema#nonNegativeInteger" => some .nonNegativeInteger
  | "http://www.w3.org/2001/XMLSchema#positiveInteger" => some .positiveInteger
  | "http://www.w3.org/2001/XMLSchema#nonPositiveInteger" => some .nonPositiveInteger
  | "http://www.w3.org/2001/XMLSchema#negativeInteger" => some .negativeInteger
  | "http://www.w3.org/2001/XMLSchema#unsignedLong" => some .unsignedLong
  | "http://www.w3.org/2001/XMLSchema#unsignedInt" => some .unsignedInt
  | "http://www.w3.org/2001/XMLSchema#unsignedShort" => some .unsignedShort
  | "http://www.w3.org/2001/XMLSchema#unsignedByte" => some .unsignedByte
  | _ => none

/-- The value of a literal whose datatype is derived from `xsd:integer`:
the §3.4.13 lexical mapping (`XSD.parseIntegerLex`), then the type's
bounds (`XSD.inIntBounds`). `none` for an ill-typed literal and for
every other datatype. -/
def integerDerivedValue? (l : WfLiteral) : Option Int :=
  match integerDerivedBuiltinOfIri? l.val.datatype.val with
  | none => none
  | some b =>
      match XSD.parseIntegerLex l.val.lexicalForm with
      | some i => if XSD.inIntBounds b i then some i else none
      | none => none

/-! ## Well-formed literal builders

`RDF.Core` carries the well-formedness rule `literalWf` in the type of
`WfLiteral`, so every literal an operator CONSTRUCTS has to come with
its proof. These three builders are the only ways this file makes one;
each discharges `literalWf` by kernel computation, so no operator arm
below has to reason about it. (The F* source builds bare records and
lets Z3 discharge the refinement; this is the same obligation, paid
once.) -/

/-- A literal with an explicit datatype. A request for `rdf:langString`
or `rdf:dirLangString` without a language tag is not well-formed, and
falls back to a plain `xsd:string` literal — the same rule the F*
`fn_strdt` applies (§17.4.2.3 STRDT). -/
def mkTypedLiteral (lex : String) (dt : WfIri) : WfLiteral :=
  if h : dt ≠ rdfLangString ∧ dt ≠ rdfDirLangString then
    ⟨{ lexicalForm := lex, datatype := dt, langTag := none, direction := none },
      by simp [literalWf, h.1, h.2]⟩
  else Literal.string lex

/-- A language-tagged literal — §17.4.2.4 STRLANG. -/
def mkLangLiteral (lex tag : String) : WfLiteral := Literal.langString lex tag

/-- A directional language-tagged literal (RDF 1.2 Concepts §3.3) —
SPARQL 1.2 STRLANGDIR. -/
def mkDirLangLiteral (lex tag : String) (d : TextDirection) : WfLiteral :=
  Literal.dirLangString lex tag d

/-! ## Operators — SPARQL 1.1 §17.4.1.7 (comparison) / §17.4.1 (arithmetic) -/

/-- The relational operators `=`, `!=`, `<`, `>`, `<=`, `>=`. -/
inductive CompOp where
  | eq | ne | lt | gt | le | ge
  deriving DecidableEq, Repr

/-- The arithmetic operators `+`, `-`, `*`, `/` (§17.4.1). -/
inductive ArithOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

/-- Set functions (§18.5.1). Carried by the AST so a HAVING/SELECT
expression parses; evaluation belongs to the aggregation context. -/
inductive AggregateFn where
  | count | sum | min | max | avg
  | groupConcat (separator : Option String)
  | sample
  deriving DecidableEq, Repr

/-! ## The expression AST — SPARQL 1.1 §18.2

One constructor per §17 operator or function form, matching the F*
`expr` type constructor for constructor. `existsPat`/`notExistsPat`
carry a `QueryPattern` — the CONCRETE pattern AST, exactly as the F*
`E_Exists : group_graph_pattern -> expr` does — so an EXISTS body is
lowered into the algebra only at evaluation time, under the real
environment and the active graph of its enclosing pattern (§18.6:
"exists(pattern, μ) evaluates substitute(pattern, μ)"). That is why
the expression AST and the query AST (`QueryPattern`, `Query` and the
query-level pieces that carry expressions) form ONE mutual inductive
below: the F* has the same knot in one `type … and …` group. The
query-level types are documented where the F* documents them
(`Query.lean` still holds their accessors and the evaluator); they
live here only because Lean requires a mutual block to be one
declaration. Design record: `SPARQL/Exists.lean`. -/

/-- §13.2 `FROM` / `FROM NAMED`. Carries no expression, so it sits
outside the mutual block. -/
inductive DatasetClause where
  | default (i : WfIri)
  | named   (i : WfIri)

mutual

inductive Expr where
  -- Primary expressions (§18.2)
  | var         (v : VarName)
  | iri         (i : WfIri)
  | lit         (l : WfLiteral)
  | boolLit     (b : Bool)
  | numericLit  (n : Int)            -- xsd:integer literal
  | decimalLit  (s : String)         -- xsd:decimal, lexical form
  | doubleLit   (s : String)         -- xsd:double, lexical form
  -- Arithmetic (§17.4.1)
  | arith       (op : ArithOp) (l r : Expr)
  | unaryMinus  (e : Expr)
  | unaryPlus   (e : Expr)
  -- Comparison (§17.4.1.7)
  | compare     (op : CompOp) (l r : Expr)
  -- Logical connectives (§17.3)
  | and         (l r : Expr)
  | or          (l r : Expr)
  | not         (e : Expr)
  -- Node type tests (§17.4.2)
  | isIri       (e : Expr)
  | isBlank     (e : Expr)
  | isLiteral   (e : Expr)
  | isNumeric   (e : Expr)
  -- Accessors (§17.4.2)
  | str         (e : Expr)
  | lang        (e : Expr)
  | datatype    (e : Expr)
  | iriFn       (e : Expr)           -- IRI() / URI()
  -- RDF 1.2 base-direction accessors (RDF 1.2 Concepts §3.3)
  | hasLang     (e : Expr)
  | hasLangDir  (e : Expr)
  | langDir     (e : Expr)
  -- Term constructors (§17.4.2)
  | strDt       (lex dt : Expr)
  | strLang     (lex tag : Expr)
  | strLangDir  (lex tag dir : Expr)
  -- BOUND (§17.4.1.1)
  | bound       (v : VarName)
  -- Functional forms (§17.4.1)
  | cond        (c t e : Expr)       -- IF(c, t, e)
  | coalesce    (es : List Expr)
  | inList      (e : Expr) (es : List Expr)
  | notInList   (e : Expr) (es : List Expr)
  -- String functions (§17.4.3)
  | strLen      (e : Expr)
  | substr      (e start : Expr) (len : Option Expr)
  | uCase       (e : Expr)
  | lCase       (e : Expr)
  | strStarts   (e pre : Expr)
  | strEnds     (e suf : Expr)
  | contains    (e sub : Expr)
  | strBefore   (e sep : Expr)
  | strAfter    (e sep : Expr)
  | concat      (es : List Expr)
  | encodeForUri (e : Expr)
  | replace     (e pat rep : Expr) (flags : Option Expr)   -- §17.4.3.15
  | regex       (e pat : Expr) (flags : Option Expr)       -- §17.4.3.14
  -- Numeric functions (§17.4.4)
  | abs         (e : Expr)
  | round       (e : Expr)
  | ceil        (e : Expr)
  | floor       (e : Expr)
  -- Hash functions (§17.4.4.7–11)
  | md5         (e : Expr)
  | sha1        (e : Expr)
  | sha256      (e : Expr)
  | sha384      (e : Expr)
  | sha512      (e : Expr)
  -- Date/time functions (§17.4.5)
  | now
  | year        (e : Expr)
  | month       (e : Expr)
  | day         (e : Expr)
  | hours       (e : Expr)
  | minutes     (e : Expr)
  | seconds     (e : Expr)
  | timezone    (e : Expr)
  | tz          (e : Expr)
  -- RDF term identity (§17.4.1.2)
  | sameTerm    (l r : Expr)
  -- EXISTS / NOT EXISTS (§18.6) — the body is the concrete pattern AST
  | existsPat    (p : QueryPattern)
  | notExistsPat (p : QueryPattern)
  -- Aggregates (§18.5.1) — evaluated over a group, not a solution
  | aggregate   (fn : AggregateFn) (distinct : Bool) (e : Expr)
  -- IRI-named function call (§17.6 extension point)
  | functionCall (i : WfIri) (args : List Expr)
  -- SPARQL 1.2 triple-term builtins (Query WD §17.4)
  | tripleTerm  (s p o : Expr)
  | ttSubject   (e : Expr)
  | ttPredicate (e : Expr)
  | ttObject    (e : Expr)
  | isTriple    (e : Expr)

/-- A SELECT projection item: a bare variable, or `(expr AS ?v)`
(§18.2.4). -/
inductive SelectItem where
  | var  (v : VarName)
  | expr (e : Expr) (v : VarName)

/-- `SELECT ?a ?b` versus `SELECT *`. -/
inductive SelectClause where
  | vars (items : List SelectItem)
  | all

/-- §18.2 query forms. `describe terms` lists the IRIs and variables of
the DESCRIBE clause; `DESCRIBE *` is the empty list. The description of
a resource is a policy decision the specification leaves to the query
service (§16.4); `evalDescribe` in `Query.lean` returns the Concise
Bounded Description. The F* source's `QF_Describe` evaluates to the
empty graph. -/
inductive QueryForm where
  | select    (sel : SelectClause)
  | construct (template : List TriplePattern)
  | ask
  | describe  (terms : List PatternTerm)

/-- §15.1 `ORDER BY ASC(e)` / `DESC(e)`. -/
inductive OrderCondition where
  | asc  (e : Expr)
  | desc (e : Expr)

/-- §15 solution modifiers, gathered (port of `solution_modifier`). -/
structure SolutionModifier where
  orderBy  : Option (List OrderCondition) := none
  distinct : Bool := false
  reduced  : Bool := false
  offset   : Option Nat := none
  limit    : Option Nat := none

/-- §18.2.4.1 GROUP BY: a variable, or an expression with an optional
`AS ?alias`. -/
inductive GroupCondition where
  | var  (v : VarName)
  | expr (e : Expr) (alias : Option VarName)

/-- The concrete graph-pattern AST — one constructor per F*
`group_graph_pattern` case (§18.2.2). Lowered into
`SPARQL.GraphPattern` by `QueryPattern.lower` (`Query.lean`). -/
inductive QueryPattern where
  | bgp          (patterns : Bgp)
  | join         (l r : QueryPattern)
  /-- `OPTIONAL { P } FILTER(e)` — LeftJoin(P1, P2, e), §18.5. -/
  | leftJoin     (l r : QueryPattern) (cond : Expr)
  | filter       (cond : Expr) (p : QueryPattern)
  | union        (l r : QueryPattern)
  | minus        (l r : QueryPattern)
  /-- `GRAPH <iri> { P }` / `GRAPH ?g { P }` — §18.6. -/
  | graph        (name : PatternTerm) (p : QueryPattern)
  /-- `P1 LATERAL { P2 }` — correlated evaluation. -/
  | lateral      (l r : QueryPattern)
  /-- `BIND(e AS ?v)` — §18.6. -/
  | bind         (e : Expr) (v : VarName) (p : QueryPattern)
  /-- `VALUES (?x ?y) { (1 2) (3 UNDEF) }` — §10.2. -/
  | values       (vars : List VarName) (rows : List (List (Option Term)))
  /-- `SERVICE [SILENT] <iri> { P }` — Federated Query §2. -/
  | service      (endpoint : WfIri) (silent : Bool) (p : QueryPattern)
  /-- `SERVICE [SILENT] ?v { P }` — variable endpoint. -/
  | serviceVar   (v : VarName) (silent : Bool) (p : QueryPattern)
  /-- A sub-SELECT used as a group graph pattern (§18.2.4). -/
  | subSelect    (q : Query)
  /-- `?s path ?o` — §18.4. -/
  | propertyPath (s : PatternSubject) (path : PropertyPath) (o : PatternTerm)
  /-- The empty group pattern `{}`. -/
  | empty

/-- A complete SPARQL 1.1 query (port of the F* `query` record). It is
an `inductive` rather than a `structure` only because it predates
mutual structures; `mkQuery` and the field accessors in `Query.lean`
restore the record ergonomics.

`base` is the BASE IRI in force for the query (the prologue's `BASE`,
else the document/request IRI the parser was given) — the F* `q_base`
— which §17.4.2.8 IRI() resolves relative references against.
`postValues` is the trailing `VALUES` block a query may carry after
its WHERE clause (§10.2): its rows are JOINed onto the WHERE result. -/
inductive Query where
  | mk (form       : QueryForm)
       (dataset    : List DatasetClause)
       (pattern    : QueryPattern)
       (groupBy    : Option (List GroupCondition))
       (having     : List Expr)
       (modifier   : SolutionModifier)
       (postValues : Option (List Binding))
       (base       : Option String)

end

/-! ## The value space of expression evaluation

Port of the F* `eval_result`. The three numeric constructors exist so
that a value keeps the numeric TYPE it was promoted to (§17.1's
xsd:integer / xsd:decimal / xsd:double lattice) without repeatedly
re-parsing a literal — the promoted-type discipline every operator arm
below has to honour (an operator that only looks at
`term (Term.literal _)` and forgets `num`/`dec`/`dbl`/`bool` is the
classic bug this shape is designed to make visible). -/

inductive EvalResult where
  | term  (t : Term)
  | bool  (b : Bool)
  | num   (n : Int)
  | dec   (s : String)
  | dbl   (s : String)
  | error
  deriving DecidableEq, Repr

/-- Shared XSD lexical values for the numeric EBV rows of SPARQL §17.2.2.
    Zero and NaN are false; malformed lexicals have no value. -/
def numericLexicalEbv (dt : WfIri) (s : String) : Option Bool :=
  (Fn.Numeric.lexicalValue? dt s).bind Fn.Numeric.booleanValue?

/-- Effective Boolean Value: the common SPARQL operand table, using the
    SPARQL 1.2 §17.2.3 error policy for malformed lexical forms. SPARQL 1.1
    §17.2.2 instead returns false for malformed booleans/numerics; selecting
    that edition's policy throughout evaluation remains unimplemented.

| argument | EBV |
|---|---|
| xsd:boolean | its value (lexical `true`/`1`) |
| xsd:string / simple literal | false iff the lexical form is empty |
| numeric | false iff the value is `0` (or `NaN` for double) |
| anything else, or a type error | **type error** (`none`) |

A language-tagged literal is "any other argument": the table's String
row is the un-tagged case only, so `ebv` of a `rdf:langString` is a
type error and not `true`. Returning `Option Bool` rather than `Bool`
is what lets §17.3's connectives below stay error-PRESERVING. -/
def ebv : EvalResult → Option Bool
  | .bool b => some b
  | .num n  => some (n ≠ 0)
  | .dec s  => numericLexicalEbv xsdDecimal s
  | .dbl s  => numericLexicalEbv xsdDouble s
  | .term (.literal l) =>
      if l.val.datatype == xsdBoolean then
        XSD.parseBooleanLex l.val.lexicalForm
      else if l.val.datatype == xsdString then
        some (l.val.lexicalForm.length > 0)
      else if isNumericDatatype l.val.datatype then
        numericLexicalEbv l.val.datatype l.val.lexicalForm
      else none
  | .term _ => none
  | .error  => none

/-- §18.5 FILTER treats a type error and `false` alike (the row is
dropped either way), so call sites that only need "does this row
survive" collapse the error here. Call sites that must tell a type
error from a definite `false` — the §17.3 connectives — use `ebv`. -/
def ebvOrFalse (v : EvalResult) : Bool := (ebv v).getD false

/-! ### §17.3 — the error-tolerant, error-preserving truth tables

A determinate `false` operand makes `&&` false even when its
co-operand is a type error (error-TOLERANT); two operands that do not
dominate propagate the error rather than collapsing it
(error-PRESERVING). -/

/-- §17.3 logical-and table. -/
def boolAnd : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- §17.3 logical-or table. -/
def boolOr : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- §17.3 logical-not table: an error stays an error. -/
def boolNot : Option Bool → Option Bool
  | some b => some (!b)
  | none   => none

/-! ### Views over an `EvalResult` -/

/-- The RDF term a value denotes — §18.5 BIND / SELECT projection needs
this to turn an expression result back into a binding. A type error
denotes no term, which is why BIND leaves the variable unbound. Port of
`er_to_term`. -/
def EvalResult.toTerm? : EvalResult → Option Term
  | .term t     => some t
  | .bool true  => some (.literal (mkTypedLiteral "true" xsdBoolean))
  | .bool false => some (.literal (mkTypedLiteral "false" xsdBoolean))
  | .num n      => some (.literal (mkTypedLiteral (toString n) xsdInteger))
  | .dec s      => some (.literal (mkTypedLiteral s xsdDecimal))
  | .dbl s      => some (.literal (mkTypedLiteral s xsdDouble))
  | .error      => none

/-- The string a value presents to a string function (port of
`er_to_string`): a literal's lexical form, an IRI's string, or the
canonical lexical form of a promoted number/boolean. Blank nodes,
triple terms and errors have none. -/
def EvalResult.toString? : EvalResult → Option String
  | .term (.literal l) => some l.val.lexicalForm
  | .term (.iri i)     => some i.val
  | .num n             => some (toString n)
  | .dec s             => some s
  | .dbl s             => some s
  | .bool b            => some (if b then "true" else "false")
  | _                  => none

/-- Lexical form + language tag + datatype, for the string functions
that PRESERVE their argument's metadata (§17.4.3: SUBSTR, UCASE,
LCASE, STRBEFORE, STRAFTER, CONCAT). Port of `er_string_info`. -/
def EvalResult.stringInfo? : EvalResult → Option (String × Option String × WfIri)
  | .term (.literal l) => some (l.val.lexicalForm, l.val.langTag, l.val.datatype)
  | .num n             => some (toString n, none, xsdInteger)
  | .dec s             => some (s, none, xsdDecimal)
  | .dbl s             => some (s, none, xsdDouble)
  | .bool b            => some ((if b then "true" else "false"), none, xsdBoolean)
  | _                  => none

/-- Lexical form + language tag + datatype of a STRING LITERAL only —
a simple literal, an `xsd:string`, an `rdf:langString` or an
`rdf:dirLangString`. §17.4.3.1 "Strings in SPARQL functions" defines
the string functions over exactly these; a promoted number or boolean
is NOT a string literal (W3C `concat02`, `strbefore01a`: `CONCAT(?x,
7)` and `STRBEFORE(7, "b")` are type errors). Every §17.4.3 function
that takes a string literal uses this: STRLEN, SUBSTR, UCASE, LCASE,
STRSTARTS, STRENDS, CONTAINS, STRBEFORE, STRAFTER, ENCODE_FOR_URI,
CONCAT, REGEX and REPLACE. The wider `stringInfo?` (which also takes a
promoted number or boolean) let `STRLEN(1)` and `UCASE(1)` answer
(https://github.com/danbri/factoidal/issues/1036). -/
def EvalResult.stringLiteralInfo? : EvalResult → Option (String × Option String × WfIri)
  | .term (.literal l) =>
      if l.val.datatype == xsdString || l.val.datatype == rdfLangString ||
         l.val.datatype == rdfDirLangString then
        some (l.val.lexicalForm, l.val.langTag, l.val.datatype)
      else none
  | _ => none

/-- SPARQL §17.4.3.13 simple-literal arguments. Numeric/IRI rendering and
    language-tagged strings are not implicit conversions to xsd:string. -/
def EvalResult.simpleLiteral? : EvalResult → Option String
  | .term (.literal l) =>
      if l.val.datatype == xsdString then some l.val.lexicalForm else none
  | _ => none

/-- The base direction a value carries, if any (RDF 1.2 Concepts §3.3).
Kept separate from `stringInfo?` so callers explicitly thread this metadata;
CONCAT and REPLACE currently do. Port of `er_direction`. -/
def EvalResult.direction? : EvalResult → Option TextDirection
  | .term (.literal l) => l.val.direction
  | _                  => none

/-- A simple literal result (`xsd:string`, no tag) — the return shape of
STR, ENCODE_FOR_URI, LANG, LANGDIR. -/
def erString (s : String) : EvalResult := .term (.literal (Literal.string s))

/-- Rebuild a string result carrying its argument's metadata forward
(port of `er_string_preserve`): a language tag survives only on
`rdf:langString`, or on `rdf:dirLangString` when a direction is supplied.
Other datatypes survive; incomplete language metadata degrades to a simple
literal. Existing callers that omit direction retain their old policy. -/
def erStringPreserve (s : String) (lang : Option String) (dt : WfIri)
    (direction : Option TextDirection := none) : EvalResult :=
  match lang with
  | none =>
      if dt != rdfLangString && dt != rdfDirLangString then
        .term (.literal (mkTypedLiteral s dt))
      else erString s
  | some l =>
      if dt == rdfLangString then .term (.literal (mkLangLiteral s l))
      else if dt == rdfDirLangString then
        match direction with
        | some d => .term (.literal (mkDirLangLiteral s l d))
        | none => erString s
      else erString s

/-! ## Integer helpers

The F* source's arithmetic runs on unbounded `int`. Lean's `Int` is the
same; the one place the two languages could silently disagree is the
rounding direction of `/`, so this port never writes `/` on `Int` and
uses the explicit truncate-toward-zero definition instead — the
behaviour of F*'s `op_Division` and of its OCaml extraction. -/

/-- Truncating (toward zero) integer division. -/
def intDivT (a b : Int) : Int :=
  if b = 0 then 0
  else
    let q : Int := ((a.natAbs / b.natAbs : Nat) : Int)
    if (decide (a < 0)) == (decide (b < 0)) then q else -q

/-- `10 ^ n`, as the F* `pow10`. -/
def pow10 : Nat → Int
  | 0 => 1
  | n + 1 => 10 * pow10 n

/-- `pow10` as the core power: `Int.pow` of a non-negative base is one
`Nat.pow` (`lean_nat_pow`, GMP), so no stack frame per digit
(https://github.com/danbri/factoidal/issues/752). -/
def pow10Fast (n : Nat) : Int := 10 ^ n

theorem pow10_eq_pow : ∀ n, pow10 n = 10 ^ n
  | 0     => rfl
  | n + 1 => by rw [pow10, pow10_eq_pow n, Int.pow_succ, Int.mul_comm]

/-- The compiler runs `pow10Fast` wherever the source says `pow10`. -/
@[csimp] theorem pow10_eq_fast : @pow10 = @pow10Fast := by
  funext n; exact pow10_eq_pow n

/-- Three-way integer comparison: `-1`, `0`, `1` (port of `int_compare`). -/
def intCompare (a b : Int) : Int :=
  if a < b then -1 else if a = b then 0 else 1

/-- §17.4.1.7: turn a three-way comparison into the operator's Boolean
(port of `apply_comp_op`). -/
def applyCompOp (cmp : Int) : CompOp → Bool
  | .eq => cmp == 0
  | .ne => cmp != 0
  | .lt => cmp < 0
  | .gt => cmp > 0
  | .le => cmp ≤ 0
  | .ge => cmp ≥ 0

/-! ## String helpers (character-list based, matching the F* source)

Everything works on `String.toList` (codepoints), because the F* tree's
own helpers do and because byte-level operations mis-handle non-ASCII —
an error this project has paid for on the OCaml side. -/

def listIsPrefix : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as1, b :: bs1 => a == b && listIsPrefix as1 bs1

def listContainsSublist (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | h :: t => listIsPrefix needle (h :: t) || listContainsSublist needle t

def strStartsWith (s pre : String) : Bool :=
  listIsPrefix pre.toList s.toList

def strEndsWith (s suffix : String) : Bool :=
  listIsPrefix suffix.toList.reverse s.toList.reverse

def strContains (s sub : String) : Bool :=
  listContainsSublist sub.toList s.toList

/-- Index of the first occurrence of `needle`, as a codepoint offset. -/
def findSubstringPos (needle : List Char) : List Char → Nat → Option Nat
  | [], pos => if needle.isEmpty then some pos else none
  | h :: t, pos =>
      if listIsPrefix needle (h :: t) then some pos
      else findSubstringPos needle t (pos + 1)

/-- §17.4.3.13 STRBEFORE's string part: everything before the first
occurrence, or `""` when there is none. -/
def strBeforeRaw (s arg : String) : String := Fn.String.substringBefore s arg

/-- §17.4.3.14 STRAFTER's string part: everything after the first
occurrence, or `""` when there is none. -/
def strAfterRaw (s arg : String) : String := Fn.String.substringAfter s arg

/-- §17.4.3.3 SUBSTR: "This function corresponds to the XPath
`fn:substring` function" (F&O §5.4.4). The result keeps the characters
at the 1-BASED positions `p` with `start <= p < start + length` (or
`start <= p` with no length). A start below 1 is NOT clamped to 1:
`SUBSTR("12345", 0, 3)` is `"12"`
(https://github.com/danbri/factoidal/issues/1036). -/
def substrSpec (s : String) (start : Int) (len : Option Int) : String :=
  match len with
  | some l => Fn.String.substringFromLen s start l
  | none   => Fn.String.substringFrom s start

/-! ### §17.4.3.15 ENCODE_FOR_URI -/

/-- §17.4.3.15 `ENCODE_FOR_URI` cites F&O §5.4.5 `fn:encode-for-uri`
unchanged, and RIF-DTB 4.7 `func:encode-for-uri` cites the same
function. The percent-encoding, the RFC 3986 unreserved set and the
UTF-8 expansion used to be written out again here; they are
`Fn.String.encodeForUri`, and `Fn/Theorems.lean` holds the theorem
that says so, so a second copy stops the build rather than drifting
in silence. -/
def strEncodeUri (s : String) : String := Fn.String.encodeForUri s
/-! ### §17.4.3.10 langMatches — RFC 4647 basic filtering -/

/-- `langMatches(tag, range)`: `"*"` matches any non-empty tag;
otherwise the tag matches the range exactly or as an extended
sub-tag, comparing case-insensitively (BCP 47 tags are ASCII, so
Lean's `String.toLower` is exact here). Port of
`fn_langMatches_spec`. -/
def fnLangMatches (tag range : String) : Bool := Fn.String.langMatchesBasic tag range

/-! ## The scaled-decimal numeric model — SPARQL 1.1 §17.1 / XSD 1.1

A value is `mantissa / 10 ^ scale`. Every xsd:decimal lexical form and
every FINITE xsd:double lexical form is EXACT in this model, so `=`,
`<` and `+ - *` over them are exact too — the same representation the
F* tree uses (`parse_to_scaled` / `parse_double_to_scaled`), and the
reason `1 = 1.0` and `1 = 1.0E0` decide correctly without floating
point. Consequences worth stating: `INF`/`-INF`/`NaN` have no scaled
value (they parse to `none`, hence a type error), and `/` is
approximated at a fixed 10-digit scale exactly as the F* source does. -/

/-- A number as `mantissa / 10 ^ scale`. -/
structure Scaled where
  mantissa : Int
  scale : Nat
  deriving DecidableEq, Repr

/-- The three numeric types of §17.1's promotion lattice. -/
inductive NumKind where
  | int | dec | dbl
  deriving DecidableEq, Repr

/-- §17.1 numeric type promotion: double dominates decimal dominates
integer (port of `promote_kind`). -/
def promoteKind : NumKind → NumKind → NumKind
  | .dbl, _ | _, .dbl => .dbl
  | .dec, _ | _, .dec => .dec
  | _, _ => .int

/-- XSD integer lexical forms share the datatype parser (§17.1). -/
def parseIntString : String → Option Int := XSD.parseIntegerLex

/-- Exact decimal adapter for the remaining scaled-arithmetic operations.
    XSD owns lexical validation and decimal normalization. -/
def parseToScaled (s : String) : Option Scaled :=
  (XSD.parseDecimalLex s).map (fun d => ⟨d.mantissa, d.scale⟩)

/-- Shared exact scientific-notation parser for legacy scaled arithmetic
    and ORDER BY. This adapter does not implement IEEE rounding; numeric
    comparison uses `Fn.Comparison` instead. -/
def parseDoubleToScaled (s : String) : Option Scaled :=
  (XSD.decimalOrScientific s).map (fun d => ⟨d.mantissa, d.scale⟩)

def makeZeros : Nat → String
  | 0 => ""
  | n + 1 => "0" ++ makeZeros n

def padLeftZeros (s : String) (target : Nat) : String :=
  if s.length ≥ target then s else makeZeros (target - s.length) ++ s

/-- `(67, 1) ↦ "6.7"`, `(2220, 3) ↦ "2.220"` (port of
`format_scaled_value`). -/
def formatScaledValue (value : Int) (scale : Nat) : String :=
  if scale = 0 then toString value
  else
    let absVal : Int := (value.natAbs : Int)
    let p := pow10 scale
    let intPart := intDivT absVal p
    let fracPart := absVal - intPart * p
    let fracStr := padLeftZeros (toString fracPart) scale
    (if value < 0 then "-" else "") ++ toString intPart ++ "." ++ fracStr

def stripTrailingZerosChars (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | _ =>
      let stripped := cs.reverse.dropWhile (fun c => c == '0')
      if stripped.isEmpty then ['0'] else stripped.reverse

/-- Canonicalise an xsd:decimal lexical form, keeping at least one
fraction digit (port of `strip_trailing_decimal_zeros`). -/
def stripTrailingDecimalZeros (s : String) : String :=
  let chars := s.toList
  let beforeDot := chars.takeWhile (fun c => c != '.')
  match chars.dropWhile (fun c => c != '.') with
  | [] => s
  | _ :: frac =>
      String.ofList beforeDot ++ "." ++ String.ofList (stripTrailingZerosChars frac)

/-- Decimal digit count, structurally recursive on an explicit fuel
argument (the fuel starts at `n`, which always exceeds the digit
count). The F* source uses well-founded recursion on `n / 10`; fuel
keeps this port structural, so `#guard` can evaluate it. -/
def countDigitsFuel : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, n => if n < 10 then 1 else 1 + countDigitsFuel n (n / 10)

/-- `countDigitsFuel` with the count in an accumulator, so each step is a
tail call (the digits of a literal in the data;
https://github.com/danbri/factoidal/issues/752). -/
def countDigitsLoop : Nat → Nat → Nat → Nat
  | 0, _, k => k + 1
  | _ + 1, n, k => if n < 10 then k + 1 else countDigitsLoop n (n / 10) (k + 1)

theorem countDigitsLoop_eq (f n k : Nat) :
    countDigitsLoop f n k = k + countDigitsFuel f n := by
  fun_induction countDigitsLoop f n k with
  | case1 n k => simp [countDigitsFuel]
  | case2 f n k h => rw [countDigitsFuel]; simp [h]
  | case3 f n k h ih => rw [countDigitsFuel, ih]; simp [h]; omega

def countDigitsFuelFast (f n : Nat) : Nat := countDigitsLoop f n 0

/-- The compiler runs `countDigitsFuelFast` wherever the source says
`countDigitsFuel`. -/
@[csimp] theorem countDigitsFuel_eq_fast : @countDigitsFuel = @countDigitsFuelFast := by
  funext f n; simp [countDigitsFuelFast, countDigitsLoop_eq]

def countDigits (n : Nat) : Nat := countDigitsFuel n n

/-- xsd:double canonical lexical form: `(32100, 0) ↦ "3.21E4"`,
`(20, 2) ↦ "2.0E-1"` (port of `format_as_double`). -/
def formatAsDouble (value : Int) (scale : Nat) : String :=
  if value = 0 then "0E0"
  else
    let absVal := value.natAbs
    let ndigits := countDigits absVal
    let exp : Int := ((ndigits - 1 : Nat) : Int) - (scale : Int)
    let mantissaStr := formatScaledValue (absVal : Int) (ndigits - 1)
    let stripped := stripTrailingDecimalZeros mantissaStr
    let withDot := if strContains stripped "." then stripped else stripped ++ ".0"
    (if value < 0 then "-" else "") ++ withDot ++ "E" ++ toString exp

/-- Promote a literal to the numeric/boolean result it denotes, so that
comparison sees VALUES rather than lexical forms (port of
`literal_promote`). The `xsd:integer` lexical mapping is the shared
XSD one (§3.4.13 `[\-+]?[0-9]+`, so a leading `+` is admitted and a lone
sign is not). Types derived from `xsd:integer` are NOT promoted here:
they stay terms and `numericView` reads their value. -/
def literalPromote (l : WfLiteral) : EvalResult :=
  if l.val.datatype == xsdInteger then
    match XSD.parseIntegerLex l.val.lexicalForm with
    | some n => .num n
    | none => .term (.literal l)
  else if l.val.datatype == xsdDecimal then .dec l.val.lexicalForm
  else if l.val.datatype == xsdDouble || l.val.datatype == xsdFloat then
    .dbl l.val.lexicalForm
  else if l.val.datatype == xsdBoolean then
    -- Valid lexical forms only, like the integer arm above: an
    -- ill-formed boolean has no value to promote TO, and promoting it
    -- to `false` hid the type error `ebv` must raise (sparql12
    -- `expression/not-not`, the `"z"^^xsd:boolean` row).
    match l.val.lexicalForm with
    | "true" | "1" => .bool true
    | "false" | "0" => .bool false
    | _ => .term (.literal l)
  else .term (.literal l)

/-- The value an operator reads from a literal TERM (SPARQL 1.1 §17.3
operator mapping, §17.1 operand types). A literal of a type derived from
`xsd:integer` with a value becomes its `xsd:integer` value (XPath 3.1
§B.1 type promotion). A literal of `xsd:integer`, `xsd:decimal`,
`xsd:double`, `xsd:float` or `xsd:boolean` whose lexical form has a value
becomes that value, as `literalPromote` gives it. Any other literal, and
an ill-typed one, stays the term: it has no value, and §17.4.1.7
compares it as an RDF term.

The same literal reaches an operator from a variable binding
(`Expr.evalIn` promotes it there) and from the query text (`.lit`, kept
as a term so DATATYPE, STR, sameTerm and an assignment see it as
written). This function gives both the same value: SPARQL 1.1 §4.1.2
makes `72` and `"72"^^xsd:integer` the same term.
https://github.com/danbri/factoidal/issues/784 -/
def literalOperandView (l : WfLiteral) : EvalResult :=
  match integerDerivedValue? l with
  | some i => .num i
  | none =>
      match literalPromote l with
      | .dec s => if (parseToScaled s).isSome then .dec s else .term (.literal l)
      | .dbl s => if (parseDoubleToScaled s).isSome then .dbl s else .term (.literal l)
      | v => v

/-- A literal of a datatype that is neither numeric, nor derived from
`xsd:integer`, nor `xsd:boolean` has no value for the operators: it
stays the term. -/
theorem literalOperandView_of_datatype (l : WfLiteral)
    (hd : integerDerivedBuiltinOfIri? l.val.datatype.val = none)
    (h1 : (l.val.datatype == xsdInteger) = false)
    (h2 : (l.val.datatype == xsdDecimal) = false)
    (h3 : (l.val.datatype == xsdDouble) = false)
    (h4 : (l.val.datatype == xsdFloat) = false)
    (h5 : (l.val.datatype == xsdBoolean) = false) :
    literalOperandView l = .term (.literal l) := by
  have hi : integerDerivedValue? l = none := by simp [integerDerivedValue?, hd]
  simp [literalOperandView, literalPromote, hi, h1, h2, h3, h4, h5]

/-- The five shapes `literalOperandView` returns: the term itself, or a
value; a decimal or double value always has a scaled reading. -/
theorem literalOperandView_cases (l : WfLiteral) :
    literalOperandView l = .term (.literal l) ∨
    (∃ i, literalOperandView l = .num i) ∨
    (∃ s v, literalOperandView l = .dec s ∧ parseToScaled s = some v) ∨
    (∃ s v, literalOperandView l = .dbl s ∧ parseDoubleToScaled s = some v) ∨
    (∃ b, literalOperandView l = .bool b) := by
  have hp : literalPromote l = .term (.literal l) ∨ (∃ n, literalPromote l = .num n) ∨
      (∃ s, literalPromote l = .dec s) ∨ (∃ s, literalPromote l = .dbl s) ∨
      (∃ b, literalPromote l = .bool b) := by
    unfold literalPromote
    split
    · split <;> simp
    · split
      · simp
      · split
        · simp
        · split
          · split <;> simp
          · simp
  unfold literalOperandView
  cases hi : integerDerivedValue? l with
  | some i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | none =>
      simp only
      rcases hp with h | ⟨n, h⟩ | ⟨s, h⟩ | ⟨s, h⟩ | ⟨b, h⟩ <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨n, rfl⟩)
      · cases hs : parseToScaled s with
        | none => exact Or.inl (by simp [hs])
        | some v => exact Or.inr (Or.inr (Or.inl ⟨s, v, by simp [hs], hs⟩))
      · cases hs : parseDoubleToScaled s with
        | none => exact Or.inl (by simp [hs])
        | some v => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, v, by simp [hs], hs⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b, rfl⟩)))

/-- Value operators opt into literal conversion. Term-returning expressions
    and RDF accessors retain the original literal. -/
def EvalResult.promoteLiteral : EvalResult → EvalResult
  | .term (.literal l) => literalPromote l
  | v => v

/-- The scaled value and numeric type a result denotes; `none` for
anything non-numeric (port of `er_to_numeric`). -/
def EvalResult.toNumeric? (v : EvalResult) : Option (Scaled × NumKind) :=
  match v.promoteLiteral with
  | .num n => some (⟨n, 0⟩, .int)
  | .term (.literal l) =>
      match literalOperandView l with
      | .num i => some (⟨i, 0⟩, .int)
      | .dec s => (parseToScaled s).map (fun v => (v, .dec))
      | .dbl s => (parseDoubleToScaled s).map (fun v => (v, .dbl))
      | _ => none
  | .dec s => (parseToScaled s).map (fun v => (v, .dec))
  | .dbl s => (parseDoubleToScaled s).map (fun v => (v, .dbl))
  | _ => none

/-- Three-way comparison of two scaled values, by normalising to the
larger scale (port of `numeric_compare`'s core). -/
def Scaled.cmp (a b : Scaled) : Int :=
  if a.scale ≥ b.scale then
    intCompare a.mantissa (b.mantissa * pow10 (a.scale - b.scale))
  else
    intCompare (a.mantissa * pow10 (b.scale - a.scale)) b.mantissa

/-- Legacy scaled ordering for Query's ORDER BY/MIN/MAX path (port of
    `numeric_compare`). It does not implement IEEE numeric promotion and
    must not be used for expression equality or relational comparisons. -/
def numericCompare (a b : EvalResult) : Option Int :=
  match a.toNumeric?, b.toNumeric? with
  | some (x, _), some (y, _) => some (x.cmp y)
  | _, _ => none

/-- Sum at the larger scale (port of `add_scaled`). -/
def Scaled.add (a b : Scaled) : Scaled :=
  if a.scale ≥ b.scale then
    ⟨a.mantissa + b.mantissa * pow10 (a.scale - b.scale), a.scale⟩
  else
    ⟨a.mantissa * pow10 (b.scale - a.scale) + b.mantissa, b.scale⟩

def Scaled.sub (a b : Scaled) : Scaled :=
  if a.scale ≥ b.scale then
    ⟨a.mantissa - b.mantissa * pow10 (a.scale - b.scale), a.scale⟩
  else
    ⟨a.mantissa * pow10 (b.scale - a.scale) - b.mantissa, b.scale⟩

/-- Exact product: scales add. -/
def Scaled.mul (a b : Scaled) : Scaled :=
  ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩

/-- §17.4.1 `/`: division by zero is a type error, and the quotient is
computed at a fixed extra precision of 10 fraction digits — the F*
source's `extra = 10` (exact division is not always representable in
the scaled model). -/
def Scaled.div? (a b : Scaled) : Option Scaled :=
  if b.mantissa = 0 then none
  else
    let extra : Nat := 10
    let extended := a.mantissa * pow10 (b.scale + extra)
    let divisor := b.mantissa * pow10 a.scale
    if divisor = 0 then none
    else some ⟨intDivT extended divisor, extra⟩

/-- Present a scaled result in its promoted type (port of
`format_numeric_result`): an integer result truncates, a decimal
result is canonicalised, a double result goes to E-notation. -/
def formatNumericResult (v : Scaled) : NumKind → EvalResult
  | .int => if v.scale = 0 then .num v.mantissa else .num (intDivT v.mantissa (pow10 v.scale))
  | .dec => .dec (stripTrailingDecimalZeros (formatScaledValue v.mantissa v.scale))
  | .dbl => .dbl (formatAsDouble v.mantissa v.scale)

/-- §17.4.1 integer arithmetic. Note `integer / integer` is an
xsd:DECIMAL, not an integer (port of `eval_arith_int`). -/
def evalArithInt (op : ArithOp) (a b : Int) : EvalResult :=
  match op with
  | .add => .num (a + b)
  | .sub => .num (a - b)
  | .mul => .num (a * b)
  | .div =>
      if b = 0 then .error
      else formatNumericResult
             (⟨intDivT (a * pow10 16) b, 16⟩ : Scaled) .dec

/-! ## §17.4.1.7 value comparison and RDF-term equality -/

/-- §17.1 the value an operand denotes: a literal term is read through
`literalOperandView` (a numeric or boolean literal with a value becomes
that value); every other result is unchanged. The operators apply this
to their operands; nothing else does, so the term itself survives
evaluation. -/
def numericView : EvalResult → EvalResult
  | .term (.literal l) => literalOperandView l
  | v => v

/-- SPARQL §17.3 numeric dispatch includes integer-derived datatypes.
    Invalid forms need the restricted RDF-term fallback, not lexical order. -/
def EvalResult.isNumericOperand : EvalResult → Bool
  | .num _ | .dec _ | .dbl _ => true
  | .term (.literal l) => Fn.Comparison.numericDatatype l.val.datatype
  | _ => false

/-- Preserve bound float versus double before promotion at the common
    operand type. Computed integers need no lexical round trip. -/
def EvalResult.numericValue? : EvalResult → Option XSD.Val
  | .num n => some (.dec (XSD.Dec.ofInt n))
  | .dec s => (XSD.parseDecimalLex s).map XSD.Val.dec
  | .dbl s => XSD.lexicalFor .xsd10 .double s
  | .term (.literal l) => Fn.Numeric.literalValue? l.val
  | _ => none

/-- Result-type selection after shared numeric validation. -/
def EvalResult.isIntegerOperand : EvalResult → Bool
  | .num _ => true
  | .term (.literal l) =>
      (XSD.builtinOfIri? l.val.datatype.val).any (fun b => (XSD.intBounds b).isSome)
  | _ => false

def ArithOp.numericOp : ArithOp → Fn.Arithmetic.Op
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div

/-- Shared XSD numeric result projection. Integer/decimal distinction belongs
    to the expression layer; floating types must survive serialization. -/
def numericResult (integer : Bool) : XSD.Val → EvalResult
  | .dec d => if integer then .num d.mantissa else .dec d.canonical
  | .flt f => .term (.literal (mkTypedLiteral (XSD.canonicalFval f) xsdFloat))
  | .dbl f => .dbl (XSD.canonicalFval f)
  | _ => .error

/-- SPARQL §17.3/§17.4.4 delegates unary operations to F&O numeric values.
    Unary plus validates even though it preserves the value. Result types
    are the base numeric types, including for derived integer operands. -/
def evalNumericUnary (op : Fn.NumericUnary.Op) (v : EvalResult) : EvalResult :=
  match v.numericValue? with
  | none => .error
  | some n =>
      match Fn.NumericUnary.apply op n with
      | some result => numericResult v.isIntegerOperand result
      | none => .error

/-- SPARQL §17.3: validate before promotion and retain floating result types.
    Decimal-only division retains the existing bounded-precision policy.
    Floating output uses XSD's exact round-tripping decimal formatter; shortest
    canonical lexical formatting remains an independent implementation gap. -/
def evalArithmetic (op : ArithOp) (a b : EvalResult) : EvalResult :=
  match a.numericValue?, b.numericValue? with
  | some (.dec x), some (.dec y) =>
      if a.isIntegerOperand && b.isIntegerOperand then evalArithInt op x.mantissa y.mantissa
      else
        match Fn.Arithmetic.decimal 10 op.numericOp x y with
        | some result =>
            -- Preserve the existing expression-layer decimal spelling: an
            -- integral result of fractional arithmetic retains its `.0`.
            let scale := match op with
              | .mul => x.scale + y.scale
              | .div => 10
              | _ => max x.scale y.scale
            formatNumericResult
              ⟨result.mantissa * pow10 (scale - result.scale), scale⟩ .dec
        | none => .error
  | some x, some y =>
      match Fn.Arithmetic.floating op.numericOp x y with
      | some result => numericResult false result
      | none => .error
  | _, _ => .error

/-- `evalArithmetic` with the numeric readings of its operands already made:
`na`/`nb` stand for `numericValue?` and `ia`/`ib` for `isIntegerOperand` of the
two operands. A caller that meets the same operand many times (the SUM and AVG
accumulators of the SBM11 id path, one reading per distinct term id) reads it
once; `evalArithmetic_eq_read` says the result is `evalArithmetic`'s whenever
the readings are those of the operands
(https://github.com/danbri/factoidal/issues/862). -/
def evalArithmeticRead (op : ArithOp) (na nb : Option XSD.Val) (ia ib : Bool) : EvalResult :=
  match na, nb with
  | some (.dec x), some (.dec y) =>
      if ia && ib then evalArithInt op x.mantissa y.mantissa
      else
        match Fn.Arithmetic.decimal 10 op.numericOp x y with
        | some result =>
            let scale := match op with
              | .mul => x.scale + y.scale
              | .div => 10
              | _ => max x.scale y.scale
            formatNumericResult
              ⟨result.mantissa * pow10 (scale - result.scale), scale⟩ .dec
        | none => .error
  | some x, some y =>
      match Fn.Arithmetic.floating op.numericOp x y with
      | some result => numericResult false result
      | none => .error
  | _, _ => .error

/-- The fast form with the operands' own readings is the shared arithmetic. -/
theorem evalArithmetic_eq_read (op : ArithOp) (a b : EvalResult) :
    evalArithmetic op a b =
      evalArithmeticRead op a.numericValue? b.numericValue? a.isIntegerOperand b.isIntegerOperand := by
  unfold evalArithmetic evalArithmeticRead
  rfl

def numericValueCompare (a b : EvalResult) (op : Fn.Comparison.Op) : Option Bool := do
  let x ← a.numericValue?
  let y ← b.numericValue?
  Fn.Comparison.numericCompare x y op

/-- SPARQL §§17.3/17.4.1.7: numeric values take precedence (including NaN),
    but identical ill-typed RDF literals can use RDFterm-equal. Other failed
    numeric comparisons remain errors. Computed invalid values are errors. -/
def numericEquality (a b : EvalResult) (negate : Bool) : Option Bool :=
  match numericValueCompare a b (if negate then .ne else .eq) with
  | some result => some result
  | none => match a, b with
    | .term (.literal x), .term (.literal y) =>
        if x.val.sameTerm y.val then some (!negate) else none
    | _, _ => none

/-- Literal equality that compares numeric literals by VALUE and
everything else by `Literal.valueEqb` (`rdf:XMLLiteral` by canonical
XML, other literals by term equality; port of
`literal_value_eq_numeric`). Value comparison is explicit here: since
https://github.com/danbri/factoidal/issues/963 `Literal.eqb` is term
equality. -/
def literalValueEqNumeric (l1 l2 : WfLiteral) : Bool :=
  if Fn.Comparison.numericDatatype l1.val.datatype || Fn.Comparison.numericDatatype l2.val.datatype then
    (numericEquality (.term (.literal l1)) (.term (.literal l2)) false).getD false
  else l1.val.valueEqb l2.val

/-- RDF 1.2 triple-term VALUE equality, used by `=` (op:triple):
subject and predicate compare structurally, the object recurses and
compares numeric literals by value. Deliberately NOT `sameTerm`:
`<<( :a :b 123 )>> = <<( :a :b 123.0 )>>` holds under `=` but not
under `sameTerm`. Port of `triple_term_value_eq`. -/
def tripleTermValueEq : Term → Term → Bool
  | .iri i1, .iri i2 => i1 == i2
  | .bnode b1, .bnode b2 => b1 == b2
  | .literal l1, .literal l2 => literalValueEqNumeric l1 l2
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
      s1.eqb s2 && p1 == p2 && tripleTermValueEq o1 o2
  | _, _ => false

/-- Lexicographic codepoint comparison of two strings, as three-way
(the F* source's `String.compare`). -/
def listCharCompare : List Char → List Char → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as1, b :: bs1 =>
      let c := intCompare (a.toNat : Int) (b.toNat : Int)
      if c == 0 then listCharCompare as1 bs1 else c

def strCompare (a b : String) : Int := listCharCompare a.toList b.toList

/-! ### The comparison the compiler emits

`strCompare` builds two character lists for every comparison. On
`ORDER BY ?s ?p` over 1,250 paragraphs of `gene.ttl` it is 53.6 percent of
the instructions (`lean_string_data` 36.2, `utf8_decode` 23.6; survey record
`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`, section 8.5).
Every ordering on the query path reaches it: ORDER BY (`sparqlOrder`), the
GROUP BY and DISTINCT-aggregate keys (`erEqual`), MIN and MAX, and the
relational operators on IRIs and literals (`valueCompare`). Lean's order on
`String` is the lexicographic order on code points, the order
`listCharCompare` computes, and its decision procedure is native code
(`String.decidableLT`, `String.decEq`). `listCharCompare_eq_lt` proves the
three-way result equal to the one read off `<` and `=`; the `csimp` theorem
makes every function compiled after this point call `strCompareFast`. The
definition of `strCompare` and every theorem about it do not change. The
same repair was made for RDFC-1.0's `strLe` (`RDF/Canonical.lean`,
`strLe_eq_strLeFast`). -/

/-- `listCharCompare` is the three-way form of Lean's list order. -/
theorem listCharCompare_eq_lt : ∀ (as bs : List Char),
    listCharCompare as bs = if as < bs then -1 else if as = bs then 0 else 1
  | [], [] => by simp [listCharCompare]
  | [], b :: bs => by simp [listCharCompare, List.nil_lt_cons]
  | a :: as, [] => by simp [listCharCompare, List.not_lt_nil]
  | a :: as, b :: bs => by
      have ih := listCharCompare_eq_lt as bs
      have key : (a :: as < b :: bs) ↔ (a < b ∨ a = b ∧ as < bs) := List.cons_lt_cons_iff
      simp only [listCharCompare, intCompare]
      by_cases h1 : a.toNat < b.toNat
      · have hlt : a < b := (UInt32.lt_iff_toNat_lt).2 h1
        have hp : (a :: as < b :: bs) := key.2 (Or.inl hlt)
        have hi : ((a.toNat : Int) < (b.toNat : Int)) := by omega
        simp [hi, hp]
      · by_cases h2 : a = b
        · subst h2
          have hiff : (a :: as < a :: bs) ↔ as < bs := by
            rw [key]; constructor
            · rintro (h | ⟨_, h⟩)
              · exact absurd h (Char.lt_irrefl a)
              · exact h
            · intro h; exact Or.inr ⟨rfl, h⟩
          have hc : ¬ ((a.toNat : Int) < (a.toNat : Int)) := Int.lt_irrefl _
          simp only [hc, if_false, if_true, beq_self_eq_true, hiff, List.cons.injEq, true_and]
          rw [ih]
        · have hgt : b.toNat < a.toNat := by
            have : a.toNat ≠ b.toNat := fun h => h2 (Char.toNat_inj.1 h)
            omega
          have hn : ¬ (a :: as < b :: bs) := by
            rw [key]; rintro (h | ⟨h, _⟩)
            · have : a.toNat < b.toNat := (UInt32.lt_iff_toNat_lt).1 h; omega
            · exact h2 h
          have hi1 : ¬ ((a.toNat : Int) < (b.toNat : Int)) := by omega
          have hi2 : ¬ ((a.toNat : Int) = (b.toNat : Int)) := by omega
          simp [hi1, hi2, hn, h2]

/-- `strCompare` through Lean's native string order and equality. -/
def strCompareFast (a b : String) : Int :=
  if a < b then -1 else if a = b then 0 else 1

theorem strCompare_eq_fast (a b : String) : strCompare a b = strCompareFast a b := by
  unfold strCompare strCompareFast
  rw [listCharCompare_eq_lt]
  have h1 : (a.toList < b.toList) ↔ a < b := Iff.rfl
  have h2 : (a.toList = b.toList) ↔ a = b := String.toList_inj
  simp only [h1, h2]

/-- The compiler calls `strCompareFast` wherever the source says `strCompare`. -/
@[csimp] theorem strCompare_eq_strCompareFast : @strCompare = @strCompareFast :=
  funext fun a => funext fun b => strCompare_eq_fast a b

/-- SPARQL §17.3 relational operations share the XSD/F&O adapter with
    SHACL. Project computed values to their RDF types without promoting away
    the datatype of bound float literals. -/
def relationalCompare (v1 v2 : EvalResult) (op : Fn.Comparison.Op) : Option Bool := do
  let a ← v1.toTerm?
  let b ← v2.toTerm?
  Fn.Comparison.termCompare a b op

/-- The datatypes whose lexical mapping is the identity on lexical forms
    (`xsd:string`; `rdf:langString` and `rdf:dirLangString` with the
    language tag and direction compared apart; RDF 1.1 Concepts 3.3 and 5.1):
    two literals of one of them, with the same language tag and direction,
    have the same value exactly when their lexical forms are the same. -/
def lexicalValueDatatype (dt : WfIri) : Bool :=
  dt == xsdString || dt == rdfLangString || dt == rdfDirLangString

/-- §17.4.1.7 `=` and `!=` of two literals of one datatype with the same
    language tag and direction. The same lexical form is the same RDF term
    (`RDFterm-equal` is true). Different lexical forms: for a datatype of
    `lexicalValueDatatype`, different values; else the value comparison of
    `Fn.Comparison.literalCompare` (`xsd:boolean`, `xsd:dateTime`,
    `xsd:date`); a datatype with no value comparison here (`rdf:XMLLiteral`,
    an unknown datatype), or a lexical form outside the lexical space, is a
    type error (`none`): `RDFterm-equal` "produces a type error if the
    arguments are both literal but are not the same RDF term". Until
    2026-10-23 every datatype compared the lexical forms, so two
    `rdf:XMLLiteral` literals that are different terms were `false` under
    `=` (https://github.com/danbri/factoidal/issues/963). -/
def sameDatatypeLiteralEq (l1 l2 : Literal) (op : CompOp) : Option Bool :=
  if l1.lexicalForm == l2.lexicalForm || lexicalValueDatatype l1.datatype then
    some (applyCompOp (strCompare l1.lexicalForm l2.lexicalForm) op)
  else
    Fn.Comparison.literalCompare l1 l2 (if op == .ne then .ne else .eq)

/-- The lexical form of `l` is in the lexical space of its datatype:
    `Fn.Comparison.literalCompare` reads a value from it (used here for
    `xsd:dateTime` and `xsd:date`). -/
def literalHasComparableValue (l : Literal) : Bool :=
  (Fn.Comparison.literalCompare l l .eq).isSome

/-- `xsd:dateTime` and `xsd:date`, in either order. -/
def dateTimeDatePair (a b : WfIri) : Bool :=
  (a == xsdDateTime && b == xsdDate) || (a == xsdDate && b == xsdDateTime)

/-- §17.4.1.7 RDFterm-equal of two literals that are different RDF terms,
    where no row of the section 17.3 operator table applies. The base rule is
    a type error. The note to section 17.4.1.7 says that RDFterm-equal on
    typed literals "tests for equivalent values" and gives the type error for
    "unsupported datatypes"; section 17.3.1 lets an extension replace a type
    error, and only a type error, with a value. This function gives `false`
    only in the two cases that W3C tests with the manifest requirement
    `mf:KnownTypesDefault2Neq` ("Values in disjoint value spaces are not
    equal") expect:
      * one literal is an `rdf:langString` and the other is not
        (open-world/open-eq-08, -10, -11, -12; these tests expect `false`
        also when the other literal is ill-formed or of an unknown
        datatype);
      * an `xsd:dateTime` and an `xsd:date` literal, both in the lexical
        space (open-world/date-2).
    Every other pair stays a type error (`none`): ill-formed literals,
    unknown datatypes, `rdf:XMLLiteral`
    (https://github.com/danbri/factoidal/issues/963), and pairs such as
    `xsd:integer` and `xsd:boolean` that no W3C test asks about. -/
def distinctLiteralsEq (l1 l2 : Literal) : Option Bool :=
  if (l1.datatype == rdfLangString) != (l2.datatype == rdfLangString) then some false
  else if dateTimeDatePair l1.datatype l2.datatype &&
      literalHasComparableValue l1 && literalHasComparableValue l2 then some false
  else none

/-- §17.4.1.7 RDFterm-equal where the section 17.3 operator table and the
    same-kind arms of `valueCompare` give no answer. Two terms of different
    kinds (IRI, blank node, literal, triple term) are not the same RDF term
    and are not both literals: RDFterm-equal "returns FALSE otherwise". Two
    literals that are different RDF terms: `distinctLiteralsEq`. Two
    literals that are the same RDF term: `none`; the callers have already
    answered that case where the terms come from the data, and a computed
    value that is not in the lexical space stays an error. -/
def rdfTermEqualFallback : Term → Term → Option Bool
  | .literal x, .literal y =>
      if x.val.sameTerm y.val then none else distinctLiteralsEq x.val y.val
  | .literal _, _ => some false
  | _, .literal _ => some false
  | .iri _, .bnode _ => some false
  | .bnode _, .iri _ => some false
  | .iri _, .tripleTerm _ _ _ => some false
  | .tripleTerm _ _ _, .iri _ => some false
  | .bnode _, .tripleTerm _ _ _ => some false
  | .tripleTerm _ _ _, .bnode _ => some false
  | _, _ => none

/-- `=` (`.eq`) or `!=` (any other `op`) by `rdfTermEqualFallback` on the
    RDF terms of two values. An error operand is an error. -/
def termEqualFallback (v1 v2 : EvalResult) (op : CompOp) : Option Bool := do
  let a ← v1.toTerm?
  let b ← v2.toTerm?
  let r ← rdfTermEqualFallback a b
  some (if op == .eq then r else !r)

theorem distinctLiteralsEq_ne_true (a b : Literal) : distinctLiteralsEq a b ≠ some true := by
  unfold distinctLiteralsEq
  split
  · simp
  · split <;> simp

theorem rdfTermEqualFallback_ne_true (a b : Term) : rdfTermEqualFallback a b ≠ some true := by
  cases a <;> cases b <;> simp only [rdfTermEqualFallback] <;> (try split) <;>
    simp [distinctLiteralsEq_ne_true]

/-- The fallback never makes `=` true: read as a FILTER condition
    (`getD false`), it is `false`. -/
theorem termEqualFallback_eq_getD (v1 v2 : EvalResult) :
    (termEqualFallback v1 v2 .eq).getD false = false := by
  unfold termEqualFallback
  cases v1.toTerm? with
  | none => rfl
  | some a =>
    cases v2.toTerm? with
    | none => rfl
    | some b =>
      have hn := rdfTermEqualFallback_ne_true a b
      cases h : rdfTermEqualFallback a b with
      | none => simp [h]
      | some r => cases r <;> simp_all

/-- §17.3/§17.4.1.7 comparison. Numeric equality and relational operations
    share the XSD/F&O value model; other equality uses the RDF fallback.
    This does not equate relational ordering with ORDER BY or sameTerm. -/
def valueCompare (v1 v2 : EvalResult) (op : CompOp) : Option Bool :=
  match op with
  | .lt => relationalCompare v1 v2 .lt
  | .le => relationalCompare v1 v2 .le
  | .gt => relationalCompare v1 v2 .gt
  | .ge => relationalCompare v1 v2 .ge
  | .eq | .ne =>
    if v1.isNumericOperand || v2.isNumericOperand then
      match numericEquality v1 v2 (op == .ne) with
      | some r => some r
      | none => termEqualFallback v1 v2 op
    else
    match v1.promoteLiteral, v2.promoteLiteral with
    | .bool a, .bool b =>
        some (applyCompOp (intCompare (if a then 1 else 0) (if b then 1 else 0)) op)
    | .term (.iri i1), .term (.iri i2) =>
        some (applyCompOp (strCompare i1.val i2.val) op)
    | .term (.literal l1), .term (.literal l2) =>
        if l1.val.datatype == l2.val.datatype then
          if langTagOptionEq l1.val.langTag l2.val.langTag &&
              l1.val.direction == l2.val.direction then
            sameDatatypeLiteralEq l1.val l2.val op
          else
            match op with
            | .eq => some false
            | .ne => some true
            | _ => none
        else termEqualFallback v1 v2 op
    | .term (.bnode a), .term (.bnode b) =>
        match op with
        | .eq => some (a == b)
        | .ne => some (a != b)
        | _ => none
    | .term (.tripleTerm s1 p1 o1), .term (.tripleTerm s2 p2 o2) =>
        match op with
        | .eq => some (tripleTermValueEq (.tripleTerm s1 p1 o1) (.tripleTerm s2 p2 o2))
        | .ne => some (!tripleTermValueEq (.tripleTerm s1 p1 o1) (.tripleTerm s2 p2 o2))
        | _ => none
    | _, _ => termEqualFallback v1 v2 op

/-! ## §17.4.2 node tests and accessors -/

def fnIsIri : EvalResult → EvalResult
  | .term (.iri _) => .bool true
  | .error => .error
  | _ => .bool false

def fnIsBlank : EvalResult → EvalResult
  | .term (.bnode _) => .bool true
  | .error => .error
  | _ => .bool false

def fnIsLiteral : EvalResult → EvalResult
  | .term (.literal _) => .bool true
  | .num _ | .dec _ | .dbl _ | .bool _ => .bool true
  | .error => .error
  | _ => .bool false

def fnIsNumeric : EvalResult → EvalResult
  | .error => .error
  | v => .bool v.numericValue?.isSome

/-- §17.4.2.5 STR. Not defined on a triple term (which is neither
literal nor IRI). -/
def fnStr : EvalResult → EvalResult
  | .term (.iri i) => erString i.val
  | .term (.literal l) => erString l.val.lexicalForm
  | .term (.bnode _) => .error
  | .num n => erString (toString n)
  | .dec s => erString s
  | .dbl s => erString s
  | .bool b => erString (if b then "true" else "false")
  | .term (.tripleTerm _ _ _) => .error
  | .error => .error

/-- §17.4.2.6 LANG: the empty string for an untagged literal, a type
error for a non-literal. -/
def fnLang : EvalResult → EvalResult
  | .term (.literal l) => erString (l.val.langTag.getD "")
  | .num _ | .dec _ | .dbl _ | .bool _ => erString ""
  | _ => .error

/-- §17.4.2.7 DATATYPE. -/
def fnDatatype : EvalResult → EvalResult
  | .term (.literal l) => .term (.iri l.val.datatype)
  | .num _ => .term (.iri xsdInteger)
  | .dec _ => .term (.iri xsdDecimal)
  | .dbl _ => .term (.iri xsdDouble)
  | .bool _ => .term (.iri xsdBoolean)
  | _ => .error

/-- RDF 1.2 `hasLANG(term)` — a presence test over ANY value, so an IRI
argument answers `false` rather than erroring. -/
def fnHasLang : EvalResult → EvalResult
  | .error => .error
  | .term (.literal l) => .bool l.val.langTag.isSome
  | _ => .bool false

/-- RDF 1.2 `hasLANGDIR(term)`. -/
def fnHasLangDir : EvalResult → EvalResult
  | .error => .error
  | .term (.literal l) => .bool l.val.direction.isSome
  | _ => .bool false

def textDirectionToString : TextDirection → String
  | .ltr => "ltr"
  | .rtl => "rtl"

/-- Strict, lowercase-only (RDF 1.2): `STRLANGDIR(_, _, "LTR")` is an
error, matching the W3C lang-basedir fixture. -/
def parseTextDirection (s : String) : Option TextDirection :=
  if s == "ltr" then some .ltr else if s == "rtl" then some .rtl else none

/-- RDF 1.2 `LANGDIR(term)` — mirrors LANG exactly. -/
def fnLangDir : EvalResult → EvalResult
  | .term (.literal l) =>
      erString (match l.val.direction with
                | some d => textDirectionToString d
                | none => "")
  | .num _ | .dec _ | .dbl _ | .bool _ => erString ""
  | _ => .error

/-! ### §17.4.5 xsd:dateTime component accessors

The accessors share the validated XSD value model; SPARQL retains its
own return types and missing-timezone error policy. -/

/-- The xsd:dateTime lexical form behind a value, if it has one. -/
def erToDateTimeLex : EvalResult → Option String
  | .term (.literal l) =>
      if l.val.datatype == xsdDateTime then some l.val.lexicalForm else none
  | _ => none

/-- SPARQL 1.1 §17.4.5 uses XSD 1.0/F&O dateTime values. -/
def dtValue (s : String) : Option XSD.DTValue := XSD.parseDateTimeFor .xsd10 .dateTime s

def dtYear (s : String) : Option Int := (dtValue s).bind (XSD.yearForEdition .xsd10)
def dtMonth (s : String) : Option Int := ((dtValue s).bind (·.month)).map Int.ofNat
def dtDay (s : String) : Option Int := ((dtValue s).bind (·.day)).map Int.ofNat
def dtHours (s : String) : Option Int := ((dtValue s).bind (·.hour)).map Int.ofNat
def dtMinutes (s : String) : Option Int := ((dtValue s).bind (·.minute)).map Int.ofNat

/-- Strip leading zeros from a numeric lexical form, keeping one digit
before a decimal point: `"01" ↦ "1"`, `"00" ↦ "0"`, `"01.5" ↦ "1.5"`,
`"0.5" ↦ "0.5"` (port of `strip_leading_zeros_num`). -/
def stripLeadingZerosNum (s : String) : String :=
  let rec skip : List Char → List Char
    | '0' :: rest =>
        match rest with
        | []       => ['0']
        | c2 :: _  => if c2 == '.' then '0' :: rest else skip rest
    | cs => cs
  match skip s.toList with
  | [] => "0"
  | cs => String.ofList cs

/-- Exact decimal seconds; invalid dateTime lexicals yield a type error. -/
def dtSeconds (s : String) : Option String :=
  ((dtValue s).bind (·.second)).map XSD.Dec.canonical

/-- §17.4.5.7 TIMEZONE: absent timezone remains a caller-visible error. -/
def dtTimezone (s : String) : Option String := do
  let v ← dtValue s
  match v.tz with
  | none => some ""
  | some 0 => some "PT0S"
  | some offset =>
      let h := offset.natAbs / 60
      let m := offset.natAbs % 60
      some ((if offset < 0 then "-" else "") ++ "PT" ++ toString h ++ "H" ++
        (if m == 0 then "" else toString m ++ "M"))

/-- §17.4.5.8 TZ preserves a validated lexical timezone spelling. -/
def dtTz (s : String) : Option String := do
  let v ← dtValue s
  if v.tz.isNone then some ""
  else if s.endsWith "Z" then some "Z"
  else some (String.ofList (s.toList.drop (s.length - 6)))

/-! ## The evaluation environment

The F* evaluator reaches for the host through `assume val`s (a clock,
an extension-function registry, a regex engine). Lean has no
`assume val`, and this project's purity doctrine says the answer is
PARAMETERISATION: what the host would supply becomes an explicit
input, so the semantics stays a total function of its arguments and
real I/O lives in `IO` at the executable edge only. -/

structure EvalEnv where
  /-- §17.6 extension functions: an IRI-named function the host
  registers. Absent (the default) means every unregistered IRI is a
  type error — which is the §17.6 requirement, not a shortcut. -/
  ext : String → List EvalResult → Option EvalResult := fun _ _ => none
  /-- §17.4.5.1 NOW(): the query's execution timestamp as an
  xsd:dateTime lexical form. Read once, at the edge, and passed in —
  never an ambient clock call. -/
  now : Option String := none
  /-- SPARQL 1.1 Federated Query §2 SERVICE: the endpoint IRI → graph
  map. The F* tree reaches the same information through the
  `service_endpoint_lookup` `assume val`; here it is an ordinary input,
  so SERVICE evaluation stays a total function of its arguments. An
  endpoint absent from this list is an unreachable endpoint, which is
  what SILENT is defined against. -/
  services : List (Iri × Graph) := []
  /-- §18.6 EXISTS: the dataset `D` that `exists(pattern, μ)` evaluates
  the substituted pattern against (the F* `eval_exists … ds`
  argument). `evalSelect` / `evalAsk` / `evalConstruct` install the
  query's dataset here (after FROM / FROM NAMED); with none, EXISTS
  is left un-substituted and is the expression-layer error. -/
  dataset : Option Dataset := none
  /-- §17.4.2.8 IRI(): the query's BASE IRI (the prologue's `BASE`, or
  the request/document IRI the parser was given), against which a
  relative reference resolves. The F* evaluator threads this as the
  `base` parameter of `eval_expr_with_base`; here it is an environment
  field. Absent means a non-absolute lexical form is a type error. -/
  base : Option String := none

/-- Resolve a SERVICE endpoint IRI to the graph it serves. -/
def EvalEnv.resolveService (env : EvalEnv) (i : Iri) : Option Graph :=
  match env.services.find? (fun p => p.1 == i) with
  | some p => some p.2
  | none   => none

/-- The environment with no host services and no dataset: extension
functions error, EXISTS errors, NOW errors. -/
def emptyEnv : EvalEnv := {}

/-- The IRI the F* evaluator dispatches `langMatches` on. -/
def langMatchesIri : WfIri :=
  ⟨"http://www.w3.org/2005/xpath-functions#langMatches", rfl⟩

/-! ### CONCAT — §17.4.3.12

CONCAT keeps a language tag (and, RDF 1.2, a base direction) only when
EVERY argument agrees on it; any disagreement drops to `xsd:string`.
The single-argument case is handled explicitly because a fold that
starts from `""` would lose the tag — the recursive-base-case bug this
project has hit before. -/
def concatResults : List EvalResult → EvalResult
  | [] => erString ""
  | [v] =>
      match v.stringLiteralInfo? with
      | none => .error
      | some (s, lang, dt) =>
          match lang, v.direction? with
          | some l1, some d => .term (.literal (mkDirLangLiteral s l1 d))
          | _, _ => erStringPreserve s lang dt
  | v :: rest =>
      match v.stringLiteralInfo? with
      | none => .error
      | some (s, lang, dt) =>
          match concatResults rest with
          | .term (.literal l) =>
              let combined := s ++ l.val.lexicalForm
              match lang, l.val.langTag with
              | some l1, some l2 =>
                  if l1.toLower == l2.toLower then
                    match v.direction?, l.val.direction with
                    | some d1, some d2 =>
                        if d1 == d2 then .term (.literal (mkDirLangLiteral combined l1 d1))
                        else erString combined
                    | none, none => .term (.literal (mkLangLiteral combined l1))
                    | _, _ => erString combined
                  else erString combined
              | none, none =>
                  if dt == l.val.datatype then
                    .term (.literal (mkTypedLiteral combined dt))
                  else erString combined
              | _, _ => erString combined
          | _ => .error

/-- §17.4.3.14 REGEX over the pure XPath engine (`L4Factoidal.Regex`,
the port of the F* derivative engine behind `regex_match`). Arguments:
text (a string literal — simple, xsd:string or language-tagged),
pattern and flags (simple literals). An invalid pattern or flag
(FORX0001/FORX0002) is an expression error. -/
def regexCore (t p f : EvalResult) : EvalResult :=
  match t.stringLiteralInfo?, p.simpleLiteral?, f.simpleLiteral? with
  | some (s, _, _), some pat, some fl =>
      match Regex.Profiles.matchSparql pat fl s with
      | .ok matched => .bool matched
      | .error _ => .error
  | _, _, _ => .error

/-- §17.4.3.15 REPLACE: like REGEX, plus the replacement template
(FORX0003 for a nullable pattern, FORX0004 for a bad template); the
text's language tag, datatype and base direction are kept (`erStringPreserve`). -/
def replaceCore (t p r f : EvalResult) : EvalResult :=
  match t.stringLiteralInfo?, p.simpleLiteral?, r.simpleLiteral?, f.simpleLiteral? with
  | some (s, lg, dt), some pat, some rep, some fl =>
      match Regex.Profiles.replaceSparql pat fl s rep with
      | .ok out => erStringPreserve out lg dt t.direction?
      | .error _ => .error
  | _, _, _, _ => .error

/-- §17.4.3.3 SUBSTR applied to arguments that are already evaluated.
Split out of the evaluator so that each evaluator arm stays a plain
structural match — which is what lets Lean generate the equation
lemmas the proofs in `ExprTheorems` rewrite with. -/
def substrResult (v1 v2 : EvalResult) (vlen : Option EvalResult) : EvalResult :=
  match v1.stringLiteralInfo?, v2.promoteLiteral with
  | some (s, tg, dt), .num start =>
      match vlen.map EvalResult.promoteLiteral with
      | none => erStringPreserve (substrSpec s start none) tg dt v1.direction?
      | some (.num n) => erStringPreserve (substrSpec s start (some n)) tg dt v1.direction?
      | some _ => .error
  | _, _ => .error

/-- §17.4.1.3 COALESCE: the first argument that is not a type error. -/
def coalesceResults : List EvalResult → EvalResult
  | [] => .error
  | .error :: rest => coalesceResults rest
  | v :: _ => v

/-- §17.4.1.9 IN: `=` against each element in turn. Following the F*
source, a comparison that ERRORS is treated as "no match" rather than
poisoning the whole test, so `IN` answers `false` instead of erroring
when nothing matches. -/
def inResults (v : EvalResult) : List EvalResult → EvalResult
  | [] => .bool false
  | w :: rest =>
      match valueCompare v w .eq with
      | some true => .bool true
      | _ => inResults v rest

/-- §17.4.3.1.4 argument compatibility for STRSTARTS, STRENDS,
CONTAINS, STRBEFORE and STRAFTER (both arguments already known to be
string literals, see `stringLiteralInfo?`). The table lists exactly three compatible
pairs: two simple/`xsd:string` literals; two language-tagged literals
with the SAME tag; a language-tagged first argument with a
simple/`xsd:string` second. A simple first argument with a tagged
second is NOT compatible (W3C `strbefore02`: `STRBEFORE("abc",
"b"@cy)` is a type error). -/
def strBeforeAfterCompatible
    (lang1 : Option String) (_dt1 : WfIri)
    (lang2 : Option String) (_dt2 : WfIri) : Bool :=
  match lang1, lang2 with
  | none,    none    => true
  | some _,  none    => true
  | some l1, some l2 => l1 == l2
  | none,    some _  => false

/-- §17.4.3.2 STRLEN over an evaluated argument: a string literal only. -/
def strLenResult (v : EvalResult) : EvalResult :=
  match v.stringLiteralInfo? with
  | some (s, _, _) => .num (s.length : Int)
  | none => .error

/-- §17.4.3.4-5 UCASE / LCASE over an evaluated argument: a string
literal only; the language tag, datatype and base direction are kept. -/
def caseMapResult (f : String → String) (v : EvalResult) : EvalResult :=
  match v.stringLiteralInfo? with
  | some (s, tg, dt) => erStringPreserve (f s) tg dt v.direction?
  | none => .error

/-- §17.4.3.6-8 STRSTARTS / STRENDS / CONTAINS over evaluated
arguments: two string literals that are argument-compatible
(§17.4.3.1.4); otherwise a type error. -/
def strTestResult (test : String → String → Bool) (v1 v2 : EvalResult) : EvalResult :=
  match v1.stringLiteralInfo?, v2.stringLiteralInfo? with
  | some (s, lang1, dt1), some (p, lang2, dt2) =>
      if strBeforeAfterCompatible lang1 dt1 lang2 dt2 then .bool (test s p) else .error
  | _, _ => .error

/-! ## §17.5 XSD constructor functions (casting)

Port of `eval_xsd_cast`, with the XSD lexical-space rule made
explicit: a cast FROM A STRING succeeds only when the lexical form is
in the target datatype's lexical space (XSD 1.1 Part 2 §3.3.13
integer, §3.3.3 decimal, §3.3.5 double, §3.3.2 boolean); a cast from
a NUMBER or BOOLEAN converts the VALUE. The W3C `cast` suite pins
both halves (`xsd:integer("1.5")` is an error, `xsd:integer(1.5)` is
`1`). -/

/-- Drop one leading `+` (numeric lexical forms admit it, results do
not carry it). -/
def stripLeadingPlus (s : String) : String :=
  match s.toList with
  | '+' :: rest => String.ofList rest
  | _ => s

def isDigit (c : Char) : Bool := c.toNat ≥ 48 && c.toNat ≤ 57

/-- XSD integer lexical space: `[+-]?[0-9]+`. -/
def isIntegerLexical (s : String) : Bool := (XSD.parseIntegerLex s).isSome

/-- XSD decimal lexical space: `[+-]?([0-9]+(\.[0-9]*)?|\.[0-9]+)`. -/
def isDecimalLexical (s : String) : Bool := (XSD.parseDecimalLex s).isSome

/-- XSD double/float lexical space: a decimal with an optional
`[Ee][+-]?[0-9]+` exponent, or `INF` / `-INF` / `NaN`.
The existing cast extension accepting `+INF` is retained explicitly; it
differs from the XSD 1.0 adapter used by SHACL and XForms. -/
def isDoubleLexical (s : String) : Bool := (XSD.parseLexical s).isSome

/-- Canonical xsd:decimal lexical form of a decimal lexical: no
leading `+`, a digit before the point, trailing zeros dropped but one
fraction digit kept (`"+33.3300" ↦ "33.33"`, `"0" ↦ "0.0"`). -/
def canonDecimalLexical (s : String) : String :=
  let s1 := stripLeadingPlus s
  let (neg, cs) := match s1.toList with
    | '-' :: rest => (true, rest)
    | cs => (false, cs)
  let intPart := cs.takeWhile (fun c => c != '.')
  let frac := (cs.dropWhile (fun c => c != '.')).drop 1
  let intStr := if intPart.isEmpty then "0"
                else String.ofList (stripLeadingZerosNum (String.ofList intPart)).toList
  let fracStr := String.ofList (stripTrailingZerosChars frac)
  let fracStr := if fracStr.isEmpty then "0" else fracStr
  (if neg then "-" else "") ++ intStr ++ "." ++ fracStr

/-- Decimal lexical form of a scaled value, with at least one fraction
digit (`⟨1, 0⟩ ↦ "1.0"`, `⟨125, 2⟩ ↦ "1.25"`). -/
def scaledToDecimalLexical (v : Scaled) : String :=
  if v.scale = 0 then toString v.mantissa ++ ".0"
  else stripTrailingDecimalZeros (formatScaledValue v.mantissa v.scale)

/-- The lexical form a cast reads: promoted numbers print canonically,
literals and IRIs give their own string; blank nodes and triple terms
have none. -/
def castLexical : EvalResult → Option String
  | .num n => some (toString n)
  | .dec s => some s
  | .dbl s => some s
  | .bool b => some (if b then "true" else "false")
  | .term (.literal l) => some l.val.lexicalForm
  | .term (.iri i) => some i.val
  | _ => none

/-- Candidate result spelling only, checked against the shared cast value.
    `xsd:double(v)`: the F* lexical conventions — a boolean is
`1.0E0`/`0.0E0`, an integer `<n>.0E0`, a decimal or double keeps its
lexical form, a string must be a double lexical form. -/
private def doubleCastSpelling (v : EvalResult) (lex : String) : EvalResult :=
  match v with
  | .bool b => .dbl (if b then "1.0E0" else "0.0E0")
  | .num n => .dbl (toString n ++ ".0E0")
  | .dbl _ | .dec _ => if isDoubleLexical lex then .dbl lex else .error
  | _ => if isDoubleLexical lex then .dbl lex else .error

/-- Candidate result spelling only, checked against the shared cast value.
    `xsd:float(v)`: a typed `xsd:float` literal (no promoted float
kind exists). Lexical conventions follow the F* source (ARQ's, which
the W3C `cast-float` expectation records): boolean `1.0E0`/`0E0`,
integer `0` or `<n>.0`, an integer-VALUED double `0.0`/`<n>.0`,
anything else its own lexical form. -/
private def floatCastSpelling (v : EvalResult) (lex : String) : EvalResult :=
  let mkFloat := fun (s : String) => EvalResult.term (.literal (mkTypedLiteral s xsdFloat))
  match v with
  | .bool b => mkFloat (if b then "1.0E0" else "0E0")
  | .num n => mkFloat (if n = 0 then "0" else toString n ++ ".0")
  | .dbl _ =>
      match parseDoubleToScaled lex with
      | some sv =>
          let p := pow10 sv.scale
          if sv.mantissa % p = 0 then
            let n := intDivT sv.mantissa p
            mkFloat (if n = 0 then "0.0" else toString n ++ ".0")
          else mkFloat lex
      | none => .error
  | .dec _ => if isDecimalLexical lex then mkFloat lex else .error
  | _ => if isDoubleLexical lex then mkFloat lex else .error

/-- Source validation for constructors, before literal promotion can erase
    float precision or the restrictions on derived numeric datatypes. -/
def EvalResult.castValue? : EvalResult → Option XSD.Val
  | .num n => some (.dec (XSD.Dec.ofInt n))
  | .dec s => XSD.checkedLexicalValue .xsd10 .decimal s
  | .dbl s => XSD.checkedLexicalValue .xsd10 .double s
  | .bool b => some (.bool b)
  | .term (.literal l) => do
      let b ← XSD.builtinOfIri? l.val.datatype.val
      XSD.checkedLexicalValue .xsd10 b l.val.lexicalForm
  | _ => none

/-- Shared F&O numeric constructors. Existing expression spellings are kept
    only if reparsing them gives exactly the shared conversion result. The
    historical +INF string extension remains explicit, not a source-type cast. -/
def castNumeric (target : XSD.Builtin) (v : EvalResult) : EvalResult := Id.run do
  let some source := v.castValue? | return .error
  let edition := match source with
    | .str .string s => if (target == .float || target == .double) &&
        XSD.applyWhiteSpace .collapse s == "+INF" then XSD.Edition.xsd11 else .xsd10
    | _ => .xsd10
  let some result := Fn.Cast.cast edition target source | return .error
  let promoted := v.promoteLiteral
  let lex := stripLeadingPlus ((castLexical promoted).getD "")
  let candidate := match target with
    | .double => doubleCastSpelling promoted lex
    | .float => floatCastSpelling promoted lex
    | _ => .error
  if candidate.castValue?.any (XSD.valIdentical result) then return candidate
  match result with
  | .dec d =>
      if target == .integer then
        return (d.toInt?.map EvalResult.num).getD .error
      else return .dec (canonDecimalLexical d.canonical)
  | .flt _ | .dbl _ => return numericResult false result
  | _ => return .error

/-- Compatibility entry points; `lex` is no longer trusted as a source value. -/
def castInteger (v : EvalResult) (_lex : String) := castNumeric .integer v
def castDecimal (v : EvalResult) (_lex : String) := castNumeric .decimal v
def castDouble (v : EvalResult) (_lex : String) := castNumeric .double v
def castFloat (v : EvalResult) (_lex : String) := castNumeric .float v

/-- F&O §17.1.6: Boolean casts share numeric EBV, preserving the source
    float type before rounding. String casts use the target's whitespace
    facet (§17.1.1); unsupported RDF datatypes are not strings. -/
def castBoolean (v : EvalResult) : EvalResult :=
  let result := match v with
    | .bool b => some b
    | .term (.literal l) =>
        if l.val.datatype == xsdBoolean then XSD.parseBooleanLex l.val.lexicalForm
        else if l.val.datatype == xsdString then
          XSD.parseBooleanLex (XSD.applyWhiteSpace .collapse l.val.lexicalForm)
        else v.numericValue?.bind Fn.Numeric.booleanValue?
    | _ => v.numericValue?.bind Fn.Numeric.booleanValue?
  (result.map EvalResult.bool).getD .error

/-- `xsd:string(v)`: a simple literal; an integer-valued decimal or
double prints as its integer (`1.0 ↦ "1"`, `1E0 ↦ "1"`), as in the F*
source. -/
def castString (v : EvalResult) (lex : String) : EvalResult :=
  match v with
  | .dec _ =>
      match parseToScaled lex with
      | some sv =>
          let p := pow10 sv.scale
          if sv.mantissa % p = 0 then erString (toString (intDivT sv.mantissa p)) else erString lex
      | none => erString lex
  | .dbl _ =>
      match parseDoubleToScaled lex with
      | some sv =>
          let p := pow10 sv.scale
          if sv.mantissa % p = 0 then erString (toString (intDivT sv.mantissa p)) else erString lex
      | none => erString lex
  | _ => erString lex

/-- §17.5 / F&O casting to dateTime: in the supported SPARQL type table,
    accept string/simple literals or dateTime values with a valid lexical.
    Reuse the same XSD 1.0 decision as the date component accessors.
    Preserve the input spelling; numeric leading-plus removal does not apply. -/
def castDateTime (v : EvalResult) : EvalResult :=
  match v with
  | .term (.literal l) =>
      if (l.val.datatype == xsdString || l.val.datatype == xsdDateTime) &&
          (dtValue l.val.lexicalForm).isSome then
        .term (.literal (mkTypedLiteral l.val.lexicalForm xsdDateTime))
      else .error
  | _ => .error

/-- §17.5: dispatch `xsd:<targetType>(v)`. Other XSD datatype IRIs retain
the historical typed-literal fallback; their constructor semantics remain a
coverage gap. Language-tagged datatypes are never constructible this way. -/
def evalXsdCast (v : EvalResult) (targetType : String) (fullIri : WfIri) : EvalResult :=
  if targetType == "integer" then castNumeric .integer v else
  if targetType == "decimal" then castNumeric .decimal v else
  if targetType == "double" then castNumeric .double v else
  if targetType == "float" then castNumeric .float v else
  if targetType == "dateTime" then castDateTime v else
  if targetType == "boolean" then castBoolean v else
  let v := v.promoteLiteral
  match castLexical v with
  | none => .error
  | some lex0 =>
      let lex := if targetType == "string" || targetType == "boolean" then lex0
                 else stripLeadingPlus lex0
      if targetType == "string" then castString v lex
      else if fullIri != rdfLangString && fullIri != rdfDirLangString then
        .term (.literal (mkTypedLiteral lex fullIri))
      else .error

/-! ## §17.4.2.9 / §17.4.2.12 / §17.4.2.13 — fresh values, purely

BNODE(), UUID() and STRUUID() must return a value distinct per
solution and per call site. The caller (BIND, the SELECT projection)
injects the row index and a call-site tag under the reserved keys of
`Binding.withFreshnessCtx`; the value is SHA-256 of a seed built from
them, so it is deterministic, reproducible, and distinct wherever the
spec requires distinctness (port of `fx_uuid_of_seed` /
`fx_bnode_of_seed`). -/

/-- The first 32 hex digits of SHA-256(seed) laid out 8-4-4-4-12
(lowercase; the W3C UUID fixtures match case-insensitively). -/
def fxUuidOfSeed (seed : String) : String :=
  let cs := (Crypto.hashHex .sha256 seed).toList.take 32
  let s := fun (l : List Char) => String.ofList l
  s (cs.take 8) ++ "-" ++ s ((cs.drop 8).take 4) ++ "-" ++ s ((cs.drop 12).take 4) ++ "-" ++
  s ((cs.drop 16).take 4) ++ "-" ++ s (cs.drop 20)

/-- A fresh blank-node label; the `fxbn` prefix keeps these apart
from data blank nodes. (The F* label carries a literal `_:` prefix;
Lean blank-node labels never do, so it is omitted here.) -/
def fxBnodeOfSeed (seed : String) : String :=
  "fxbn" ++ Crypto.hashHex .sha256 seed

/-- Hash builtin body shared by MD5/SHA1/SHA256/SHA384/SHA512
(§17.4.6.1–5): the argument is a simple literal or an `xsd:string`;
its UTF-8 bytes are hashed, and the result is a simple literal of
lowercase hex. Any other argument (a number, a language-tagged
literal, an IRI) is a type error
(https://github.com/danbri/factoidal/issues/1036). -/
def hashResult (digest : String → String) (v : EvalResult) : EvalResult :=
  match v.simpleLiteral? with
  | some s => erString (digest s)
  | none => .error

/-! ## The evaluator — SPARQL 1.1 §17

`Expr.evalIn env mu e` is TOTAL: every operator either produces a value
or produces `EvalResult.error`, the spec's type error. There is no
`partial def`, no fuel, and no escape hatch; the recursion is
structural on the expression tree, with `evalArgs` handling the
argument LISTS of COALESCE, IN, NOT IN, CONCAT and function calls. -/

mutual

/-- Evaluate one expression under a solution mapping. Port of
`eval_expr_with_base` (with the BASE-IRI parameter dropped — see the
deviation note on `Expr.iriFn`). -/
def Expr.evalIn (env : EvalEnv) (mu : Binding) : Expr → EvalResult
  -- §18.2 primary expressions preserve RDF terms, including lexical spelling.
  -- Numeric and comparison operators opt into value conversion locally.
  | .var v =>
      match mu.lookup v with
      | some t => .term t
      | none => .error
  | .iri i => .term (.iri i)
  | .lit l => .term (.literal l)
  | .boolLit b => .bool b
  | .numericLit n => .num n
  | .decimalLit s => .dec s
  | .doubleLit s => .dbl s

  -- §17.4.1 arithmetic, with §17.1 numeric promotion.
  | .arith op e1 e2 =>
      evalArithmetic op (Expr.evalIn env mu e1) (Expr.evalIn env mu e2)
  | .unaryMinus e1 => evalNumericUnary .minus (Expr.evalIn env mu e1)
  | .unaryPlus e1 => evalNumericUnary .plus (Expr.evalIn env mu e1)

  -- §17.4.1.7 comparison.
  | .compare op e1 e2 =>
      match valueCompare (Expr.evalIn env mu e1) (Expr.evalIn env mu e2) op with
      | some b => .bool b
      | none => .error

  -- §17.3 connectives: error-tolerant and error-preserving.
  | .and e1 e2 =>
      match boolAnd (ebv (Expr.evalIn env mu e1)) (ebv (Expr.evalIn env mu e2)) with
      | some b => .bool b
      | none => .error
  | .or e1 e2 =>
      match boolOr (ebv (Expr.evalIn env mu e1)) (ebv (Expr.evalIn env mu e2)) with
      | some b => .bool b
      | none => .error
  | .not e1 =>
      match boolNot (ebv (Expr.evalIn env mu e1)) with
      | some b => .bool b
      | none => .error

  -- §17.4.2 node tests.
  | .isIri e1 => fnIsIri (Expr.evalIn env mu e1)
  | .isBlank e1 => fnIsBlank (Expr.evalIn env mu e1)
  | .isLiteral e1 => fnIsLiteral (Expr.evalIn env mu e1)
  | .isNumeric e1 => fnIsNumeric (Expr.evalIn env mu e1)

  -- §17.4.2 accessors.
  | .str e1 => fnStr (Expr.evalIn env mu e1)
  | .lang e1 => fnLang (Expr.evalIn env mu e1)
  | .datatype e1 => fnDatatype (Expr.evalIn env mu e1)
  | .hasLang e1 => fnHasLang (Expr.evalIn env mu e1)
  | .hasLangDir e1 => fnHasLangDir (Expr.evalIn env mu e1)
  | .langDir e1 => fnLangDir (Expr.evalIn env mu e1)
  -- §17.4.2.8 IRI(): a literal's lexical form is resolved against the
  -- query's BASE when there is one (RFC 3986 §5.2, `resolveIri`), as
  -- the F* arm does with `resolve_iri`; the result must be an
  -- absolute IRI.
  | .iriFn e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.iri i) => .term (.iri i)
      | .term (.literal l) =>
          let s := L4Factoidal.Syntax.resolveAgainst? env.base l.val.lexicalForm
          if h : L4Factoidal.RDF.isIri s then .term (.iri ⟨s, h⟩)
          else .error
      | _ => .error

  -- §17.4.2 term constructors. STRDT takes a SIMPLE LITERAL (RDF 1.1:
  -- an `xsd:string` literal without a language tag); a tagged or
  -- otherwise-typed literal, or a promoted value, is a type error
  -- (W3C `strdt01`, `strdt03`).
  | .strDt e1 e2 =>
      match Expr.evalIn env mu e1, Expr.evalIn env mu e2 with
      | .term (.literal l), .term (.iri dt) =>
          if l.val.datatype == xsdString && l.val.langTag.isNone then
            .term (.literal (mkTypedLiteral l.val.lexicalForm dt))
          else .error
      | _, _ => .error
  | .strLang e1 e2 =>
      match Expr.evalIn env mu e1, (Expr.evalIn env mu e2).toString? with
      | .term (.literal l), some tag =>
          -- An empty language tag is not a language tag; SPARQL 1.2
          -- `lang-basedir/strlang` requires the error, and `strLangDir`
          -- below already carries the same check.
          if l.val.datatype == xsdString && l.val.langTag.isNone
              && tag.length > 0 then
            .term (.literal (mkLangLiteral l.val.lexicalForm tag))
          else .error
      | _, _ => .error
  | .strLangDir e1 e2 e3 =>
      match Expr.evalIn env mu e1, (Expr.evalIn env mu e2).toString?,
            (Expr.evalIn env mu e3).toString? with
      | .term (.literal l), some tag, some dirStr =>
          if l.val.datatype == xsdString && l.val.langTag.isNone && tag.length > 0 then
            match parseTextDirection dirStr with
            | some d => .term (.literal (mkDirLangLiteral l.val.lexicalForm tag d))
            | none => .error
          else .error
      | _, _, _ => .error

  -- §17.4.1.1 BOUND. The only form that inspects the mapping's DOMAIN
  -- rather than a value, and so the only one that never errors.
  | .bound v => .bool (mu.lookup v).isSome

  -- §17.4.1.2 IF: "if the EBV of expression1 raises an error, then an
  -- error is raised" — the condition's type error PROPAGATES (W3C
  -- `if02`: `IF(1/0, false, true)` is unbound), it is not folded to
  -- the else branch.
  | .cond c t e =>
      match ebv (Expr.evalIn env mu c) with
      | some true  => Expr.evalIn env mu t
      | some false => Expr.evalIn env mu e
      | none       => .error
  | .coalesce es => coalesceResults (Expr.evalArgs env mu es)
  | .inList e1 es => inResults (Expr.evalIn env mu e1) (Expr.evalArgs env mu es)
  | .notInList e1 es =>
      match inResults (Expr.evalIn env mu e1) (Expr.evalArgs env mu es) with
      | .bool b => .bool (!b)
      | other => other

  -- §17.4.3 string functions.
  | .strLen e1 => strLenResult (Expr.evalIn env mu e1)
  | .substr e1 e2 lenOpt =>
      substrResult (Expr.evalIn env mu e1) (Expr.evalIn env mu e2)
        (Expr.evalOpt env mu lenOpt)
  | .uCase e1 => caseMapResult Fn.String.upperCase (Expr.evalIn env mu e1)
  | .lCase e1 => caseMapResult Fn.String.lowerCase (Expr.evalIn env mu e1)
  | .strStarts e1 e2 =>
      strTestResult strStartsWith (Expr.evalIn env mu e1) (Expr.evalIn env mu e2)
  | .strEnds e1 e2 =>
      strTestResult strEndsWith (Expr.evalIn env mu e1) (Expr.evalIn env mu e2)
  | .contains e1 e2 =>
      strTestResult strContains (Expr.evalIn env mu e1) (Expr.evalIn env mu e2)
  | .strBefore e1 e2 =>
      match (Expr.evalIn env mu e1).stringLiteralInfo?,
            (Expr.evalIn env mu e2).stringLiteralInfo? with
      | some (s, lang1, dt1), some (arg, lang2, dt2) =>
          if !strBeforeAfterCompatible lang1 dt1 lang2 dt2 then .error
          else if arg.length = 0 then erStringPreserve "" lang1 dt1
          else
            let result := strBeforeRaw s arg
            if result.length = 0 && !strContains s arg then erString ""
            else erStringPreserve result lang1 dt1
      | _, _ => .error
  | .strAfter e1 e2 =>
      match (Expr.evalIn env mu e1).stringLiteralInfo?,
            (Expr.evalIn env mu e2).stringLiteralInfo? with
      | some (s, lang1, dt1), some (arg, lang2, dt2) =>
          if !strBeforeAfterCompatible lang1 dt1 lang2 dt2 then .error
          else if arg.length = 0 then erStringPreserve s lang1 dt1
          else
            let result := strAfterRaw s arg
            if result.length = 0 && !strContains s arg then erString ""
            else erStringPreserve result lang1 dt1
      | _, _ => .error
  | .concat es => concatResults (Expr.evalArgs env mu es)
  | .encodeForUri e1 =>
      -- §17.4.3.11 ENCODE_FOR_URI takes a string literal and always
      -- returns a simple literal; no tag is preserved.
      match (Expr.evalIn env mu e1).stringLiteralInfo? with
      | some (s, _, _) => erString (strEncodeUri s)
      | none => .error
  -- §17.4.3.14 REGEX / §17.4.3.15 REPLACE, over the pure XPath regex
  -- engine in `L4Factoidal.Regex` (F* `regex_match` / `regex_replace`,
  -- which the F* tree reaches through its host call-out; here a port
  -- of the same derivative engine). The text argument is a string
  -- literal (simple, xsd:string or language-tagged — `stringLiteralInfo?`);
  -- pattern, replacement and flags are simple literals. REPLACE keeps
  -- the text's language tag / datatype (`erStringPreserve`). An invalid
  -- pattern, flag or replacement template (FORX0001–FORX0004) is an
  -- expression error, as in F&O.
  | .regex e1 pat none =>
      regexCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (erString "")
  | .regex e1 pat (some f) =>
      regexCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (Expr.evalIn env mu f)
  | .replace e1 pat rep none =>
      replaceCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (Expr.evalIn env mu rep) (erString "")
  | .replace e1 pat rep (some f) =>
      replaceCore (Expr.evalIn env mu e1) (Expr.evalIn env mu pat) (Expr.evalIn env mu rep) (Expr.evalIn env mu f)

  -- §17.4.4 numeric functions share XSD values and F&O operations.
  | .abs e1 => evalNumericUnary .abs (Expr.evalIn env mu e1)
  | .round e1 => evalNumericUnary (.integral .nearest) (Expr.evalIn env mu e1)
  | .ceil e1 => evalNumericUnary (.integral .ceiling) (Expr.evalIn env mu e1)
  | .floor e1 => evalNumericUnary (.integral .floor) (Expr.evalIn env mu e1)

  -- §17.4.4.7–11 hash builtins: pure Lean digests of the UTF-8 bytes,
  -- lowercase hex. SHA-2 goes through the hash-agile `Crypto.hashHex`.
  | .md5 e1    => hashResult Crypto.md5Hex (Expr.evalIn env mu e1)
  | .sha1 e1   => hashResult Crypto.sha1Hex (Expr.evalIn env mu e1)
  | .sha256 e1 => hashResult (Crypto.hashHex .sha256) (Expr.evalIn env mu e1)
  | .sha384 e1 => hashResult (Crypto.hashHex .sha384) (Expr.evalIn env mu e1)
  | .sha512 e1 => hashResult (Crypto.hashHex .sha512) (Expr.evalIn env mu e1)

  -- §17.4.5 date/time.
  | .now =>
      match env.now with
      | some ts => .term (.literal (mkTypedLiteral ts xsdDateTime))
      | none => .error
  | .year e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtYear s with | some n => .num n | none => .error
      | none => .error
  | .month e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtMonth s with | some n => .num n | none => .error
      | none => .error
  | .day e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtDay s with | some n => .num n | none => .error
      | none => .error
  | .hours e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtHours s with | some n => .num n | none => .error
      | none => .error
  | .minutes e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtMinutes s with | some n => .num n | none => .error
      | none => .error
  | .seconds e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtSeconds s with | some ds => .dec ds | none => .error
      | none => .error
  -- §17.4.5.7 TIMEZONE: an xsd:dayTimeDuration; a dateTime with no
  -- timezone is a type error (W3C `timezone01`, row `d4` unbound).
  | .timezone e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s =>
          match dtTimezone s with
          | some "" => .error
          | some tzStr => .term (.literal (mkTypedLiteral tzStr xsdDayTimeDuration))
          | none => .error
      | none => .error
  -- §17.4.5.8 TZ: a simple literal, `""` when there is no timezone.
  | .tz e1 =>
      match erToDateTimeLex (Expr.evalIn env mu e1) with
      | some s => match dtTz s with | some tzStr => erString tzStr | none => .error
      | none => .error

  -- §17.4.1.8 sameTerm uses RDF identity, including computed result terms.
  | .sameTerm e1 e2 =>
      match (Expr.evalIn env mu e1).toTerm?, (Expr.evalIn env mu e2).toTerm? with
      | some t1, some t2 => .bool (t1.sameTerm t2)
      | _, _ => .error

  -- §18.6 EXISTS: evaluated by the pattern layer, which replaces every
  -- EXISTS sub-expression by its boolean before calling this function
  -- (`substituteExistentials`, Query.lean — the F* arm is
  -- `E_Exists _ -> ER_Error` for the same reason).
  | .existsPat _ => .error
  | .notExistsPat _ => .error

  -- SCOPED OUT: §18.5.1 aggregates evaluate over a GROUP.
  | .aggregate _ _ _ => .error

  -- IRI-named functions, dispatched in the F* arm's order: langMatches
  -- (§17.4.3.10); RAND / UUID / STRUUID / BNODE (the parser maps the
  -- keywords to `fn:` IRIs); the §17.5 `xsd:` constructor functions;
  -- then the §17.6 host registry, where an unregistered IRI is the
  -- spec-required type error.
  | .functionCall i args =>
      let vals := Expr.evalArgs env mu args
      let iriS := i.val
      if i == langMatchesIri then
        match vals with
        | [v1, v2] =>
            match v1.simpleLiteral?, v2.simpleLiteral? with
            | some tag, some range => .bool (fnLangMatches tag range)
            | _, _ => .error
        | _ => .error
      -- §17.4.4.3 RAND(): the F* tree's fixed value — a double in
      -- [0, 1), deterministic by design (stated in the banner).
      else if iriS == fnNamespace ++ "rand" then .dbl "0.5"
      -- §17.4.2.12 UUID(): a fresh `urn:uuid:` IRI per (row, call site).
      else if iriS == fnNamespace ++ "uuid" then
        let row := mu.freshnessCtx fxKeyRow
        let occ := mu.freshnessCtx fxKeyOcc
        let u := "urn:uuid:" ++ fxUuidOfSeed ("u|" ++ row ++ "|" ++ occ)
        if h : L4Factoidal.RDF.isIri u then .term (.iri ⟨u, h⟩) else .error
      -- §17.4.2.13 STRUUID(): the same value as a simple literal.
      else if iriS == fnNamespace ++ "struuid" then
        let row := mu.freshnessCtx fxKeyRow
        let occ := mu.freshnessCtx fxKeyOcc
        erString (fxUuidOfSeed ("u|" ++ row ++ "|" ++ occ))
      -- §17.4.2.9 BNODE(): distinct across solutions AND across call
      -- sites within one solution; BNODE(str): the same label for the
      -- same string within one solution, distinct across solutions.
      else if iriS == fnNamespace ++ "bnode" then
        let row := mu.freshnessCtx fxKeyRow
        match vals with
        | [] =>
            let occ := mu.freshnessCtx fxKeyOcc
            .term (.bnode (fxBnodeOfSeed ("n|" ++ row ++ "|" ++ occ)))
        | [v1] =>
            match v1.toString? with
            | some s => .term (.bnode (fxBnodeOfSeed ("s|" ++ row ++ "|" ++ s)))
            | none => .error
        | _ => .error
      -- §17.5 `xsd:<type>(v)`.
      else if xsdNamespace.isPrefixOf iriS && iriS.length > xsdNamespace.length then
        match vals with
        | [v1] => evalXsdCast v1 (String.ofList (iriS.toList.drop xsdNamespace.length)) i
        | _ => .error
      else
        match env.ext iriS vals with
        | some r => r
        | none => .error

  -- SPARQL 1.2 triple-term builtins.
  | .tripleTerm es ep eo =>
      match (Expr.evalIn env mu es).toTerm?, (Expr.evalIn env mu ep).toTerm?,
            (Expr.evalIn env mu eo).toTerm? with
      | some sterm, some (.iri p), some oterm =>
          match sterm.toSubject? with
          | some ssub => .term (.tripleTerm ssub p oterm)
          | none => .error
      | _, _, _ => .error
  | .ttSubject e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.tripleTerm s _ _) => .term s.toTerm
      | _ => .error
  | .ttPredicate e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.tripleTerm _ p _) => .term (.iri p)
      | _ => .error
  | .ttObject e1 =>
      match Expr.evalIn env mu e1 with
      | .term (.tripleTerm _ _ o) => .term o
      | _ => .error
  | .isTriple e1 =>
      match Expr.evalIn env mu e1 with
      | .error => .error
      | .term (.tripleTerm _ _ _) => .bool true
      | _ => .bool false

/-- Evaluate an argument LIST (COALESCE, IN, CONCAT, function calls).
Evaluating every argument before selecting is observationally the same
as the F* source's short-circuiting recursion: the evaluator is pure
and total, so an unused argument's value cannot be observed. -/
def Expr.evalArgs (env : EvalEnv) (mu : Binding) : List Expr → List EvalResult
  | [] => []
  | e :: rest => Expr.evalIn env mu e :: Expr.evalArgs env mu rest

/-- Evaluate an OPTIONAL sub-expression (SUBSTR's length argument). -/
def Expr.evalOpt (env : EvalEnv) (mu : Binding) : Option Expr → Option EvalResult
  | none => none
  | some e => some (Expr.evalIn env mu e)

end

/-- Evaluate with no host services — the §17 semantics on its own. -/
def Expr.eval (mu : Binding) (e : Expr) : EvalResult := Expr.evalIn emptyEnv mu e

/-! ## Bridge to the algebra — §18.5 FILTER

`GraphPattern.filter` and `GraphPattern.leftJoin` take a
`Graph → Binding → Bool` (the active graph is what an EXISTS inside
the condition is evaluated against; `Query.lean` builds those
conditions). §18.5 says a row survives FILTER when its expression
"has an effective boolean value of true", so a type error is
indistinguishable from `false` at that boundary. `Expr.toCond` is
exactly that collapse — and it is where §17's careful error PRESERVING
finally stops mattering. This bridge evaluates under `emptyEnv`, so an
EXISTS in `e` is the expression-layer error; the full pipeline is
`QueryPattern.lower`. -/

def Expr.toCond (e : Expr) : Binding → Bool := fun mu => (ebv (e.eval mu)).getD false

/-- FILTER(expr) as an algebra operation (§18.5). -/
def GraphPattern.filterExpr (e : Expr) (p : GraphPattern) : GraphPattern :=
  .filter (fun _ => e.toCond) p

/-- OPTIONAL with a filter: LeftJoin(P1, P2, expr) (§18.5). -/
def GraphPattern.leftJoinExpr (l r : GraphPattern) (e : Expr) : GraphPattern :=
  .leftJoin l r (fun _ => e.toCond)

end L4Factoidal.SPARQL
