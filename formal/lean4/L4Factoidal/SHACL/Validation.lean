/-
L4Factoidal.SHACL.Validation — SHACL Core validation (§3) and the
Core constraint components (§4): the specification as a relation
(`Spec.Conforms`) and the engine as a function (`validate`).

W3C SHACL Recommendation (20 July 2017), https://www.w3.org/TR/shacl/:
  §1.4   SHACL instance / SHACL subclass   → `isShaclInstance`, `Spec.IsInstance`
  §2.1   focus nodes from targets          → `evalTarget`, `shapeFocusNodes`
  §2.3.1 property-path evaluation          → `evalPath` (value-node SETS)
  §3.1–3.4 validation, conformance         → `collectShapeViolations`, `validate`
  §3.6   validation results                → `Violation`, `ValidationReport`
  §4     constraint components             → `simpleValueCheck`,
                                              `evalAggregateNonRec`, `evalOneConstraint`

Port of `formal/fstar/SHACL.Validation.fst` sections 11c–11j and of
the numeric / dateTime / ill-formed-literal helpers of
`XSD.Datatypes.fst` that section 11g re-exports. Translation points:

* The F* evaluator is one fuel-bounded mutual group
  (`collect_shape_violations` / `eval_one_constraint` /
  `eval_aggregate_constraints`). The same group is here, structurally
  recursive on the fuel, but the NON-recursive components are factored
  out into plain functions (`simpleValueCheck` per value node,
  `evalAggregateNonRec` per focus node) so that the theorems in
  `ShaclTheorems.lean` can talk about one component at a time. Running
  out of fuel yields no violations ("sound by omission", as the F*).
* F* `shacl_class_closure` materialises the rdfs:subClassOf closure of
  the whole data graph; here `superClasses` walks the closure from the
  node's own rdf:type values — the same SHACL-instance relation (§1.4:
  rdf:type plus rdfs:subClassOf*, in the data graph only, no RDFS
  entailment), without the intermediate graph.
* SHACL-SPARQL (sh:sparql constraints, custom constraint components)
  is a separate pass in `Sparql.lean` (`validateWithSparql`), as the
  F* dispatches CC_Sparql / CC_Custom outside its Core mutual group;
  `validate` here is SHACL Core only and sees the `.sparql` / `.custom`
  constructors as inert. SPARQL-based TARGETS (sh:target) are not
  ported — see `Vocabulary.lean`; the F* `assume val
  eval_sparql_target_select` is a forward reference for exactly those,
  and nothing corresponds to it here.

The specification side (`Spec` namespace) states each ported Core
component declaratively over the same data, and `Spec.Conforms` is
§3.4's conformance relation. `ShaclTheorems.lean` relates the two.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SHACL.Shapes
import L4Factoidal.SPARQL.Expr
import L4Factoidal.Regex.XPath
import L4Factoidal.NatBounds
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.SHACL

open L4Factoidal.RDF
open L4Factoidal.SPARQL (Scaled parseToScaled parseDoubleToScaled parseIntString)

/-! ## §3.6 validation results -/

/-- One validation result (§3.6.2): focus node, result path, value,
source shape, source constraint component, severity, message. The
constraint component IRI is derived from `constraint` by
`Report.constraintComponentIri`. -/
structure Violation where
  focus       : Term
  path        : Option Path
  value       : Option Term
  sourceShape : ShapeRef
  constraint  : Constraint
  severity    : Severity
  message     : Option WfLiteral
  /-- §3.6.2.7 sh:detail: further results that explain this one. SHACL
  1.2 asks for them for sh:memberShape (one per non-conforming member's
  results) and sh:uniqueMembers (one per duplicated member). -/
  details     : List Violation := []
  /-- §3.6.2.6 sh:sourceConstraint, when the result names one beyond
  what its constraint determines: SHACL 1.2 sh:nodeByExpression results
  carry the shape the node expression yielded. -/
  sourceConstraint : Option Term := none
  deriving Repr

instance : Inhabited Violation :=
  ⟨{ focus := .bnode "", path := none, value := none, sourceShape := "",
     constraint := default, severity := default, message := none, details := [],
     sourceConstraint := none }⟩

/-- §3.6.1: `conforms` is true iff there are no validation results.
`failure` is the SHACL-SPARQL failure channel (Part 2 §5.3.2: a query
that does not parse or uses a construct forbidden with pre-bound
variables "must be rejected with a failure", the suite's `sht:Failure`
outcome) — always `none` for SHACL Core (`validate`); set only by
`validateWithSparql` (`Sparql.lean`). A failed validation is not a
conforming one: `conforms` / `results` are the partial answer, and the
harness treats `failure` as the outcome. -/
structure ValidationReport where
  conforms : Bool
  results  : List Violation
  failure  : Option String := none
  /-- SHACL 1.2 §conformanceDisallows: the conformance-disallow set the
  validation used, when it was set explicitly (`some`); `none` means
  the default set, which the report does not need to state ("If no
  values are present ... then a default set MUST be used"). -/
  disallowed : Option (List Severity) := none
  deriving Repr, Inhabited

def conformingReport : ValidationReport := { conforms := true, results := [] }

/-! ## SHACL 1.2 conformance checking

SHACL 1.2 Core §conformance-definition: "A focus node conforms to a
shape if and only if the set of result of the validation of the focus
node against the shape does not contain any validation results with a
severity level of the set of disallowed levels". §conformanceDisallows:
the set is the report's `sh:conformanceDisallows` values, and "If no
values are present ... a default set MUST be used, comprised of
sh:Violation, sh:Warning, and sh:Info". So a `sh:Debug`, `sh:Trace` or
other-IRI result is reported but does not make the report
non-conforming (core/misc/severity-004, -005). The same set decides
conformance checking inside the shape-expecting components (sh:not,
sh:and, sh:or, sh:xone, sh:node, sh:qualifiedValueShape): "all
shape-expecting constraint parameters of SHACL Core rely on
conformance checking". -/

/-- §conformanceDisallows: the default conformance-disallow set. -/
def defaultDisallowed : List Severity := [.violation, .warning, .info]

/-- SHACL 1.2 §node-expressions: "Core only supports constant IRIs and
literals as node expressions" (§IRIExpression, §LiteralExpression: the
output is the expression itself). The Core evaluator answers every term
with itself, so a blank-node sh:targetNode keeps its SHACL 1.0 reading
(a constant); an evaluator for richer node expressions (SHACL-SPARQL,
the shnex library) is passed in through `ValidationConfig.evalExpr`. -/
def constantNodeExpr (expr : Term) (_focus : Option Term) : List Term := [expr]

/-- What validation reads beyond the data graph and the shapes: the
conformance-disallow set; the node-expression evaluator
`evalExpr(expr, data graph, focusNode, {})` (§node-expressions); and the
target nodes of each shape that carries sh:uniqueValuesFor
(§UniqueValuesForConstraintComponent, "$targetNodes"). -/
structure ValidationEnv where
  disallowed : List Severity := defaultDisallowed
  evalExpr : Term → Option Term → List Term := constantNodeExpr
  targetsOf : ShapeRef → List Term := fun _ => []
  deriving Inhabited

/-- Does a result at severity `sev` count against conformance? -/
def ValidationEnv.blocks (env : ValidationEnv) (sev : Severity) : Bool :=
  env.disallowed.contains sev

/-- §conformance-definition: a list of results conforms iff no result
has a severity in the disallowed set. -/
def ValidationEnv.conforms (env : ValidationEnv) (rs : List Violation) : Bool :=
  rs.all fun r => !env.blocks r.severity

/-- The caller's choices for one validation run. `disallowed` is the
§conformanceDisallows customisation the Recommendation allows ("A
validation engine MAY provide mechanisms to customize this set");
`none` selects the default set. -/
structure ValidationConfig where
  disallowed : Option (List Severity) := none
  evalExpr : Term → Option Term → List Term := constantNodeExpr
  deriving Inhabited

def ValidationConfig.toEnv (cfg : ValidationConfig) : ValidationEnv :=
  { disallowed := cfg.disallowed.getD defaultDisallowed, evalExpr := cfg.evalExpr }

/-! ## XSD lexical spaces (port of `XSD.Datatypes.literal_ill_formed`)

§4.1.2 sh:datatype: "a literal matches a datatype if the literal's
datatype has the same IRI and, for the datatypes supported by SPARQL
1.1, is not an ill-typed literal". Conservative: a datatype not listed
is never flagged, so this only ADDS the violations the spec requires. -/

def isAsciiDigit (c : Char) : Bool := c.isDigit

/-- `[+-]? digit+`. -/
def isSignedDigitsChars : List Char → Bool
  | [] => false
  | c :: rest =>
    let digits := if c == '+' || c == '-' then rest else c :: rest
    !digits.isEmpty && digits.all isAsciiDigit

/-- `[+-]? (digit | '.')+` with at most one point and at least one digit. -/
def isDecimalLexicalChars : List Char → Bool
  | [] => false
  | c :: rest =>
    let body := if c == '+' || c == '-' then rest else c :: rest
    !body.isEmpty && body.all (fun ch => isAsciiDigit ch || ch == '.') &&
    (body.filter (fun ch => ch == '.')).length ≤ 1 && body.any isAsciiDigit

def isIntegerLexical (lex : String) : Bool := isSignedDigitsChars lex.toList
def isDecimalLexical (lex : String) : Bool := isDecimalLexicalChars lex.toList

/-- Split at the first `e` / `E`. -/
def splitAtE : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: rest =>
    if c == 'e' || c == 'E' then ([], some rest)
    else
      let (before, after) := splitAtE rest
      (c :: before, after)

/-- xsd:float / xsd:double lexical space: `NaN`, `INF`, `-INF`, or a
decimal mantissa with an optional signed-integer exponent. -/
def isFloatLexical (lex : String) : Bool :=
  if lex == "NaN" || lex == "INF" || lex == "-INF" then true
  else
    let (mantissa, expOpt) := splitAtE lex.toList
    isDecimalLexicalChars mantissa &&
    (match expOpt with | none => true | some e => isSignedDigitsChars e)

def stripLeadingPlus (lex : String) : String :=
  if lex.startsWith "+" then String.ofList (lex.toList.drop 1) else lex

/-- Well-formed integer lexical form whose value lies in `[lo, hi]`
(`none` = unbounded). -/
def intLexicalInRange (lex : String) (lo hi : Option Int) : Bool :=
  isIntegerLexical lex &&
  (match parseIntString (stripLeadingPlus lex) with
   | some n => (match lo with | some l => l ≤ n | none => true) &&
               (match hi with | some h => n ≤ h | none => true)
   | none => true)

/-! ### xsd:dateTime ordering

`YYYY-MM-DDTHH:MM:SS(.fraction)?(Z|+HH:MM|-HH:MM)?` to a millisecond
position on the proleptic Gregorian timeline plus a has-timezone flag.
Two values compare only when both or neither carry a timezone (XML
Schema's partial order leaves the mixed case indeterminate) —
core/node/minInclusive-002/003. -/

def daysFromCivil (y m d : Int) : Int :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := (if y' ≥ 0 then y' else y' - 399) / 400
  let yoe := y' - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The codepoints `[from, from+len)` of a string as a string. -/
def substr (s : String) (start len : Nat) : String :=
  String.ofList ((s.toList.drop start).take len)

/-- The `(.fraction)?(Z|±HH:MM)?` tail: (fraction ms, tz offset seconds, has tz). -/
def dtParseTail (tail : String) : Option (Int × Int × Bool) :=
  let cs := tail.toList
  let (fracMs, tzStart) : Option Int × Nat :=
    match cs with
    | '.' :: rest =>
      let digits := rest.takeWhile isAsciiDigit
      if digits.isEmpty then (none, 0)
      else
        let digLen := min digits.length 3
        match parseIntString (String.ofList (digits.take digLen)) with
        | some f =>
          let ms := if digLen == 1 then f * 100 else if digLen == 2 then f * 10 else f
          (some ms, 1 + digits.length)
        | none => (none, 0)
    | _ => (some 0, 0)
  match fracMs with
  | none => none
  | some fms =>
    let rest := cs.drop tzStart
    match rest with
    | [] => some (fms, 0, false)
    | ['Z'] => some (fms, 0, true)
    | sign :: _ =>
      if rest.length == 6 && (sign == '+' || sign == '-') then
        match parseIntString (String.ofList ((rest.drop 1).take 2)),
              parseIntString (String.ofList ((rest.drop 4).take 2)) with
        | some th, some tm =>
          let off := th * 3600 + tm * 60
          some (fms, if sign == '-' then 0 - off else off, true)
        | _, _ => none
      else none

def dtParseMs (s : String) : Option (Int × Bool) :=
  if s.length < 19 then none
  else
    match parseIntString (substr s 0 4), parseIntString (substr s 5 2),
          parseIntString (substr s 8 2), parseIntString (substr s 11 2),
          parseIntString (substr s 14 2), parseIntString (substr s 17 2) with
    | some y, some mo, some d, some h, some mi, some se =>
      match dtParseTail (String.ofList (s.toList.drop 19)) with
      | some (fms, tzoff, hasTz) =>
        let days := daysFromCivil y mo d
        let secs := days * 86400 + h * 3600 + mi * 60 + se - tzoff
        some (secs * 1000 + fms, hasTz)
      | none => none
    | _, _, _, _, _, _ => none

def dtCmp (a b : String) : Option Int :=
  match dtParseMs a, dtParseMs b with
  | some (ma, tza), some (mb, tzb) =>
    if tza == tzb then some (if ma < mb then -1 else if ma > mb then 1 else 0) else none
  | _, _ => none

/-- The XSD ill-formed-literal test for the datatypes the F* knows. -/
def literalIllFormed (dt : WfIri) (lex : String) : Bool :=
  match L4Factoidal.XSD.builtinOfIri? dt.val with
  | some b => (L4Factoidal.XSD.lexicalMap b lex).isNone
  | none   => false

/-! ## §4.3 value-range comparison (port of `numeric_cmp_le` / `_lt`) -/

/-- A numeric literal as a scaled integer: doubles through the
E-notation-aware parser FIRST (anti-pattern #8), integers and decimals
through the plain one; every other datatype has no numeric value. -/
def literalToScaled (l : Literal) : Option Scaled :=
  if l.datatype == xsdDouble then parseDoubleToScaled l.lexicalForm
  else if l.datatype == xsdInteger || l.datatype == xsdDecimal then parseToScaled l.lexicalForm
  else none

def bothDateTimes (a b : Literal) : Bool :=
  a.datatype == xsdDateTime && b.datatype == xsdDateTime

/-- `a ≤ b` when both are comparable (numeric-numeric, or both
dateTime with the same timezone presence); `none` otherwise. -/
def numericCmpLe (a b : Literal) : Option Bool :=
  if bothDateTimes a b then (dtCmp a.lexicalForm b.lexicalForm).map (· ≤ 0)
  else match literalToScaled a, literalToScaled b with
    | some sa, some sb => some (sa.cmp sb ≤ 0)
    | _, _ => none

def numericCmpLt (a b : Literal) : Option Bool :=
  if bothDateTimes a b then (dtCmp a.lexicalForm b.lexicalForm).map (· < 0)
  else match literalToScaled a, literalToScaled b with
    | some sa, some sb => some (sa.cmp sb < 0)
    | _, _ => none

/-- §4.5.3 sh:lessThan's "less than": numeric comparison when both are
numeric, lexical comparison when both have the SAME datatype, and not
less-than across incompatible datatypes (core/property/lessThan-002:
an integer against a string must violate). -/
def termLt (a b : Term) : Bool :=
  match a, b with
  | .literal la, .literal lb =>
    match literalToScaled la.val, literalToScaled lb.val with
    | some sa, some sb => sa.cmp sb < 0
    | _, _ =>
      if la.val.datatype == lb.val.datatype
      then decide (la.val.lexicalForm < lb.val.lexicalForm) else false
  | _, _ => false

def termLe (a b : Term) : Bool := termLt a b || a.eqb b

/-! ## §4.4.3 sh:pattern — the Lean regex engine (`Regex/XPath.lean`) -/

/-- SPARQL `REGEX(str, pattern, flags)` (§4.4.3's definition). A
pattern the engine cannot compile does not match — a violation,
never a silent pass. -/
def regexMatch (lex re flags : String) : Bool :=
  match Regex.compile re flags with
  | .ok c => Regex.isMatch c lex
  | .error _ => false

/-! ## §4.4.4 sh:languageIn — basic language range (RFC 4647 §3.3.1) -/

/-- `langMatches(tag, range)`: equal, or `range` is a prefix of `tag`
at a `-` boundary; case-insensitive (core/property/languageIn-001:
`"Hill"@en-NZ` is in `("en" "mi")`). -/
def langMatchesRange (tag range : String) : Bool :=
  let t := tag.toLower
  let r := range.toLower
  t == r || t.startsWith (r ++ "-")

/-- §4.4.5 sh:uniqueLang: the language tags used by two or more of the
values (case-insensitive), each listed once — one result per tag.
SHACL 1.2 §UniqueLangConstraintComponent: "For value nodes of datatype
rdf:dirLangString, the base direction is included in the uniqueness
condition, e.g., "1"@ar--rtl and "1"@ar-ltr are different, as is the
pair "1"@ar--rtl and "1"@ar" — so the key is the tag together with the
base direction. -/
def duplicatedLangTags (values : List Term) : List (String × Option TextDirection) :=
  let langs := values.filterMap fun t =>
    match t with
    | .literal l => l.val.langTag.map fun tag => (tag, l.val.direction)
    | _ => none
  let keyEq (a b : String × Option TextDirection) : Bool := langTagEq a.1 b.1 && a.2 == b.2
  let count (x : String × Option TextDirection) : Nat := (langs.filter (keyEq x)).length
  let rec distinctDups (seen : List (String × Option TextDirection)) :
      List (String × Option TextDirection) → List (String × Option TextDirection)
    | [] => []
    | x :: rest =>
      if seen.any (keyEq x) then distinctDups seen rest
      else if count x ≥ 2 then x :: distinctDups (x :: seen) rest
      else distinctDups (x :: seen) rest
  distinctDups [] langs

/-! ## §2.3.1 property-path evaluation

Value-node SET semantics: order-insensitive, deduplicated after every
hop (core/path/path-sequence-duplicate-001: two routes to the same
literal give ONE value). `Path.invert` pushes inverse paths down to
predicate leaves (inverse distributes over sequence with the order
reversed, elementwise over alternative, commutes with the star
operators, and cancels with itself) so evaluation only walks forwards
or backwards over single predicates. The star operators iterate to a
fixpoint under fuel. -/

mutual
  def Path.invert : Path → Path
    | .pred i => .inverse (.pred i)
    | .inverse p => p
    | .seq ps => .seq (Path.invertList ps).reverse
    | .alt ps => .alt (Path.invertList ps)
    | .zeroOrMore p => .zeroOrMore p.invert
    | .oneOrMore p => .oneOrMore p.invert
    | .zeroOrOne p => .zeroOrOne p.invert
  def Path.invertList : List Path → List Path
    | [] => []
    | p :: rest => p.invert :: Path.invertList rest
end

mutual
  def evalPathFuel (g : Graph) (start : Term) : Path → Nat → List Term
    | _, 0 => []
    | p, fuel + 1 =>
      match p with
      | .pred pr => objectsOfTerm g start pr
      | .inverse (.pred pr) => subjectsOf g pr start
      | .inverse p' => evalPathFuel g start p'.invert fuel
      | .seq ps => evalSeqFuel g [start] ps fuel
      | .alt ps => evalAltFuel g start ps fuel
      | .zeroOrMore p' =>
        dedupTerms (start :: evalPlusFuel g (evalPathFuel g start p' fuel) p' fuel)
      | .oneOrMore p' =>
        dedupTerms (evalPlusFuel g (evalPathFuel g start p' fuel) p' fuel)
      | .zeroOrOne p' => dedupTerms (start :: evalPathFuel g start p' fuel)

  def evalSeqFuel (g : Graph) (starts : List Term) : List Path → Nat → List Term
    | _, 0 => []
    | [], _ + 1 => dedupTerms starts
    | p :: rest, fuel + 1 =>
      let nexts := dedupTerms (starts.flatMap fun s => evalPathFuel g s p fuel)
      evalSeqFuel g nexts rest fuel

  def evalAltFuel (g : Graph) (start : Term) : List Path → Nat → List Term
    | _, 0 => []
    | ps, fuel + 1 => dedupTerms (ps.flatMap fun p => evalPathFuel g start p fuel)

  def evalPlusFuel (g : Graph) (frontier : List Term) (p : Path) : Nat → List Term
    | 0 => dedupTerms frontier
    | fuel + 1 =>
      let nexts := dedupTerms (frontier.flatMap fun s => evalPathFuel g s p fuel)
      let combined := dedupTerms (frontier ++ nexts)
      if combined.length ≤ frontier.length then frontier
      else evalPlusFuel g combined p fuel
end

/-- §2.3.1: the value nodes reachable from `start` over `p`. -/
def evalPath (g : Graph) (start : Term) (p : Path) : List Term :=
  evalPathFuel g start p (g.length + 50)

/-- §2.3 / SHACL 1.2 §value-nodes-property-shapes: the value nodes of a
focus node for a shape — the focus node itself for a node shape; for a
property shape, "all nodes in the data graph that can be reached from
the focus node with the path mapping of p", plus the output nodes of
sh:values, and, "If the set is still empty", the output nodes of
sh:defaultValue. -/
def valueNodes (env : ValidationEnv) (data : Graph) (node : Term) (s : Shape) : List Term :=
  if s.isProperty then
    let viaPath := match s.path with
      | some p => evalPath data node p
      | none => []
    let viaValues := match s.valuesExpr with
      | some e => env.evalExpr e (some node)
      | none => []
    let combined := dedupTerms (viaPath ++ viaValues)
    if combined.isEmpty then
      match s.defaultValue with
      | some d => dedupTerms (env.evalExpr d (some node))
      | none => []
    else combined
  else [node]

/-! ## §4 the non-recursive components -/

def isBnodeTerm : Term → Bool
  | .bnode _ => true
  | _ => false

def isIriTerm : Term → Bool
  | .iri _ => true
  | _ => false

def isLiteralTerm : Term → Bool
  | .literal _ => true
  | _ => false

/-! ## SHACL 1.2 SHACL lists

SHACL 1.2 Core §terminology, "SHACL Lists": "A SHACL list in an RDF
graph G is an IRI or a blank node that is either rdf:nil (provided that
rdf:nil has no value for either rdf:first or rdf:rest), or has exactly
one value for the property rdf:first in G and exactly one value for the
property rdf:rest in G that is also a SHACL list in G, and the list does
not have itself as a value of the property path rdf:rest+ in G." The
members are the rdf:first value followed by the members of the rdf:rest
value. `visited` holds the list nodes already passed, so a node met
again is the rdf:rest+ cycle the definition excludes; the fuel bounds
the walk by the graph size (each step passes a distinct node that is
the subject of an rdf:first triple), and running out answers "not a
SHACL list". -/

def shaclListMembersFuel (g : Graph) (visited : List Term) : Term → Nat → Option (List Term)
  | _, 0 => none
  | t, fuel + 1 =>
    match t with
    | .iri _ | .bnode _ =>
      let firsts := dedupTerms (objectsOfTerm g t rdfFirst)
      let rests := dedupTerms (objectsOfTerm g t rdfRest)
      if t == .iri rdfNil then
        if firsts.isEmpty && rests.isEmpty then some [] else none
      else if visited.contains t then none
      else
        match firsts, rests with
        | [f], [r] => (shaclListMembersFuel g (t :: visited) r fuel).map (f :: ·)
        | _, _ => none
    | _ => none

/-- The members of `t` when `t` is a SHACL list in `g`, else `none`. -/
def shaclListMembers (g : Graph) (t : Term) : Option (List Term) :=
  shaclListMembersFuel g [] t (g.length + 2)

/-- SHACL 1.2 §UniqueMembersConstraintComponent: the members that occur
more than once (under term equality `Term.eqb`), each occurrence kept. -/
def dupMembers (ms : List Term) : List Term :=
  ms.filter fun m => 2 ≤ (ms.filter fun u => u.eqb m).length

def isTripleTermTerm : Term → Bool
  | .tripleTerm _ _ _ => true
  | _ => false

def nodeKindOk (t : Term) : NodeKind → Bool
  | .blankNode => isBnodeTerm t
  | .iri => isIriTerm t
  | .literal => isLiteralTerm t
  | .blankNodeOrIri => isBnodeTerm t || isIriTerm t
  | .blankNodeOrLiteral => isBnodeTerm t || isLiteralTerm t
  | .iriOrLiteral => isIriTerm t || isLiteralTerm t
  | .tripleTerm => isTripleTermTerm t

/-- SHACL 1.2 §SingleLineConstraintComponent: the characters of the
regular expression `[\f\r\n\v]` — form feed, carriage return, line
feed, vertical tab. -/
def isLineBreakChar (c : Char) : Bool :=
  c == '\x0C' || c == '\r' || c == '\n' || c == '\x0B'

/-- Does the lexical form contain a line break? -/
def hasLineBreak (lex : String) : Bool := lex.toList.any isLineBreakChar

/-- The per-VALUE-NODE check of the non-recursive components (§4.1,
§4.3, §4.4.1–§4.4.4, §4.8.2): `some true` = the value node satisfies
the component, `some false` = a validation result for that value,
`none` = not a per-value component (cardinality, property-pair,
uniqueLang, closed, hasValue are per focus node; the logical and
shape-based components need conformance, see `evalOneConstraint`). -/
def simpleValueCheck (data : Graph) (cc : Constraint) (v : Term) : Option Bool :=
  match cc with
  | .cls cs => some (cs.any (isShaclInstance data v))
  | .datatype dts =>
    some (match v with
      | .literal l => dts.any fun dt =>
          l.val.datatype == dt && !literalIllFormed dt l.val.lexicalForm
      | _ => false)
  | .nodeKind nks => some (nks.any (nodeKindOk v))
  | .singleLine b =>
    some (match v with
      | .literal l => !b || !hasLineBreak l.val.lexicalForm
      | _ => true)
  | .rootClass cs =>
    some (match v with
      | .iri i => cs.any fun c => (superClasses data i).contains c
      | _ => false)
  -- SHACL 1.2 §MinListLengthConstraintComponent /
  -- §MaxListLengthConstraintComponent / §UniqueMembersConstraintComponent:
  -- "Each value node v must be a SHACL list - if v is not a SHACL list
  -- there is a validation result."
  | .minListLength n =>
    some (match shaclListMembers data v with
      | some ms => decide (n ≤ ms.length)
      | none => false)
  | .maxListLength n =>
    some (match shaclListMembers data v with
      | some ms => decide (ms.length ≤ n)
      | none => false)
  | .uniqueMembers b =>
    some (match shaclListMembers data v with
      | some ms => !b || (dupMembers ms).isEmpty
      | none => false)
  | .inSet items => some (termMem v items)
  | .pattern re flags =>
    some (match termLexical v with | some lex => regexMatch lex re flags | none => false)
  | .minLength n =>
    some (match termLexical v with | some lex => decide (n ≤ lex.length) | none => false)
  | .maxLength n =>
    some (match termLexical v with | some lex => decide (lex.length ≤ n) | none => false)
  | .languageIn langs =>
    some (match v with
      | .literal l => match l.val.langTag with
        | some lt => langs.any (langMatchesRange lt)
        | none => false
      | _ => false)
  | .minInclusive t =>
    some (match v, t with
      | .literal lv, .literal lt => numericCmpLe lt.val lv.val == some true
      | _, _ => false)
  | .maxInclusive t =>
    some (match v, t with
      | .literal lv, .literal lt => numericCmpLe lv.val lt.val == some true
      | _, _ => false)
  | .minExclusive t =>
    some (match v, t with
      | .literal lv, .literal lt => numericCmpLt lt.val lv.val == some true
      | _, _ => false)
  | .maxExclusive t =>
    some (match v, t with
      | .literal lv, .literal lt => numericCmpLt lv.val lt.val == some true
      | _, _ => false)
  | _ => none

/-- A result with sh:value (§3.6.2). -/
def valueViolation (focus : Term) (s : Shape) (cc : Constraint) (v : Term) : Violation :=
  { focus := focus, path := s.path, value := some v, sourceShape := s.id,
    constraint := cc, severity := s.severity, message := s.message }

/-- The sh:detail results of a per-value result (§3.6.2.7). SHACL 1.2
§UniqueMembersConstraintComponent: "Each duplicate member m of a list v
should be reported as a separate sh:detail in the validation result
for v" — one per distinct duplicated member, with the member as
sh:value. Every other per-value component has none. -/
def valueDetails (data : Graph) (focus : Term) (s : Shape) (cc : Constraint) (v : Term) :
    List Violation :=
  match cc with
  | .uniqueMembers _ =>
    match shaclListMembers data v with
    | some ms => (dedupTerms (dupMembers ms)).map (valueViolation focus s cc)
    | none => []
  | _ => []

/-- A result without sh:value. -/
def focusViolation (focus : Term) (s : Shape) (cc : Constraint) : Violation :=
  { focus := focus, path := s.path, value := none, sourceShape := s.id,
    constraint := cc, severity := s.severity, message := s.message }

/-- §4.8.1 sh:closed: the predicates a closed shape allows — the
sh:path predicates of its property shapes plus sh:ignoredProperties. -/
def pathPredicatesOfShape (sg : List Shape) (s : Shape) : List WfIri :=
  s.propertyRefs.filterMap fun r =>
    match lookupShape r sg with
    | some ps => match ps.path with | some (.pred p) => some p | _ => none
    | none => none

/-- §4.8.1 sh:closed: "there is a validation result for each triple
that has a value node as its subject and a predicate that is not in P
... The validation result MUST have the predicate of the triple as its
sh:resultPath, and the object of the triple as its sh:value." `allowed`
gives P (with the ignored properties) for a value node. -/
def closedViolations (data : Graph) (focus : Term) (s : Shape) (cc : Constraint)
    (values : List Term) (allowed : Subject → List WfIri) : List Violation :=
  values.flatMap fun v =>
    match v.toSubject? with
    | none => []
    | some subj =>
      data.filterMap fun t =>
        if t.s == subj && !(allowed subj).contains t.p
        then some { focus := focus, path := some (.pred t.p), value := some t.o,
                    sourceShape := s.id, constraint := cc,
                    severity := s.severity, message := s.message }
        else none

/-- SHACL 1.2 sh:closed sh:ByTypes: "P is the set of IRI properties that
can be reached from the value node via the following algorithm, plus
rdf:type" — collectProperties(T) for each rdf:type T of the value node
in the data graph, looked up in the decode-time table — plus the
ignored properties. -/
def byTypesAllowed (data : Graph) (table : List (WfIri × List WfIri)) (ignored : List WfIri)
    (subj : Subject) : List WfIri :=
  rdfType :: ignored ++ (objectsOf data subj rdfType).flatMap fun t =>
    match t with
    | .iri ti => match table.find? (fun e => e.1 == ti) with
      | some e => e.2
      | none => []
    | _ => []

/-- SHACL 1.2 §UniqueValuesForConstraintComponent: a node's values for
the key properties, one value set per property, or `none` when some
property has no value — such a node shares its key with no other node
("No result is produced if V has no values for any of the properties";
see `uvfKey`'s use below for the reading taken). -/
def uvfKey (data : Graph) (n : Term) : List WfIri → Option (List (List Term))
  | [] => some []
  | p :: rest =>
    match dedupTerms (objectsOfTerm data n p) with
    | [] => none
    | vs => (uvfKey data n rest).map (vs :: ·)

/-- Two value sets are equal (under `Term.eqb`). -/
def termSetEq (a b : List Term) : Bool :=
  a.all (fun x => termMem x b) && b.all (fun x => termMem x a)

/-- Two keys are equal: the same value set for every key property. -/
def keyEq : List (List Term) → List (List Term) → Bool
  | [], [] => true
  | x :: xs, y :: ys => termSetEq x y && keyEq xs ys
  | _, _ => false

/-- "there exists another node in $targetNodes that has exactly the same
values for all properties in $properties as V". -/
def uvfClash (data : Graph) (targets : List Term) (props : List WfIri) (v : Term) : Bool :=
  match uvfKey data v props with
  | none => false
  | some k => targets.any fun t =>
      !t.eqb v && match uvfKey data t props with
        | some k2 => keyEq k k2
        | none => false

/-- The per-FOCUS-NODE check of the non-recursive aggregate
components, given the value nodes: §4.2 cardinality, §4.4.5
uniqueLang, §4.5 property pairs, §4.8.1 closed, §4.8.2 hasValue. The
result multiplicity follows each component's textual definition (one
result per missing value for sh:equals, per pair for sh:lessThan, per
offending triple for sh:closed, …) because the suite compares reports
up to isomorphism. -/
def evalAggregateNonRec (env : ValidationEnv) (data : Graph) (sg : List Shape) (focus : Term)
    (s : Shape) (values : List Term) (cc : Constraint) : List Violation :=
  match cc with
  -- SHACL 1.2 §UniqueValuesForConstraintComponent: "For each value node V
  -- for which there exists another node in $targetNodes that has exactly
  -- the same values for all properties in $properties as V there is a
  -- validation result." The text names no sh:value, and the suite's
  -- expected results (core/node/uniqueValuesFor-001) carry none. A node
  -- missing a value for some key property has no key (`uvfKey`), the
  -- reading under which a partial key never clashes.
  | .uniqueValuesFor props =>
    values.filterMap fun v =>
      if uvfClash data (env.targetsOf s.id) props v then some (focusViolation focus s cc) else none
  | .minCount n => if values.length < n then [focusViolation focus s cc] else []
  | .maxCount n => if n < values.length then [focusViolation focus s cc] else []
  | .hasValue t => if termMem t values then [] else [focusViolation focus s cc]
  | .uniqueLang b =>
    if b then (duplicatedLangTags values).map (fun _ => focusViolation focus s cc) else []
  | .closed ignored =>
    closedViolations data focus s cc values fun _ => pathPredicatesOfShape sg s ++ ignored
  | .closedByTypes table ignored =>
    closedViolations data focus s cc values (byTypesAllowed data table ignored)
  | .equals p =>
    let others := evalPath data focus p
    (values.filterMap fun v => if termMem v others then none else some (valueViolation focus s cc v)) ++
    (others.filterMap fun o => if termMem o values then none else some (valueViolation focus s cc o))
  | .disjoint p =>
    let others := evalPath data focus p
    values.filterMap fun v => if termMem v others then some (valueViolation focus s cc v) else none
  | .lessThan p =>
    let others := evalPath data focus p
    values.flatMap fun v => others.filterMap fun w =>
      if termLt v w then none else some (valueViolation focus s cc v)
  | .lessThanOrEquals p =>
    let others := evalPath data focus p
    values.flatMap fun v => others.filterMap fun w =>
      if termLe v w then none else some (valueViolation focus s cc v)
  -- SHACL 1.2 §SubsetOfConstraintComponent: "For each value node that
  -- does not exist in $otherNodes, there is a validation result with the
  -- value node as sh:value."
  | .subsetOf p =>
    let others := evalPath data focus p
    values.filterMap fun v => if termMem v others then none else some (valueViolation focus s cc v)
  | _ => []

/-! ## §3 validation — the fuel-bounded mutual group

§3.4: a focus node conforms to a shape iff validating it produces no
result. The logical (§4.6) and shape-based (§4.7) components ask that
question of other shapes, so the three judgments are mutually
recursive; shapes may reference each other cyclically, so recursion is
on a fuel, as in the F* source. Every mutual call decrements it. -/

/-- §4.7.2: the siblings of a property shape — the OTHER sh:property
values of every shape that has it as a sh:property value. -/
def siblingShapeRefs (sg : List Shape) (selfId : ShapeRef) : List ShapeRef :=
  sg.flatMap fun parent =>
    if parent.propertyRefs.contains selfId
    then parent.propertyRefs.filter (· != selfId) else []

def qualifiedShapeRefOf : Constraint → Option ShapeRef
  | .qualifiedMinCount r _ _ => some r
  | .qualifiedMaxCount r _ _ => some r
  | _ => none

mutual
  /-- §3.4: every validation result of validating `node` against `s`.
  The shape's OWN results (per value node, per focus node, qualified)
  all carry `s.severity`; the nested property shapes' results carry
  theirs. -/
  def collectShapeViolations (env : ValidationEnv) (data : Graph) (sg : List Shape)
      (node : Term) (s : Shape) : Nat → List Violation
    | 0 => []
    | fuel + 1 =>
      let values := valueNodes env data node s
      let perValue := values.flatMap fun v =>
        s.constraints.flatMap fun cc => evalOneConstraint env data sg node s v cc fuel
      let agg := s.constraints.flatMap fun cc => evalAggregateNonRec env data sg node s values cc
      let qualified := s.constraints.flatMap fun cc =>
        evalAggregate env data sg node s values cc fuel
      -- §2.2: the property shapes of a shape are validated against its
      -- VALUE nodes (for a node shape, the focus node itself).
      let nested := values.flatMap fun v =>
        s.propertyRefs.flatMap fun r =>
          match lookupShape r sg with
          | none => []
          | some ps => collectShapeViolations env data sg v ps fuel
      (perValue ++ agg ++ qualified) ++ nested

  /-- One component against one value node. The shape-expecting
  components ask the SHACL 1.2 conformance-checking question
  (`ValidationEnv.conforms`) of the referenced shape. -/
  def evalOneConstraint (env : ValidationEnv) (data : Graph) (sg : List Shape) (focus : Term)
      (s : Shape) (v : Term) (cc : Constraint) : Nat → List Violation
    | 0 => []
    | fuel + 1 =>
      let viol := [valueViolation focus s cc v]
      match cc with
      -- §4.6.1 sh:not: a result iff the value conforms to the shape.
      | .notOf r =>
        match lookupShape r sg with
        | none => []
        | some rs => if env.conforms (collectShapeViolations env data sg v rs fuel) then viol else []
      -- §4.6.2 sh:and: a result iff the value fails some shape.
      | .andOf rs =>
        if rs.all (fun r => match lookupShape r sg with
            | none => true
            | some s2 => env.conforms (collectShapeViolations env data sg v s2 fuel))
        then [] else viol
      -- §4.6.3 sh:or: a result iff the value conforms to no shape.
      | .orOf rs =>
        if rs.any (fun r => match lookupShape r sg with
            | none => false
            | some s2 => env.conforms (collectShapeViolations env data sg v s2 fuel))
        then [] else viol
      -- §4.6.4 sh:xone: a result iff the number of shapes conformed to is not exactly one.
      | .xoneOf rs =>
        let matched := rs.filter fun r => match lookupShape r sg with
          | none => false
          | some s2 => env.conforms (collectShapeViolations env data sg v s2 fuel)
        if matched.length == 1 then [] else viol
      -- §4.7.1 sh:node: a result iff the value does not conform.
      | .nodeOf r =>
        match lookupShape r sg with
        | none => []
        | some s2 => if env.conforms (collectShapeViolations env data sg v s2 fuel) then [] else viol
      -- SHACL 1.2 Node Expressions §NodeByExpressionConstraintComponent:
      -- "For each value node v: perform a conformance check of v against
      -- each output node of evalExpr(expr, data graph, v, {}) s ... if v
      -- does not conform to s, there is a validation result with v as
      -- sh:value and a deep copy of s as sh:sourceConstraint." An output
      -- node that names no shape imposes nothing (as for sh:node). The
      -- deep copy of an IRI shape is the IRI.
      | .nodeByExpression expr =>
        (env.evalExpr expr (some v)).filterMap fun st =>
          match termToShapeRef st with
          | none => none
          | some r =>
            match lookupShape r sg with
            | none => none
            | some s2 =>
              if env.conforms (collectShapeViolations env data sg v s2 fuel) then none
              else some { valueViolation focus s cc v with sourceConstraint := some st }
      -- SHACL 1.2 §MemberShapeConstraintComponent: a value node that is
      -- not a SHACL list is a result; otherwise a result iff some
      -- member does not conform, with the non-conforming members'
      -- results as its sh:detail values ("validation of individual
      -- members should not be attempted" for a non-list).
      | .memberShape r =>
        match shaclListMembers data v with
        | none => viol
        | some members =>
          match lookupShape r sg with
          | none => []
          | some ms =>
            let bad := members.eraseDups.filter fun m =>
              !env.conforms (collectShapeViolations env data sg m ms fuel)
            if bad.isEmpty then []
            else [{ valueViolation focus s cc v with
                    details := bad.flatMap fun m => collectShapeViolations env data sg m ms fuel }]
      | _ =>
        match simpleValueCheck data cc v with
        | some true => []
        | some false => [{ valueViolation focus s cc v with
                           details := valueDetails data focus s cc v }]
        | none => []

  /-- §4.7.2 / §4.7.3 qualified cardinality over the value nodes of one
  focus node — the one aggregate that needs conformance counts (every
  other aggregate is `evalAggregateNonRec`). -/
  def evalAggregate (env : ValidationEnv) (data : Graph) (sg : List Shape) (focus : Term)
      (s : Shape) (values : List Term) (cc : Constraint) : Nat → List Violation
    | 0 => []
    | fuel + 1 =>
      match cc with
      | .qualifiedMinCount qref qmin qdisjoint =>
        if qmin ≤ qualifyingCount env data sg s values qref qdisjoint fuel then []
        else [focusViolation focus s cc]
      | .qualifiedMaxCount qref qmax qdisjoint =>
        if qualifyingCount env data sg s values qref qdisjoint fuel ≤ qmax then []
        else [focusViolation focus s cc]
      -- SHACL 1.2 §SomeValueConstraintComponent: "if none of the value
      -- nodes conforms to $someValue, there is a validation result".
      | .someValue r =>
        match lookupShape r sg with
        | none => []
        | some rs =>
          if values.any (fun v => env.conforms (collectShapeViolations env data sg v rs fuel))
          then [] else [focusViolation focus s cc]
      | _ => []

  /-- §4.7.2: the number of value nodes conforming to the qualified
  value shape and — with sh:qualifiedValueShapesDisjoint — to no
  sibling's qualified value shape. -/
  def qualifyingCount (env : ValidationEnv) (data : Graph) (sg : List Shape) (s : Shape)
      (values : List Term) (qref : ShapeRef) (qdisjoint : Bool) : Nat → Nat
    | 0 => 0
    | fuel + 1 =>
      match lookupShape qref sg with
      | none => 0
      | some qs =>
        let siblingQrefs := (siblingShapeRefs sg s.id).flatMap fun r =>
          match lookupShape r sg with
          | some sib => sib.constraints.filterMap qualifiedShapeRefOf
          | none => []
        let conformsQ (v : Term) : Bool :=
          env.conforms (collectShapeViolations env data sg v qs fuel)
        let excluded (v : Term) : Bool :=
          qdisjoint && siblingQrefs.any fun sr =>
            match lookupShape sr sg with
            | some sqs => env.conforms (collectShapeViolations env data sg v sqs fuel)
            | none => false
        (values.filter fun v => conformsQ v && !excluded v).length
end

/-- The fuel `validate` runs with: each nesting level through sh:not /
sh:and / sh:or / sh:xone / sh:node / sh:qualifiedValueShape consumes
two units, and a shapes graph of `n` shapes cannot nest deeper than
`n` without repeating. -/
def validateFuel (sg : List Shape) : Nat := sg.length * 4 + 50

/-! ## §2.1 targets

Defined after the mutual group because SHACL 1.2 §targetWhere asks
conformance checking of candidate nodes. -/

/-- The nodes of a graph: its subjects and objects (RDF 1.1 Concepts
§3.1, "The set of nodes of an RDF graph is the set of subjects and
objects of triples in the graph"), deduplicated. -/
def graphNodes (data : Graph) : List Term :=
  dedupTerms (data.flatMap fun t => [t.s.toTerm, t.o])

/-- §2.1.1–§2.1.4, §2.1.3.1, SHACL 1.2 §targetNode (a node expression,
evaluated with the shape as focus node: "evalExpr(expr, data graph, s,
{})") and §targetWhere ("the set of nodes in a data graph DG that
conform to w"). `allSubjects` are the candidate focus nodes for class
targets (every subject of the data graph). -/
def evalTarget (env : ValidationEnv) (data : Graph) (sg : List Shape)
    (allSubjects : List Subject) (s : Shape) : Target → List Term
  | .cls c => allSubjects.filterMap fun n =>
      if isShaclInstance data n.toTerm c then some n.toTerm else none
  | .implicitClass c => allSubjects.filterMap fun n =>
      if isShaclInstance data n.toTerm c then some n.toTerm else none
  | .node n =>
    match n with
    | .bnode _ => env.evalExpr n (some (shapeRefToTerm s.id))
    | _ => [n]
  | .subjectsOf p => dedupTerms ((data.filter (fun t => t.p == p)).map (·.s.toTerm))
  | .objectsOf p => dedupTerms ((data.filter (fun t => t.p == p)).map (·.o))
  | .whereShape r =>
    match lookupShape r sg with
    | none => []
    | some ws => (graphNodes data).filter fun n =>
        env.conforms (collectShapeViolations env data sg n ws (validateFuel sg))

/-- SHACL 1.2 §explicit-shape-target: "If n has value s for sh:shape in
the data graph, then n is a target for s" — for every shape, declared
or not. -/
def explicitShapeTargets (data : Graph) (s : Shape) : List Term :=
  (data.filter fun t => t.p == shShape && t.o == shapeRefToTerm s.id).map (·.s.toTerm)

/-- §2.1: the focus nodes of a shape — the union of its targets. -/
def shapeFocusNodes (env : ValidationEnv) (data : Graph) (sg : List Shape)
    (allSubjects : List Subject) (s : Shape) : List Term :=
  dedupTerms (s.targets.flatMap (evalTarget env data sg allSubjects s) ++
    explicitShapeTargets data s)

def hasUniqueValuesFor (s : Shape) : Bool :=
  s.constraints.any fun c => match c with | .uniqueValuesFor _ => true | _ => false

/-- The validation environment of one run: the caller's choices plus,
for every shape with sh:uniqueValuesFor, its target nodes. Those target
nodes are computed under the caller's environment, whose `targetsOf` is
empty: a sh:targetWhere shape that itself carries sh:uniqueValuesFor
would make targets and conformance depend on each other, a case of the
recursion SHACL leaves undefined (§shapes-recursion). -/
def ValidationConfig.envFor (cfg : ValidationConfig) (data : Graph) (shapes : List Shape) :
    ValidationEnv :=
  let env0 := cfg.toEnv
  let allSubjects := distinctSubjects data
  let table := (shapes.filter hasUniqueValuesFor).map fun s =>
    (s.id, shapeFocusNodes env0 data shapes allSubjects s)
  { env0 with targetsOf := fun r => match table.find? (fun e => e.1 == r) with
      | some e => e.2
      | none => [] }

/-- §3.1: validate a data graph against a shapes graph. "the validation
results are the union of results of the validation of the data graph
against all shapes in the shapes graph": every shape is validated
against its focus nodes (a shape with no target and no sh:shape link
has none and is reached only by reference). SHACL 1.2
§conformance-definition: `conforms` iff no result has a disallowed
severity. -/
def validate (data : Graph) (sg : ShapesGraph) (cfg : ValidationConfig := {}) :
    ValidationReport :=
  let shapes := sg.shapes
  let env := cfg.envFor data shapes
  let allSubjects := distinctSubjects data
  let fuel := validateFuel shapes
  let results := shapes.flatMap fun s =>
    (shapeFocusNodes env data shapes allSubjects s).flatMap fun fn =>
      collectShapeViolations env data shapes fn s fuel
  { conforms := env.conforms results, results := results, disallowed := cfg.disallowed }

/-! ## The specification: conformance as a relation

The declarative statement of the ported components and of §3.4
conformance, over the same data the engine reads. Where a component's
definition is itself a computation on lexical forms (the XSD lexical
spaces, the regex match, the numeric order, the path algebra) the
specification names that computation; what it adds is the quantifier
structure ("for each value node", "the number of value nodes", …)
that the engine realises with list traversals. `ShaclTheorems.lean`
relates the two. -/

namespace Spec

/-- §1.4 "SHACL subclass": the reflexive-transitive closure of
rdfs:subClassOf in the data graph. -/
inductive SubClassOf (g : Graph) : WfIri → WfIri → Prop
  | refl (c : WfIri) : SubClassOf g c c
  | step {a b c : WfIri}
      (h : ({ s := .iri a, p := rdfsSubClassOf, o := .iri b } : Triple) ∈ g)
      (hbc : SubClassOf g b c) : SubClassOf g a c

/-- §1.4 "SHACL instance": a node with an rdf:type that is a SHACL
subclass of the class. -/
def IsInstance (g : Graph) (n : Term) (c : WfIri) : Prop :=
  ∃ s t, n.toSubject? = some s ∧
    ({ s := s, p := rdfType, o := .iri t } : Triple) ∈ g ∧ SubClassOf g t c

/-- §4.1.3 node kinds (SHACL 1.2 adds sh:TripleTerm). -/
def NodeKindOk (nk : NodeKind) (v : Term) : Prop :=
  match nk with
  | .blankNode => ∃ b, v = .bnode b
  | .iri => ∃ i, v = .iri i
  | .literal => ∃ l, v = .literal l
  | .blankNodeOrIri => (∃ b, v = .bnode b) ∨ (∃ i, v = .iri i)
  | .blankNodeOrLiteral => (∃ b, v = .bnode b) ∨ (∃ l, v = .literal l)
  | .iriOrLiteral => (∃ i, v = .iri i) ∨ (∃ l, v = .literal l)
  | .tripleTerm => ∃ s p o, v = .tripleTerm s p o

/-- The per-value components, declaratively. `True` for a component
that is not per-value (those are in `FocusSatisfies` and `Conforms`). -/
def ValueSatisfies (g : Graph) (cc : Constraint) (v : Term) : Prop :=
  match cc with
  | .cls cs => ∃ c ∈ cs, IsInstance g v c
  | .datatype dts => ∃ l, v = .literal l ∧ ∃ dt ∈ dts, l.val.datatype = dt ∧
      literalIllFormed dt l.val.lexicalForm = false
  | .nodeKind nks => ∃ nk ∈ nks, NodeKindOk nk v
  | .singleLine b => b = true → ∀ l, v = .literal l →
      ∀ c ∈ l.val.lexicalForm.toList, isLineBreakChar c = false
  | .rootClass cs => ∃ i, v = .iri i ∧ ∃ c ∈ cs, SubClassOf g i c
  | .minListLength n => ∃ ms, shaclListMembers g v = some ms ∧ n ≤ ms.length
  | .maxListLength n => ∃ ms, shaclListMembers g v = some ms ∧ ms.length ≤ n
  | .uniqueMembers b => ∃ ms, shaclListMembers g v = some ms ∧
      (b = true → ∀ m ∈ ms, (ms.filter fun u => u.eqb m).length < 2)
  | .inSet items => ∃ u ∈ items, Term.eqb u v = true
  | .pattern re flags => ∃ lex, termLexical v = some lex ∧ regexMatch lex re flags = true
  | .minLength n => ∃ lex, termLexical v = some lex ∧ n ≤ lex.length
  | .maxLength n => ∃ lex, termLexical v = some lex ∧ lex.length ≤ n
  | .languageIn langs => ∃ l lt, v = .literal l ∧ l.val.langTag = some lt ∧
      ∃ r ∈ langs, langMatchesRange lt r = true
  | .minInclusive t => ∃ lv lt, v = .literal lv ∧ t = .literal lt ∧
      numericCmpLe lt.val lv.val = some true
  | .maxInclusive t => ∃ lv lt, v = .literal lv ∧ t = .literal lt ∧
      numericCmpLe lv.val lt.val = some true
  | .minExclusive t => ∃ lv lt, v = .literal lv ∧ t = .literal lt ∧
      numericCmpLt lt.val lv.val = some true
  | .maxExclusive t => ∃ lv lt, v = .literal lv ∧ t = .literal lt ∧
      numericCmpLt lv.val lt.val = some true
  | _ => True

/-- §4.8.1 sh:closed, declaratively: every triple whose subject is a
value node has an allowed predicate. -/
def ClosedOk (g : Graph) (values : List Term) (allowed : Subject → List WfIri) : Prop :=
  ∀ v ∈ values, ∀ subj, v.toSubject? = some subj → ∀ t ∈ g, t.s = subj → t.p ∈ allowed subj

/-- The per-focus-node components over the value nodes, declaratively.
`True` for the components handled elsewhere. -/
def FocusSatisfies (env : ValidationEnv) (g : Graph) (sg : List Shape) (focus : Term)
    (s : Shape) (cc : Constraint) (values : List Term) : Prop :=
  match cc with
  | .uniqueValuesFor props => ∀ v ∈ values, ∀ k, uvfKey g v props = some k →
      ∀ t ∈ env.targetsOf s.id, Term.eqb t v = false →
        ∀ k2, uvfKey g t props = some k2 → keyEq k k2 = false
  | .minCount n => n ≤ values.length
  | .maxCount n => values.length ≤ n
  | .hasValue t => ∃ u ∈ values, Term.eqb u t = true
  | .uniqueLang b => b = true → duplicatedLangTags values = []
  | .equals p =>
    (∀ v ∈ values, ∃ u ∈ evalPath g focus p, Term.eqb u v = true) ∧
    (∀ o ∈ evalPath g focus p, ∃ u ∈ values, Term.eqb u o = true)
  | .disjoint p => ∀ v ∈ values, ¬ ∃ u ∈ evalPath g focus p, Term.eqb u v = true
  | .lessThan p => ∀ v ∈ values, ∀ w ∈ evalPath g focus p, termLt v w = true
  | .lessThanOrEquals p => ∀ v ∈ values, ∀ w ∈ evalPath g focus p, termLe v w = true
  | .subsetOf p => ∀ v ∈ values, ∃ u ∈ evalPath g focus p, Term.eqb u v = true
  | .closed ignored => ClosedOk g values fun _ => pathPredicatesOfShape sg s ++ ignored
  | .closedByTypes table ignored => ClosedOk g values (byTypesAllowed g table ignored)
  | _ => True

mutual
  /-- §3.4 conformance of a focus node to a shape at a nesting budget,
  with SHACL 1.2 conformance checking: when the shape's own severity is
  in the disallowed set, every value node satisfies every per-value
  component, every aggregate component holds over the value nodes, and
  the logical and shape-based components hold by recursion; whatever
  the shape's severity, the focus node's value nodes conform to every
  property shape (whose results carry the property shape's own
  severity). At budget 0 the relation is vacuously true, matching the
  engine's sound-by-omission fuel exhaustion. -/
  def Conforms (env : ValidationEnv) (g : Graph) (sg : List Shape) (node : Term) (s : Shape) :
      Nat → Prop
    | 0 => True
    | fuel + 1 =>
      let values := valueNodes env g node s
      (env.blocks s.severity = true →
        (∀ v ∈ values, ∀ cc ∈ s.constraints, ValueConforms env g sg v cc fuel) ∧
        (∀ cc ∈ s.constraints, FocusSatisfies env g sg node s cc values) ∧
        (∀ cc ∈ s.constraints, AggConforms env g sg s values cc fuel)) ∧
      (∀ v ∈ values, ∀ r ∈ s.propertyRefs, ∀ ps, lookupShape r sg = some ps →
        Conforms env g sg v ps fuel)

  /-- A value node against one component, the recursive ones by
  `Conforms` at the smaller budget (§4.6, §4.7.1). -/
  def ValueConforms (env : ValidationEnv) (g : Graph) (sg : List Shape) (v : Term)
      (cc : Constraint) : Nat → Prop
    | 0 => True
    | fuel + 1 =>
      match cc with
      | .notOf r => ∀ rs, lookupShape r sg = some rs → ¬ Conforms env g sg v rs fuel
      | .andOf rs => ∀ r ∈ rs, ∀ s2, lookupShape r sg = some s2 → Conforms env g sg v s2 fuel
      | .orOf rs => ∃ r ∈ rs, ∃ s2, lookupShape r sg = some s2 ∧ Conforms env g sg v s2 fuel
      | .xoneOf rs =>
        (rs.filter fun r => match lookupShape r sg with
          | none => false
          | some s2 => env.conforms (collectShapeViolations env g sg v s2 fuel)).length = 1
      | .nodeOf r => ∀ s2, lookupShape r sg = some s2 → Conforms env g sg v s2 fuel
      | .nodeByExpression expr => ∀ st ∈ env.evalExpr expr (some v), ∀ r,
          termToShapeRef st = some r → ∀ s2, lookupShape r sg = some s2 →
            Conforms env g sg v s2 fuel
      | .memberShape r => ∃ members, shaclListMembers g v = some members ∧
          ∀ s2, lookupShape r sg = some s2 → ∀ m ∈ members, Conforms env g sg m s2 fuel
      | _ => ValueSatisfies g cc v

  /-- §4.7.2 / §4.7.3 qualified cardinality, by the engine's count. -/
  def AggConforms (env : ValidationEnv) (g : Graph) (sg : List Shape) (s : Shape)
      (values : List Term) (cc : Constraint) : Nat → Prop
    | 0 => True
    | fuel + 1 =>
      match cc with
      | .qualifiedMinCount qref n d => n ≤ qualifyingCount env g sg s values qref d fuel
      | .qualifiedMaxCount qref n d => qualifyingCount env g sg s values qref d fuel ≤ n
      | .someValue r => ∀ rs, lookupShape r sg = some rs →
          ∃ v ∈ values, env.conforms (collectShapeViolations env g sg v rs fuel) = true
      | _ => True
end

/-- §3.1 / SHACL 1.2 §conformance-definition: a data graph conforms to
a shapes graph iff every focus node of every shape conforms, at the
engine's budget. -/
def GraphConforms (env : ValidationEnv) (g : Graph) (sg : ShapesGraph) : Prop :=
  ∀ s ∈ sg.shapes, ∀ fn ∈ shapeFocusNodes env g sg.shapes (distinctSubjects g) s,
    Conforms env g sg.shapes fn s (validateFuel sg.shapes)

end Spec

end L4Factoidal.SHACL
