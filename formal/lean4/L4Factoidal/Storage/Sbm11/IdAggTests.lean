/-
L4Factoidal.Storage.Sbm11.IdAggTests — the grouped aggregates on ids
(`IdAgg.aggregateM`) against the reference evaluator
(https://github.com/danbri/factoidal/issues/825; record
docs/designissues/2026-10-12-sbm11-stage4.md section 16).

Each check builds a table of term ids, answers a query in two ways, and
compares:

  * the id path: `IdAgg.aggregateM` over the table, `AggStream.groupedRow` for
    each group, `AggStream.groupedTail`;
  * the reference: the table's rows decoded into solution mappings
    (a variable with the id 0 left unbound, as `decodeRowsM` leaves it), and
    `selectPost` on them.

This is the check of lemma L5k of the end-to-end record (the groups, representative rows and value
streams of the id path are those of `groupWhere` on the decoded rows) on small
tables that hold every value form the aggregates tell apart: integers of
several datatypes, an integer in a non-canonical form, an integer beyond the
inline range, decimals, doubles, a string no number can be read from, language
tagged and typed literals, dates, booleans, IRIs and blank nodes; unbound
values; groups keyed by IRIs, blank nodes, integers and booleans; empty
groups; a variable no column holds. A table the plan does not admit (a literal
or an unbound value in a group column) must make `aggregateM` answer `none`.
A disagreement fails the build.
-/
import L4Factoidal.Storage.Sbm11.IdAgg
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.Storage.Sbm11.IdAggTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.AggStream
open L4Factoidal.Qlvr (Table)

/-! ## Sample terms and ids -/

def xsdT (s : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ s

def iri (s : String) : Term :=
  if h : isIri s = true then .iri ⟨s, h⟩ else .bnode s

def typed (lex dt : String) : Term :=
  match mkLit lex (xsdT dt) none none with
  | some t => t
  | none => .bnode "bad"

def lang (lex tag : String) : Term := .literal (Literal.langString lex tag)

def str (lex : String) : Term := .literal (Literal.string lex)

def int (n : Int) : Term := typed (toString n) "integer"

/-- The dictionary: every sample term that is not inline. -/
def dict : Array Term := #[
  .bnode "b1", .bnode "b2",
  iri "http://ex/G1", iri "http://ex/G2", iri "http://ex/G3", iri "http://ex/x1", iri "http://ex/x2",
  str "abc", str "plain", lang "one" "en", lang "two" "fr", lang "zwei" "de",
  typed "5.5" "decimal", typed "-2.25" "decimal", typed "2.5" "decimal", typed "1.5E1" "double", typed "2.5E0" "double",
  typed "007" "integer", typed "36028797018963968" "integer", typed "-36028797018963969" "integer",
  typed "2020-01-01" "date", typed "2021-06-30" "date", typed "2020-01-01T10:00:00" "dateTime",
  typed "1" "boolean", typed "TRUE" "boolean"]

def tagOfTerm : Term → Nat
  | .bnode _ => 1
  | .iri _ => 2
  | .literal _ => 3
  | .tripleTerm _ _ _ => 9

/-- The id of a term: its inline code, else its place in `dict` under its tag. -/
def idOfTerm (t : Term) : UInt64 :=
  match inlineCode? t with
  | some c => c.toUInt64
  | none => (UInt64.ofNat (tagOfTerm t) <<< 60) ||| UInt64.ofNat (dict.idxOf t)

def termOfId (x : UInt64) : ExceptT String Id Term :=
  let tag := (x >>> 60).toNat
  if tag == 4 || tag == 5 then
    match ofInlineCode? x.toNat with
    | some t => pure t
    | none => throw "inline id"
  else
    match dict[(x &&& 0x0FFFFFFFFFFFFFFF).toNat]? with
    | some t => pure t
    | none => throw "no such id"

def put64 (b : ByteArray) (x : UInt64) : ByteArray :=
  (List.range 8).foldl (fun acc k => acc.push ((x >>> (8 * k.toUInt64)).toUInt8)) b

/-- A table of ids; `none` is an unbound value (the id 0). -/
def mkTable (vars : Array String) (rows : List (List (Option Term))) : Table :=
  { vars, rows := rows.length,
    cols := (List.range vars.size).toArray.map fun c =>
      rows.foldl (fun acc r => put64 acc (match r[c]! with | some t => idOfTerm t | none => 0)) ByteArray.empty }

/-- The rows of the table as solution mappings, as `decodeRowsM` makes them. -/
def decodeRows (t : Table) : SolutionSeq :=
  (List.range t.rows).map fun i =>
    (List.range t.vars.size).filterMap fun c =>
      let x := t.at c i
      if x == 0 then none
      else match (termOfId x).run with
        | .ok tm => some (t.vars[c]!, tm)
        | .error _ => none

/-- The id path and the reference give the same rows for `text` over the table. -/
def agrees (text : String) (t : Table) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok q =>
    match aggPlan? q with
    | none => false
    | some p =>
      match (IdAgg.aggregateM termOfId t p).run with
      | .ok (some r) =>
        let omega' := (List.range r.reps.size).map fun g =>
          groupedRow {} p.items (r.vals[g]!).toList r.reps[g]!
        groupedTail {} Graph.empty p.items p.md omega' == selectPost {} Graph.empty q (decodeRows t)
      | _ => false

/-- `aggregateM` declines the table. -/
def declines (text : String) (t : Table) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok q =>
    match aggPlan? q with
    | none => false
    | some p => match (IdAgg.aggregateM termOfId t p).run with
      | .ok none => true
      | _ => false

/-- `aggPlan?` does not take the query. -/
def refused (text : String) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok q => (aggPlan? q).isNone

/-! ## Tables -/

def g1 := iri "http://ex/G1"
def g2 := iri "http://ex/G2"
def g3 := iri "http://ex/G3"
def b1 := Term.bnode "b1"
def b2 := Term.bnode "b2"

/-- Group, value, extra: numbers of every kind, a string, an unbound value. -/
def numbers : Table := mkTable #["g", "v", "x"] [
  [some g1, some (int 10), some (iri "http://ex/x1")],
  [some g1, some (typed "20" "int"), some (iri "http://ex/x2")],
  [some g2, some (typed "5.5" "decimal"), some (iri "http://ex/x1")],
  [some g1, some (typed "1.5E1" "double"), none],
  [some g2, some (str "abc"), some (str "plain")],
  [some g3, none, some (iri "http://ex/x1")],
  [some g2, some (int (-7)), some (iri "http://ex/x2")],
  [some g3, some (int 36028797018963968), some (iri "http://ex/x1")],
  [some g1, some (typed "007" "integer"), some (iri "http://ex/x2")],
  [some b1, some (typed "-2.25" "decimal"), none],
  [some b1, some (typed "2.5E0" "double"), none],
  [some b2, some (typed "300" "unsignedLong"), some (iri "http://ex/x1")],
  [some b2, some (int (-36028797018963969)), some (iri "http://ex/x2")]]

/-- Strings, language tagged literals, dates, booleans, IRIs and blank nodes in
the value column. -/
def kinds : Table := mkTable #["g", "v", "x"] [
  [some g1, some (str "abc"), none],
  [some g1, some (lang "one" "en"), none],
  [some g1, some (lang "two" "fr"), none],
  [some g1, some (str "plain"), none],
  [some g2, some (typed "2020-01-01" "date"), none],
  [some g2, some (typed "2021-06-30" "date"), none],
  [some g2, some (typed "2020-01-01T10:00:00" "dateTime"), none],
  [some g3, some (typed "true" "boolean"), none],
  [some g3, some (typed "1" "boolean"), none],
  [some g3, some (typed "false" "boolean"), none],
  [some b1, some (iri "http://ex/x1"), none],
  [some b1, some (iri "http://ex/x2"), none],
  [some b1, some b2, none],
  [some b2, some (lang "zwei" "de"), none],
  [some b2, some b1, none]]

/-- Group keys that are integers and booleans. -/
def keyed : Table := mkTable #["k", "b", "v"] [
  [some (int 1), some (typed "true" "boolean"), some (int 10)],
  [some (int 2), some (typed "false" "boolean"), some (int 20)],
  [some (int 1), some (typed "false" "boolean"), some (int 30)],
  [some (typed "1" "int"), some (typed "true" "boolean"), some (int 40)],
  [some (int 2), some (typed "true" "boolean"), none],
  [some (int (-3)), some (typed "false" "boolean"), some (typed "2.5" "decimal")]]

def empty : Table := mkTable #["g", "v", "x"] []

def wherePart : String := "WHERE { ?g <http://ex/p> ?v . ?g <http://ex/q> ?x }"

/-! ## The checks -/

-- every function, every group, all value kinds
#guard agrees s!"SELECT ?g (COUNT(*) AS ?n) (COUNT(?v) AS ?c) (SUM(?v) AS ?s) (MIN(?v) AS ?lo) (MAX(?v) AS ?hi) (AVG(?v) AS ?m) {wherePart} GROUP BY ?g" numbers
#guard agrees s!"SELECT ?g (COUNT(*) AS ?n) (COUNT(?v) AS ?c) (SUM(?v) AS ?s) (MIN(?v) AS ?lo) (MAX(?v) AS ?hi) (AVG(?v) AS ?m) {wherePart} GROUP BY ?g ORDER BY ?g" numbers
#guard agrees s!"SELECT ?g (COUNT(*) AS ?n) (COUNT(?v) AS ?c) (SUM(?v) AS ?s) (MIN(?v) AS ?lo) (MAX(?v) AS ?hi) (AVG(?v) AS ?m) {wherePart} GROUP BY ?g ORDER BY DESC(?hi) ?g LIMIT 3" numbers
#guard agrees s!"SELECT ?g (MIN(?v) AS ?lo) (MAX(?v) AS ?hi) (COUNT(?v) AS ?c) (SUM(?v) AS ?s) (AVG(?v) AS ?m) {wherePart} GROUP BY ?g" kinds
#guard agrees s!"SELECT ?g (MIN(?v) AS ?lo) (MAX(?v) AS ?hi) {wherePart} GROUP BY ?g ORDER BY ?g" kinds
-- no GROUP BY: one group, also over no rows
#guard agrees s!"SELECT (COUNT(*) AS ?n) (COUNT(?v) AS ?c) (SUM(?v) AS ?s) (MIN(?v) AS ?lo) (MAX(?v) AS ?hi) (AVG(?v) AS ?m) {wherePart}" numbers
#guard agrees s!"SELECT (COUNT(*) AS ?n) (COUNT(?v) AS ?c) (SUM(?v) AS ?s) (MIN(?v) AS ?lo) (MAX(?v) AS ?hi) (AVG(?v) AS ?m) {wherePart}" empty
#guard agrees s!"SELECT (COUNT(*) AS ?n) (SUM(?v) AS ?s) (MAX(?v) AS ?hi) {wherePart}" kinds
-- GROUP BY over no rows: no group
#guard agrees s!"SELECT ?g (COUNT(*) AS ?n) (MAX(?v) AS ?hi) {wherePart} GROUP BY ?g" empty
-- a variable no column holds
#guard agrees s!"SELECT ?g (COUNT(?z) AS ?c) (SUM(?z) AS ?s) (MAX(?z) AS ?hi) (AVG(?z) AS ?m) (MIN(?z) AS ?lo) {wherePart} GROUP BY ?g" numbers
-- a variable that is not grouped is not a SELECT item (the parser refuses it) but ORDER BY
-- can read it from the representative row
#guard agrees s!"SELECT ?g (MAX(?v) AS ?hi) {wherePart} GROUP BY ?g ORDER BY ?x ?g" numbers
#guard agrees s!"SELECT ?g (COUNT(*) AS ?n) {wherePart} GROUP BY ?g ORDER BY DESC(?x) ?g" numbers
-- the same aggregate twice, an alias used by ORDER BY, DISTINCT, OFFSET, LIMIT
#guard agrees s!"SELECT ?g (MAX(?v) AS ?a) (MAX(?v) AS ?b) (COUNT(*) AS ?n) {wherePart} GROUP BY ?g ORDER BY DESC(?n) ?g" numbers
#guard agrees s!"SELECT DISTINCT (COUNT(*) AS ?n) {wherePart} GROUP BY ?g" numbers
#guard agrees s!"SELECT ?g (COUNT(*) AS ?n) {wherePart} GROUP BY ?g ORDER BY ?g OFFSET 1 LIMIT 2" numbers
#guard agrees s!"SELECT ?g (SUM(?v) AS ?s) {wherePart} GROUP BY ?g ORDER BY ?s ?g" numbers
-- a group variable not selected, or selected after the aggregates
#guard agrees s!"SELECT (COUNT(*) AS ?n) {wherePart} GROUP BY ?g ORDER BY ?g" numbers
#guard agrees s!"SELECT (COUNT(*) AS ?n) ?g {wherePart} GROUP BY ?g ORDER BY ?n ?g" numbers
-- keys that are integers and booleans, one or two of them
#guard agrees s!"SELECT ?k (COUNT(*) AS ?n) (SUM(?v) AS ?s) (MAX(?v) AS ?hi) WHERE \{ ?x <http://ex/p> ?k . ?x <http://ex/q> ?v . ?x <http://ex/r> ?b } GROUP BY ?k ORDER BY ?k" keyed
#guard agrees s!"SELECT ?b (COUNT(?v) AS ?n) (AVG(?v) AS ?m) WHERE \{ ?x <http://ex/p> ?k . ?x <http://ex/q> ?v . ?x <http://ex/r> ?b } GROUP BY ?b ORDER BY ?b" keyed
#guard agrees s!"SELECT ?k ?b (COUNT(*) AS ?n) (MIN(?v) AS ?lo) WHERE \{ ?x <http://ex/p> ?k . ?x <http://ex/q> ?v . ?x <http://ex/r> ?b } GROUP BY ?k ?b ORDER BY ?k ?b" keyed

-- tables the plan does not admit: a literal key, an unbound key, a missing key column
#guard declines s!"SELECT ?x (COUNT(*) AS ?n) {wherePart} GROUP BY ?x" numbers
#guard declines s!"SELECT ?g ?x (COUNT(*) AS ?n) {wherePart} GROUP BY ?g ?x" numbers
#guard declines s!"SELECT ?v (COUNT(*) AS ?n) {wherePart} GROUP BY ?v" numbers
#guard declines s!"SELECT ?z (COUNT(*) AS ?n) {wherePart} GROUP BY ?z" numbers

-- queries the plan does not take
#guard refused s!"SELECT ?g (COUNT(DISTINCT ?v) AS ?n) {wherePart} GROUP BY ?g"
#guard refused s!"SELECT ?g (GROUP_CONCAT(?v) AS ?n) {wherePart} GROUP BY ?g"
#guard refused s!"SELECT ?g (SAMPLE(?v) AS ?n) {wherePart} GROUP BY ?g"
#guard refused s!"SELECT ?g (COUNT(*) AS ?n) {wherePart} GROUP BY ?g HAVING (COUNT(*) > 1)"
#guard refused s!"SELECT ?g (MAX(?v) + 1 AS ?n) {wherePart} GROUP BY ?g"
#guard refused s!"SELECT ?g (MAX(STR(?v)) AS ?n) {wherePart} GROUP BY ?g"
#guard refused s!"SELECT (COUNT(*) AS ?n) {wherePart} GROUP BY (STR(?g) AS ?s)"
#guard refused s!"SELECT ?s (COUNT(*) AS ?n) {wherePart} GROUP BY (STR(?g) AS ?s)"
#guard refused s!"SELECT ?g ?v {wherePart}"
#guard refused s!"SELECT (STR(?g) AS ?n) {wherePart}"
#guard refused s!"SELECT ?g (COUNT(*) AS ?n) {wherePart} GROUP BY ?g VALUES ?g \{ <http://ex/G1> }"

end L4Factoidal.Storage.Sbm11.IdAggTests
