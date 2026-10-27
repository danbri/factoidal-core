/-
L4Factoidal.SPARQL.PathAlternative — an alternative of IRIs as the UNION of
triple patterns (https://github.com/danbri/factoidal/issues/1008).

## The rule

SPARQL 1.1 §18.4 evaluates a property path pattern `X P Y` by the pairs the
path `P` denotes:

* a link path `iri` denotes the pairs `(s, o)` of the triples `(s, iri, o)`;
* an alternative path `P1 | P2` denotes the MULTISET UNION of the pairs of
  `P1` and of `P2` (`evalPath`'s `.alternative` arm is `++`).

§18.2.2.4 translates a link path `X iri Y` to the triple pattern `X iri Y`.
So for IRIs `p` and `q`, the pattern `?s p|q ?o` has the solutions of
`{ ?s p ?o } UNION { ?s q ?o }`, with the same multiplicity (a triple matched
by both operands gives two solutions on both sides) and, in this engine, in
the same order. `p|q|r` is `(p|q)|r` (grammar rule [89] is left-assoc) and
becomes the nested UNION.

`QueryPattern.expandIriAlternatives` makes that rewrite once, when the query
is parsed (`parseSparql`, `SPARQL/Parser.lean`), so every planner and every
evaluator downstream reads the UNION. The persisted-store planners admit a
UNION of triple patterns and refuse a property path
(`SPARQL.DatasetRestriction.plannerFragment`); before this rewrite, the
alternative `?s p|q ?o` made them read every block of a store.

The theorem is `expandIriAlternatives_lowerWith` in
`SPARQL/PathAlternativeTheorems.lean`: the rewritten pattern evaluates to the
same solution sequence, as a LIST (order and multiplicity), under every
environment, seed binding, dataset and active graph, and makes the same
SERVICE failure.

## Where the rewrite does NOT apply, and why

* An alternative with any step that is not an IRI (`^p`, `p/q`, `p*`, `p+`,
  `p?`, a negated property set). Those are not unions of triple patterns.
* An alternative step that is the `text:query` IRI
  (`FullText.fulltextQueryPred`). A triple pattern with that predicate and a
  marker literal object is a full-text search (`TriplePattern.fulltext?`), and
  the path step is an ordinary predicate lookup, so the two forms differ.
* A triple-term object (`<<( … )>>`, RDF 1.2). The path evaluator gives a
  triple term no endpoint match (`pathResultToSolutions`), and a triple
  pattern matches one position by position (`tryBindTerm`), so the two forms
  differ. `substPatternTerm` never produces a triple term, so this condition
  is stable under the substitutions LATERAL and EXISTS make.
* Inside an `EXISTS` / `NOT EXISTS` expression, a sub-SELECT, a LATERAL
  right operand, a SERVICE body and a VALUES block: the rewrite descends only
  through BGP-level operators (join, UNION, MINUS, OPTIONAL, FILTER's pattern,
  BIND's pattern, GRAPH). Those are the operators the store planners admit;
  the others keep the path, and their answers are unchanged.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

/-- Is this pattern term an RDF 1.2 triple-term pattern? -/
def PatternTerm.isTripleTerm : PatternTerm → Bool
  | .tripleTerm _ _ _ => true
  | _ => false

/-- The UNION of triple patterns that an alternative of IRIs denotes between
the endpoints `s` and `o`, or `none` when a step is not an IRI or is the
`text:query` IRI. A single IRI gives the one triple pattern of §18.2.2.4. -/
def iriAlternativeUnion (s : PatternSubject) (o : PatternTerm) :
    PropertyPath → Option QueryPattern
  | .iri p =>
      if p == fulltextQueryPred then none
      else some (.bgp [{ s := s, p := .iri p, o := o }])
  | .alternative a b =>
      match iriAlternativeUnion s o a, iriAlternativeUnion s o b with
      | some l, some r => some (.union l r)
      | _, _ => none
  | .inverse _ => none
  | .sequence _ _ => none
  | .zeroOrMore _ => none
  | .oneOrMore _ => none
  | .zeroOrOne _ => none
  | .negatedSet _ => none

/-- Replace every property-path pattern whose path is an alternative of IRIs
by the UNION of its triple patterns, through the BGP-level operators. See the
module header for the cases that keep the path. -/
def QueryPattern.expandIriAlternatives : QueryPattern → QueryPattern
  | .propertyPath s path o =>
      if o.isTripleTerm then .propertyPath s path o
      else
        match iriAlternativeUnion s o path with
        | some u => u
        | none => .propertyPath s path o
  | .join l r => .join l.expandIriAlternatives r.expandIriAlternatives
  | .union l r => .union l.expandIriAlternatives r.expandIriAlternatives
  | .minus l r => .minus l.expandIriAlternatives r.expandIriAlternatives
  | .leftJoin l r c => .leftJoin l.expandIriAlternatives r.expandIriAlternatives c
  | .filter c p => .filter c p.expandIriAlternatives
  | .bind e v p => .bind e v p.expandIriAlternatives
  | .graph n p => .graph n p.expandIriAlternatives
  | .bgp b => .bgp b
  | .lateral l r => .lateral l r
  | .values vs rows => .values vs rows
  | .service i silent p => .service i silent p
  | .serviceVar v silent p => .serviceVar v silent p
  | .subSelect q => .subSelect q
  | .empty => .empty

/-- The query with its WHERE pattern rewritten. Every other part of the query
is unchanged. -/
def Query.expandIriAlternatives : Query → Query
  | .mk form ds pattern groupBy having modifier postValues base =>
      .mk form ds pattern.expandIriAlternatives groupBy having modifier postValues base

theorem Query.expandIriAlternatives_pattern (q : Query) :
    q.expandIriAlternatives.pattern = q.pattern.expandIriAlternatives := by
  cases q; rfl

end L4Factoidal.SPARQL
