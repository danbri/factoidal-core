---
title: SPARQL-RL
description: SPARQL 1.2 RL rules (W3C editor's draft) run in the page, OWL 2 RL written as SPARQL-RL rules, what the Lean theorems prove, and how SPARQL-RL compares with RIF, SWRL, SPIN, SHACL rules, N3, Datalog and OWL 2 RL.
layout: hub.njk
tests: tests/hub/hub_sparql-rl_test.mjs
---

# SPARQL-RL

[Hub](../) · SPARQL 1.2 RL, RIF Core, OWL 2 RL

SPARQL-RL (SPARQL 1.2 RL) is a rule language for RDF. It is being written
by the W3C Data Shapes Working Group. The draft is an editor's draft, not a
W3C Recommendation, and it can still change:
[w3c.github.io/data-shapes/sparql12-rl/](https://w3c.github.io/data-shapes/sparql12-rl/).
The repository holds a copy of the draft and its test suite in
`third_party/testing/sparql-rl/` (data-shapes commit fe4eed4). Until
August 2026 the same work was called "SHACL 1.2 Rules"
(`third_party/testing/sparql-rl/spec/CHANGES.md`, entry 2026-08-19).

Factoidal implements the draft's `infer` operation in Lean 4
(`formal/lean4/L4Factoidal/SPARQLRL/`). The npm package has it as
`Factoidal.sparqlRlInfer(data, rules, options)` (it is in the published
release 0.21.0). The cells on this page call it in release
{{ factoidalRelease.version }}. The draft's second operation, `query`
(can a goal pattern be derived, and how), is not implemented.

## The language

The draft calls SPARQL-RL "a Datalog-style rules language for RDF". A rule
has a head of triple templates and a body of triple patterns, written as in
SPARQL:

```
RULE { ?x :exposedTo ?v } WHERE { ?x :dependsOn ?y . ?y :exposedTo ?v }
```

| Element | Meaning |
|---|---|
| `RULE { head } WHERE { body }` | for each solution of the body, add the head triples |
| `DATA { triples }` | triples that are part of the rule set; they are added to the evaluation graph |
| `FILTER ( expr )` | keep a solution when the SPARQL 1.2 expression is true |
| `NOT { patterns }` | negation as failure, against the evaluation graph |
| `WHERE DATA { … }`, `NOT DATA { … }` | match, or fail to match, the base graph only (not derived triples) |
| `SET ( ?v := expr )` | bind a new variable; an error in `expr` drops the solution |
| `GROUP BY ?k { patterns } [ ?n := COUNT(*) … ]` | group and aggregate: `COUNT`, `COUNT DISTINCT`, `MIN`, `MAX`, `SUM` |
| `:p/:q`, `^:p` | sequence and inverse paths, expanded to triple patterns |
| `[]` or `_:b` in a head | a fresh blank node for each solution |
| `<<( s p o )>>` | an RDF 1.2 triple term, in a pattern or in a head |
| `IMPORTS <iri>` | another rule set (optional in the draft; `sparqlRlInfer` refuses it) |

**Run-once rules.** A rule is run-once when its body has a `SET` or a
`GROUP`, or its head has a blank node or a triple term with a variable in
it. Such a rule runs exactly once, after every rule it depends on and before
every rule that depends on it. That keeps it from feeding itself and making
new terms without end. All other rules are *general rules*.

**Stratification.** Each triple pattern of a body is compared with each
head template. A match is a dependency. The dependency is *closed* when the
pattern is inside a `NOT` or the depending rule is run-once; otherwise it
is *open*. The draft's algorithm puts every rule in a stratum so that an
open dependency points to the same or a lower stratum and a closed one to a
strictly lower one. A rule set for which no such assignment exists is
rejected.

**Evaluation.** The strata run in order. In each stratum the run-once
rules run once, then the general rules run until a round adds nothing. The
result is the *inference graph*: the triples derived (and the `DATA`
triples) that are not in the base graph. Factoidal evaluates the general
rules semi-naively: after the first round, a rule only looks for solutions
that use at least one triple the previous round added. The section on
theorems says what is proved about that.

## The worked example of the draft

The draft explains evaluation with five rules about software components.
`R1` to `R3` are general rules in stratum 0. `R4` has a `NOT` and `R5` has
a blank node in its head, so both go to stratum 1 and see every
`:criticallyExposed` triple before they run.

```observable-js
workedData = `@prefix : <http://example/> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
:frontend rdf:type :Component ; :dependsOn :app .
:app      rdf:type :Component ; :dependsOn :db , :logger .
:db       rdf:type :Component ; :hasVulnerability :vuln1 .
:logger   rdf:type :Component .
:vuln1    :severity 9.1 .`
```

```observable-js
workedRules = `PREFIX : <http://example/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
# R1
RULE { ?x :exposedTo ?v } WHERE { ?x :hasVulnerability ?v }
# R2
RULE { ?x :exposedTo ?v } WHERE { ?x :dependsOn ?y . ?y :exposedTo ?v }
# R3
RULE { ?x :status :criticallyExposed }
WHERE { ?x :exposedTo ?v . ?v :severity ?s . FILTER(?s >= 9.0) }
# R4
RULE { ?x :status :safeToDeploy }
WHERE { ?x rdf:type :Component . NOT { ?x :status :criticallyExposed } }
# R5
RULE { [] rdf:type :Notification ; :concerns ?x }
WHERE { ?x :status :criticallyExposed }`
```

```observable-js
exposure = Factoidal.sparqlRlInfer(workedData, workedRules, { format: 'turtle' })
```

The inference graph, 13 triples (the blank-node labels the engine picks
are written `[]` here):

<!-- expect exposure workedData workedRules -->
```text
:app :exposedTo :vuln1 .
:app :status :criticallyExposed .
:db :exposedTo :vuln1 .
:db :status :criticallyExposed .
:frontend :exposedTo :vuln1 .
:frontend :status :criticallyExposed .
:logger :status :safeToDeploy .
[] :concerns :app .
[] :concerns :db .
[] :concerns :frontend .
[] rdf:type :Notification .
[] rdf:type :Notification .
[] rdf:type :Notification .
```

This is the inference graph the draft's own trace ends with. Only
`:logger` is safe to deploy: had `R4` run in the first round, before
`:frontend :status :criticallyExposed` was derived, it would also have
called `:frontend` safe.

## Data blocks and assignment

A `DATA` block adds triples to the evaluation graph; they are part of the
inference graph when the base graph does not have them. `SET` computes a
value. A rule with `SET` is run-once.

```observable-js
riskRules = `PREFIX : <http://example/>
DATA { :vuln1 :exploitLikelihood 0.5 }
RULE { ?x :risk ?r }
WHERE { ?x :hasVulnerability ?v . ?v :severity ?s . ?v :exploitLikelihood ?p
        SET ( ?r := ?s * ?p ) }`
```

```observable-js
risk = Factoidal.sparqlRlInfer(workedData, riskRules, { format: 'turtle' })
```

<!-- expect risk workedData riskRules -->
```text
:db :risk 4.55 .
:vuln1 :exploitLikelihood 0.5 .
```

## Grouping and aggregation

```observable-js
countRules = `PREFIX : <http://example/>
RULE { ?x :dependencyCount ?n }
WHERE { GROUP BY ?x { ?x :dependsOn ?y } [ ?n := COUNT(*) ] }`
```

```observable-js
dependencyCounts = Factoidal.sparqlRlInfer(workedData, countRules, { format: 'turtle' })
```

<!-- expect dependencyCounts workedData countRules -->
```text
:app :dependencyCount 2 .
:frontend :dependencyCount 1 .
```

## The base graph against derived triples

`WHERE DATA` and `NOT DATA` read only the base graph. Here the first rule
derives `:db :exposedTo :vuln1`, but `NOT DATA` asks about
`:hasVulnerability` in the input, so the derived triple does not matter.

```observable-js
baseRules = `PREFIX : <http://example/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
RULE { ?x :exposedTo ?v } WHERE { ?x :hasVulnerability ?v }
RULE { ?x :directlyExposed true } WHERE DATA { ?x :hasVulnerability ?v }
RULE { ?x :noDirectVulnerability true }
WHERE { ?x rdf:type :Component NOT DATA { ?x :hasVulnerability ?v } }`
```

```observable-js
baseOnly = Factoidal.sparqlRlInfer(workedData, baseRules, { format: 'turtle' })
```

<!-- expect baseOnly workedData baseRules -->
```text
:app :noDirectVulnerability true .
:db :directlyExposed true .
:db :exposedTo :vuln1 .
:frontend :noDirectVulnerability true .
:logger :noDirectVulnerability true .
```

## Paths and triple terms

A path `/` is expanded to two triple patterns with a new variable between
them. A head with a triple term that contains a variable makes the rule
run-once (draft, "Run-once rule"; W3C data-shapes issue 1293 gives the
reason).

```observable-js
pathRules = `PREFIX : <http://example/>
RULE { ?x :indirectlyDependsOn ?z } WHERE { ?x :dependsOn/:dependsOn ?z }
RULE { ?x :flaggedBy <<( ?x :hasVulnerability ?v )>> } WHERE { ?x :hasVulnerability ?v }`
```

```observable-js
pathsAndTerms = Factoidal.sparqlRlInfer(workedData, pathRules, { format: 'turtle' })
```

<!-- expect pathsAndTerms workedData pathRules -->
```text
:db :flaggedBy <<( :db :hasVulnerability :vuln1 )>> .
:frontend :indirectlyDependsOn :db .
:frontend :indirectlyDependsOn :logger .
```

## Rule sets that are rejected

`sparqlRlInfer` rejects a rule set with a syntax error, one that is not
well-formed (here `?z` in the head is bound nowhere in the body), and one
that cannot be stratified (two rules, each negating the other's head).

```observable-js
rejections = {
  const P = 'PREFIX : <http://example/>\nPREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n';
  const attempts = {
    'syntax error': P + 'RULE { ?x :p ?y } WHERE { ?x :q }',
    'not well-formed': P + 'RULE { ?x :p ?z } WHERE { ?x :dependsOn ?y }',
    'not stratifiable': P + `RULE { ?x :p :a } WHERE { ?x rdf:type :Component NOT { ?x :q :a } }
RULE { ?x :q :a } WHERE { ?x rdf:type :Component NOT { ?x :p :a } }`,
  };
  const out = [];
  for (const [ruleSet, rules] of Object.entries(attempts)) {
    try {
      await Factoidal.sparqlRlInfer(workedData, rules, { format: 'turtle' });
      out.push({ ruleSet, result: 'accepted' });
    } catch (e) {
      out.push({ ruleSet, result: e.message });
    }
  }
  return out;
}
```

| Rule set | Message in 0.21.0 |
|---|---|
| syntax error | `sparqlRlInfer: syntax error at 117: expected an RDF term` |
| not well-formed | `sparqlRlInfer: the rule set is not well-formed` |
| not stratifiable | `sparqlRlInfer: the rule set does not meet the stratification condition` |

## The same rules in RIF Core

RIF Core has no negation, no assignment and no aggregates, so of the
worked example only `R1` and `R2` can be written in it. In RIF's XML
syntax a triple is a frame `x[p -> v]`:

```observable-js
rifRules = {
  const iri = (s) => `<Const type="http://www.w3.org/2007/rif#iri">http://example/${s}</Const>`;
  const v = (n) => `<Var>${n}</Var>`;
  const frame = (o, p, x) => `<Frame><object>${o}</object><slot ordered="yes">${iri(p)}${x}</slot></Frame>`;
  const rule = (vars, body, head) => `<sentence><Forall>${vars.map((n) => `<declare>${v(n)}</declare>`).join('')}
  <formula><Implies><if>${body}</if><then>${head}</then></Implies></formula></Forall></sentence>`;
  return `<?xml version="1.0" encoding="UTF-8"?>
<Document xmlns="http://www.w3.org/2007/rif#"><payload><Group>
${rule(['x', 'v'], frame(v('x'), 'hasVulnerability', v('v')), frame(v('x'), 'exposedTo', v('v')))}
${rule(['x', 'y', 'v'],
  `<And><formula>${frame(v('x'), 'dependsOn', v('y'))}</formula><formula>${frame(v('y'), 'exposedTo', v('v'))}</formula></And>`,
  frame(v('x'), 'exposedTo', v('v')))}
</Group></payload></Document>`;
}
```

`Factoidal.rifEval` returns the input with the derived triples;
`sparqlRlInfer` returns only the derived triples. The next cell runs both
and compares the `:exposedTo` triples:

```observable-js
rifVsSrl = {
  const base = await Factoidal.parse(workedData, { format: 'turtle' });
  const rif = await Factoidal.rifEval(base, rifRules);
  const srl = await Factoidal.sparqlRlInfer(base, `PREFIX : <http://example/>
RULE { ?x :exposedTo ?v } WHERE { ?x :hasVulnerability ?v }
RULE { ?x :exposedTo ?v } WHERE { ?x :dependsOn ?y . ?y :exposedTo ?v }`);
  const exposed = (ds) => [...ds]
    .filter((q) => q.predicate.value === 'http://example/exposedTo')
    .map((q) => `${q.subject.value} ${q.object.value}`).sort();
  return { rif: exposed(rif), sparqlRl: exposed(srl), same: exposed(rif).join() === exposed(srl).join(),
           rifSize: rif.size, inputSize: base.size, sparqlRlSize: srl.size };
}
```

Both give the same three triples (`:app`, `:db` and `:frontend` exposed to
`:vuln1`); `rifSize` is 12, the 9 input triples and the 3 derived ones.

## OWL 2 RL as SPARQL-RL rules

`formal/lean4/L4Factoidal/SPARQLRL/OwlRl.lean` writes the OWL 2 RL/RDF rule
tables (OWL 2 Profiles §4.3, Tables 4 to 9) as one SPARQL-RL document. Each
rule carries its table id in a comment. The decisions recorded in its
header:

1. Every derived triple is an RDF triple. The tables allow a literal in
   subject position; the rules add `FILTER(isIRI(?v) || isBlank(?v))` where
   a head moves an object into subject position.
2. RDF lists (`LIST[…]` in the tables) are walked with recursive helper
   rules in the namespace `urn:x-factoidal:owlrl#`. `prp-spo2`
   (property chains) and `prp-key` (keys) cannot be written that way,
   because the rule that builds the needed relation would be run-once and
   could not recurse. They are unrolled for lists of 1 to 8 members.
3. A clash row (no conclusion) is a rule that adds a marker triple
   `h:result h:clash "<table id>"`; SPARQL-RL has no way to report a
   contradiction.
4. The datatype rows of Table 8 are not rules: they conclude triples with a
   literal subject, or need the datatype map.
5. `cls-maxqc3` and `cls-maxqc4` are rules, in a separate section, because
   the Lean OWL 2 RL closure does not have them.

The document has 95 rules (93 without `cls-maxqc3` and `cls-maxqc4`), and it
is one stratum of general rules (`#guard`s in `OwlRlTests.lean`).
`OwlRlDiff.lean` compares its inference graph with the table rows of the
Lean OWL 2 RL closure. Over the W3C OWL 2 test catalogs
(`l4owl-probe --srl-diff`), pull request
[danbri/factoidal-core#163](https://github.com/danbri/factoidal-core/pull/163)
reports 928 agree, 0 differ, 3 skipped (out of 931). That number is from
the pull request, not from a record in the repository.

Five of those rules, copied from `OwlRl.lean`, run here over a small
ontology. Every triple they derive is also in the engine's own OWL 2 RL
closure (`Factoidal.closure(data, 'owl-rl')`):

```observable-js
owlOntology = `@prefix : <http://example/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:dependsOn a owl:TransitiveProperty ; rdfs:domain :Component .
:usedBy owl:inverseOf :dependsOn .
:Component rdfs:subClassOf :Asset .
:frontend :dependsOn :app . :app :dependsOn :db .`
```

```observable-js
owlRules = `PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
# prp-dom
RULE { ?x rdf:type ?c } WHERE { ?p rdfs:domain ?c . ?x ?p ?y }
# prp-trp
RULE { ?x ?p ?z } WHERE { ?p rdf:type owl:TransitiveProperty . ?x ?p ?y . ?y ?p ?z }
# prp-inv1
RULE { ?y ?p2 ?x } WHERE {
  ?p1 owl:inverseOf ?p2 FILTER(isIRI(?p1) && isIRI(?p2)) ?x ?p1 ?y FILTER(isIRI(?y) || isBlank(?y)) }
# prp-inv2
RULE { ?y ?p1 ?x } WHERE {
  ?p1 owl:inverseOf ?p2 FILTER(isIRI(?p1) && isIRI(?p2)) ?x ?p2 ?y FILTER(isIRI(?y) || isBlank(?y)) }
# cax-sco
RULE { ?x rdf:type ?c2 } WHERE { ?c1 rdfs:subClassOf ?c2 . ?x rdf:type ?c1 }`
```

```observable-js
owlDerived = Factoidal.sparqlRlInfer(owlOntology, owlRules, { format: 'turtle' })
```

<!-- expect owlDerived owlOntology owlRules -->
```text
:app :usedBy :frontend .
:app rdf:type :Asset .
:app rdf:type :Component .
:db :usedBy :app .
:db :usedBy :frontend .
:frontend :dependsOn :db .
:frontend rdf:type :Asset .
:frontend rdf:type :Component .
```

```observable-js
owlCheck = {
  const closure = await Factoidal.closure(owlOntology, 'owl-rl', { format: 'turtle' });
  const key = (q) => `${q.subject.value} ${q.predicate.value} ${q.object.value}`;
  const inClosure = new Set([...closure].map(key));
  const derived = Array.from(owlDerived);
  return { derived: derived.length, alsoInClosure: derived.filter((q) => inClosure.has(key(q))).length };
}
```

## What the Lean theorems prove

Two files hold proofs about the evaluator. Every name below is a
`theorem` in the file named; the page's test checks that.

**Semi-naive equals naive** (`SemiNaiveTheorems.lean`). The executable
loop over the general rules of a stratum (`generalLoop`, in `Eval.lean`)
gives the same triples as a naive loop that evaluates every rule against
the whole graph in each round. Its hypotheses: no rule is run-once; no
pattern inside a `NOT` matches a head of the same rules (`NegBlind`, which
is what stratification gives a stratum); and the graph indexes are
consistent (`IGraph.WF`).

| Theorem | File | Statement |
|---|---|---|
| `generalLoop_eq_naiveLoop` | `formal/lean4/L4Factoidal/SPARQLRL/SemiNaiveTheorems.lean` | for the same fuel, the semi-naive loop and the naive loop return the same triples |
| `generalLoop_sound` | `formal/lean4/L4Factoidal/SPARQLRL/SemiNaiveTheorems.lean` | every triple of the result is in the input or an instance of a rule head |
| `generalLoop_saturated` | `formal/lean4/L4Factoidal/SPARQLRL/SemiNaiveTheorems.lean` | when one more round changes nothing, the result is closed under the rules |
| `generalLoop_least` | `formal/lean4/L4Factoidal/SPARQLRL/SemiNaiveTheorems.lean` | the result is inside every set that contains the input, is closed under the rules and adds only head instances (least fixed point) |
| `semi_round_new` | `formal/lean4/L4Factoidal/SPARQLRL/SemiNaiveTheorems.lean` | one semi-naive round adds exactly the triples one naive round adds |
| `Sem_decompose` | `formal/lean4/L4Factoidal/SPARQLRL/SemiNaiveTheorems.lean` | the Δ-decomposition: a body solution matches only old triples, or its first new triple is at some position `k` |
| `mem_evalSeq` | `formal/lean4/L4Factoidal/SPARQLRL/SemiNaiveTheorems.lean` | the executable body evaluator (`evalSeq`, with its hash indexes) agrees with the declarative semantics `Sem` |

**One semantics for basic graph patterns** (`BgpAgreement.lean`). On the
fragment both define (variables, IRIs and literals, and triple terms of
those; no blank node in a body pattern, no literal subject), SPARQL-RL
matching has the same solutions as the repository's SPARQL algebra
(`SPARQL.evalTP`, `SPARQL.evalBgp`). The theorems are about membership, not
order or multiplicity.

| Theorem | File | Statement |
|---|---|---|
| `matchTriple_mem_iff_evalTP` | `formal/lean4/L4Factoidal/SPARQLRL/BgpAgreement.lean` | one triple pattern: the SPARQL-RL solutions are the SPARQL `evalTP` solutions |
| `matchTriple_ofGraph_mem_iff_evalTP` | `formal/lean4/L4Factoidal/SPARQLRL/BgpAgreement.lean` | the same, for the indexed graph built from an RDF graph |
| `evalSeq_triples_mem_iff_evalBgpFrom` | `formal/lean4/L4Factoidal/SPARQLRL/BgpAgreement.lean` | a body of triple patterns, from one solution, agrees with `evalBgpFrom` |
| `evalSeq_triples_ofGraph_mem_iff_evalBgp` | `formal/lean4/L4Factoidal/SPARQLRL/BgpAgreement.lean` | a body of triple patterns agrees with SPARQL `evalBgp` |
| `Src.mem_candidates` | `formal/lean4/L4Factoidal/SPARQLRL/BgpAgreement.lean` | the index lookup returns every graph triple that agrees with the bound positions, and only graph triples |
| `IGraph.ofGraph_represents` | `formal/lean4/L4Factoidal/SPARQLRL/BgpAgreement.lean` | the indexed graph built from an RDF graph holds exactly its triples |

**Not proved** (from the module headers): that the fuel `evalLayers` gives
is enough to reach the fixed point; that `stratify` establishes `NegBlind`
(it is a hypothesis); that the draft's rule-at-a-time loop and the
round-at-a-time naive loop have the same fixed point; anything about
run-once rules, `SET`, `GROUP`, or the parser. The OWL 2 RL rule set is
checked by `#guard`s and the differential run, not by a theorem.

## SPARQL-RL and other rule languages

Status entries marked † were checked against the W3C page of the
specification on 2026-10-28; the rest of each row is a summary from those
documents and from general knowledge, and entries marked ‡ were not
checked against the specification text. Factoidal scores are from the
runs listed under the table.

| | Syntax | Semantics | Negation | Aggregates | RDF 1.2 triple terms | Built-ins | Status | In Factoidal |
|---|---|---|---|---|---|---|---|---|
| **SPARQL-RL** | SPARQL-like text (`RULE … WHERE …`) | stratified fixpoint; run-once rules | `NOT`, `NOT DATA`, stratified | `GROUP` with `COUNT`, `COUNT DISTINCT`, `MIN`, `MAX`, `SUM` (run-once) | in patterns and heads | SPARQL 1.2 functions in `FILTER` and `SET` | W3C editor's draft (Data Shapes WG) | `sparqlRlInfer`; W3C SPARQL-RL suite 239/239 |
| **RIF Core** | XML (the presentation syntax is not normative ‡) | Horn rules, least model | none | none | none (RIF predates RDF 1.2) | RIF-DTB functions and predicates | W3C Recommendation, 2nd ed., 5 Feb 2013 † | `rifEval`; Core suite 42/42 decided, 1 undecided, 3 excluded |
| **RIF BLD** | XML | Horn rules with equality, function symbols, lists | none † | none | none | RIF-DTB | W3C Recommendation, 5 Feb 2013 † | not implemented (out of scope) |
| **RIF PRD** | XML | production rules: conditions and actions (`Assert`, `Retract`, `Modify`) | yes † | none ‡ | none | RIF-DTB | W3C Recommendation, 2nd ed., 5 Feb 2013 † | not implemented (out of scope) |
| **SWRL** | OWL/RDF/XML, human-readable form | Horn rules over OWL classes and properties; OWL DL + SWRL is undecidable ‡ | none ‡ | none ‡ | none | `swrlb:` built-ins | W3C Member Submission, 21 May 2004 † | not implemented |
| **SPIN** | SPARQL `CONSTRUCT`/`UPDATE` stored as RDF, attached to classes | rules run until no change; order engine-defined ‡ | whatever SPARQL gives (`NOT EXISTS`, unstratified) ‡ | SPARQL aggregates ‡ | none (SPARQL 1.1) | SPARQL functions, SPIN functions | W3C Member Submission, 22 Feb 2011 † | not implemented |
| **SHACL-AF rules** | `sh:TripleRule`, `sh:SPARQLRule` in RDF, attached to shapes | ordered by `sh:order`; iteration engine-defined ‡ | via SPARQL ‡ | via SPARQL ‡ | none | SPARQL functions | W3C Working Group Note, 8 Jun 2017 † | not implemented as SHACL-AF; its SHACL 1.2 successor became SPARQL-RL |
| **N3 rules** | Notation3 `{ … } => { … }` | forward and backward rules over formulas | scoped negation as failure (`log:notIncludes`) † | through built-ins (`log:collectAllIn`) † | not part of N3 ‡ | `math:`, `string:`, `list:`, `log:` † | W3C N3 Community Group report, not standards track † | not implemented (no N3 reader) |
| **Datalog** | Horn clauses over relations | least model; stratified negation and aggregation in common extensions | in extensions | in extensions | n/a | varies | no W3C or ISO standard ‡ | no Datalog syntax; SPARQL-RL calls itself Datalog-style |
| **OWL 2 RL** | not a rule language: fixed rule tables over OWL vocabulary | least fixpoint of the tables | clash rows only | none | none | datatype rows (Table 8) | W3C Recommendation, 2nd ed., 11 Dec 2012 † | `closure(data, 'owl-rl')`; profile-RL catalog, approved and in scope, 102/102; also as SPARQL-RL rules (above) |

Where the Factoidal numbers come from:

- SPARQL-RL: `formal/lean4/.lake/build/bin/l4shacl-rules third_party/testing/sparql-rl/tests`,
  run 2026-10-28: syntax 171/171, wellformed 8/8, stratification 14/14,
  eval 35/35, eval2 6/6, examples 5/5; 239 pass, 0 fail (out of 239). The
  same numbers are in `docs/20261027-sparql-rl.md`. The July 2026 copy of
  the suite (`shacl12-test-suite/tests/rules`) scores 85/88: its 3 failing
  tests use `BIND`, which the current draft replaced with `SET`.
- RIF Core: `formal/lean4/.lake/build/bin/l4rif`, run 2026-10-28, over the
  46-test W3C Core suite (`third_party/testing/rif-core-suite/`): 42 pass,
  0 fail (out of 42 decided); 1 undecided (`RDF_Combination_Constant_Equivalence_4`,
  a built-in outside the implemented subset); 3 excluded for defective
  test data ([danbri/factoidal#1031](https://github.com/danbri/factoidal/issues/1031)),
  whose corrected copies in `tests/rif-local` pass 3/3. An undecided case is
  never counted as a pass. The F\*-era numbers in
  `docs/claude-rules/w3c-completeness-ledger.md` are for the earlier engine.
- OWL 2 RL: `docs/web/hub/records/lean-scoreboard-2026-10-25.txt`, row
  "profile-RL.rdf Approved, in scope".

## Which to use

- **SPARQL-RL** when the rules are about RDF data and the people writing
  them know SPARQL: the patterns are SPARQL patterns, negation and
  aggregation have a defined meaning through stratification, and RDF 1.2
  triple terms work. Weigh that it is a draft.
- **RIF Core** when rules have to be exchanged with systems that read RIF,
  or when a W3C Recommendation is required. It is positive Horn rules only;
  RDF goes through the frame mapping.
- **OWL 2 RL** when the rules are the meaning of an ontology rather than
  rules of your own. `closure('owl-rl')` is the faster path; the SPARQL-RL
  rule set is a readable and checkable statement of the same tables.
- **SHACL-AF rules, SPIN, SWRL, N3**: for data and tools that already use
  them. Factoidal does not run them.

## Limits and open issues

- The draft's `query` operation is not implemented; `IMPORTS` works in the
  Lean API through a loader but `sparqlRlInfer` refuses it.
- `NOW()` has one value per evaluation, given by the caller.
- No W3C eval test has a `GROUP` element yet; Factoidal follows the
  draft's algorithm as written (`docs/20261027-sparql-rl.md`).
- OWL 2 RL as SPARQL-RL: property chains and keys of more than 8 members
  are not handled,
  [danbri/factoidal#1112](https://github.com/danbri/factoidal/issues/1112).
  The Lean OWL 2 RL closure has no `cls-maxqc3` or `cls-maxqc4`,
  [danbri/factoidal#1113](https://github.com/danbri/factoidal/issues/1113).
- `RuleSet.infer` computes the stratification on every call (about 21 s
  for 93 rules in the Lean interpreter),
  [danbri/factoidal#1114](https://github.com/danbri/factoidal/issues/1114).
- The feature issue,
  [danbri/factoidal#1099](https://github.com/danbri/factoidal/issues/1099),
  is open.
- RIF Core: three W3C tests have defective data,
  [danbri/factoidal#1031](https://github.com/danbri/factoidal/issues/1031);
  `RIF/Builtins.lean` decides a named subset of the RIF-DTB built-ins, and
  a rule that needs another one makes the answer undecided
  (`RIF/Engine.lean`); RIF BLD and RIF PRD are out of scope
  (`third_party/testing/rif-core-suite/README.md`).
