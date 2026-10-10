# SPARQL DESCRIBE in the Lean tree: which resources, which description, which surfaces

Status: record of the design as it stands on 2026-10-10. Tracked at
<https://github.com/danbri/factoidal/issues/698>. Update this file when the
description policy, the resource rule or a surface changes. The worknote
index (`formal/lean4/PORT_NOTES.md`) and the `factoidal-lean-basics` skill
link here.

## 1. What the specification fixes and what it does not

SPARQL 1.1 Query section 16.4
(<https://www.w3.org/TR/sparql11-query/#describe>): "The DESCRIBE form
returns a single result RDF graph containing RDF data about resources ...
The query service determines the description". The specification fixes
WHICH resources are described and leaves WHAT is said about each to the
service.

- Section 16.4.1: the IRIs written in the DESCRIBE clause.
- Section 16.4.2: the values the solution sequence binds to the variables
  written in the clause.
- Grammar rule [11]: `DESCRIBE *` names every variable in scope in the
  WHERE clause. The parser gives it the empty target list, so `.describe []`
  means `DESCRIBE *`.

No W3C evaluation test has a DESCRIBE query: the only DESCRIBE queries in
the suites are the two sparql10 syntax tests and the protocol test
`query_content_type_describe`, which checks the media type. The unit
checks in `L4Factoidal/SPARQL/DescribeTests.lean` are therefore the only
test of the description; the W3C gates cannot move.

## 2. The resources

`evalDescribe` (`SPARQL/Query.lean`) takes the solutions from
`formSolutions`, the same pipeline ASK and CONSTRUCT use: GROUP BY, HAVING,
the trailing VALUES join, ORDER BY, OFFSET and LIMIT run before any
resource is collected. `DESCRIBE ?x WHERE { ... } LIMIT 1` describes the one
resource of the first solution.

- An IRI in the clause is described whether or not the WHERE clause matches
  (`evalDescribe_mem_of_iri`).
- A value bound to a listed variable is described when it is an IRI or a
  blank node. A literal and an RDF 1.2 triple term name no resource and are
  dropped. An unbound variable names nothing.
- After GROUP BY only the group variables are in scope, so a listed variable
  that is not a group variable names nothing.
- `DESCRIBE *` takes every value of every variable of every solution, except
  the variables `QueryPattern.rewriteBnodes` invents for blank nodes of the
  WHERE clause (`isSyntheticBnodeVar`). A blank node of the WHERE clause is
  not a variable the user wrote.

## 3. The description: Concise Bounded Description

`Graph.cbd` (`RDF/ConciseBoundedDescription.lean`) implements the W3C Member
Submission "CBD - Concise Bounded Description"
(<https://www.w3.org/Submission/CBD/>) section 2:

1. all statements with the starting node as subject;
2. recursively, for statements already included whose object is a blank
   node, all statements with that blank node as subject;
3. recursively, for statements already included, the Concise Bounded
   Description of each reification.

Clause 3 has an RDF 1.2 reading, because RDF 1.2 has no `rdf:Statement`
reification. A reification is a triple `r rdf:reifies <<( s p o )>>`. For
every included statement `s p o`, each `r` with such a triple in the source
graph is a further starting node. The triple term is compared with the
statement by `Subject.eqb`, IRI equality and `Term.eqb`. A reifier of a
reification is found the same way, because the reifies triple is itself a
statement.

An IRI object is not followed. `DESCRIBE :alice` does not describe the
people :alice knows.

The description is read from the ACTIVE DEFAULT GRAPH of the query's dataset:
the default graph after FROM and FROM NAMED are applied, as for CONSTRUCT.
Named graphs supply bindings through GRAPH clauses and are not described.

Shape. The subgraph is `g.filter (fun t => nodes.contains t.s)`, where
`nodes` is the set of starting nodes closed under clauses 2 and 3. So the
result keeps the statement order of the source graph and holds no statement
twice that the source graph does not hold twice. The union of the
descriptions of several resources is one filter, because the closure of a
union of starting sets is the union of the closures.

`nodes` comes from a worklist over two indexes built in one pass over the
graph: statements by subject, and `rdf:reifies` entries by the subject of
their triple term. A node is marked seen when it is queued, so each node is
expanded once. The fuel is `roots.length + g.length`: a queued node that is
not a starting node is the blank-node object of some statement or the
reifier of some `rdf:reifies` statement, so at most one node per statement
of `g` is queued after the starting nodes. Total by structural recursion on
the fuel; no `partial`.

Proved, in `RDF/ConciseBoundedDescription.lean` and
`RDF/ConciseBoundedDescriptionTheorems.lean`:

- `cbd_subset`: the description is a subgraph of the source graph.
- `cbd_root_triples`: every statement about a starting node is in it.
- `cbd_nil`: no starting node, no description.
- `cbd_closed_bnode` (clause 2): a statement in the description whose
  object is a blank node brings in every statement about that blank node.
- `cbd_closed_reifier` (clause 3, RDF 1.2 reading): a statement in the
  description brings in every `rdf:reifies` statement whose triple term is
  that statement.
- `cbd_least`: any set of nodes that holds the starting nodes and is closed
  under the two clauses holds the subject of every statement in the
  description. The description holds nothing the clauses do not reach.

The two closure theorems need the walk to finish within its fuel. The proof
is a potential function: the queue length plus the number of possible
candidate nodes not yet seen (`cbdUnseen`, over `cbdUniverse`, which is no
longer than the graph) does not rise at any step, falls by at least one for
the node expanded, and starts at no more than `roots.length + g.length`.

And in `SPARQL/QueryTheorems.lean`: `evalDescribe_subset` (the answer is a
subgraph of the active default graph), `evalDescribe_of_not_describe` (only a
DESCRIBE query describes) and `evalDescribe_mem_of_iri` (an IRI named in the
clause has all its statements in the answer, whatever the WHERE clause
matches).

The `#guard` cases cover the resource rules and the fixtures: a chain of 300
blank nodes, a cycle, an IRI object that is not followed, a reifier of a
reifier, FROM and FROM NAMED.

## 4. Planners must read the whole store for DESCRIBE

Every planner that opens a proper subset of a stored dataset chooses the
subset from the query's pattern: the predicate collectors, the graph-name
collector, the SBM10 zone maps, the literal and geometry index plans, the
selective paths of `Harness/IndexedBlockV3Query.lean`. For DESCRIBE that is
wrong, because the answer holds statements no pattern selects. `DESCRIBE
<x>` has an empty pattern; a planner that reads the pattern's predicates
opens no shard and describes nothing, with status 200.

`Query.patternBoundedReads` (`SPARQL/Query.lean`) is the admission test of
all of them. It is `Query.expressionsOutsidePatternExistsFree` and a refusal
of DESCRIBE (`QueryForm.readsBeyondPattern`). A DESCRIBE query makes every
collector answer `none`, and `none` means "open the complete store".
Checks: `Wasm/Ops/Store.lean` (plan modes and a stored DESCRIBE),
`SPARQL/StoreDataset.lean` (the test itself), `Wasm/native-smoke.sh` (a
two-predicate store, where the pattern predicate alone would lose a
statement).

## 5. Surfaces

| Surface | Result |
|---|---|
| `SPARQL/Query.lean` `evalDescribe` | the graph |
| `SPARQL/ProtocolService.lean` `evalQuery` | `Payload.graph`, result kind "RDF" |
| `Wasm/Ops/Query.lean` `queryDataset`, and every op that ends in `queryParsedDatasetWith` (`datasetQuery`, `storeQuery`, `storeHandleQuery`) | `{"ok":true,"kind":"describe","nquads":"..."}` |
| `Wasm/Ops/Block.lean` `queryIBK3BlockSetPreview` | the same envelope; needs no LIMIT, because the answer is a subgraph of the decoded block set |
| `Wasm/Cli.lean` `l4factoidal query` | prints the N-Triples, as for CONSTRUCT |
| `Harness/Run.lean` | compares the graph by isomorphism with an expected Turtle graph; no manifest case exists |
| `Harness/ProtocolRun.lean` | notes the triple count |
| `Harness/QuadQuery.lean`, `Harness/IndexedBlockV3Query.lean` | print the triple count and a preview, as for CONSTRUCT |
| `Harness/Differential.lean` | skipped: the F* tree answers DESCRIBE with the empty graph |

The envelope kind is `describe`, not `construct`, so that a client can tell
the two forms apart. The member that carries the graph is `nquads` in both.

## 6. Open

- The F* tree answers DESCRIBE with the empty graph
  (`SPARQL11.Algebra.fst`, `QF_Describe`). The two trees disagree until the
  F* side follows; the differential harness skips DESCRIBE for that reason.
  Tracked at <https://github.com/danbri/factoidal/issues/698>.
- Entailment regimes: `Harness/Run.lean` evaluates DESCRIBE over the
  closure-augmented dataset, as for the other forms. No test exercises it.
