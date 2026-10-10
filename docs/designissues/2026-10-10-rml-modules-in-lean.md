# RML in Lean: the five KG-Construct modules

Date: 2026-10-10. Runner: `lake exe l4rml` (`formal/lean4/Harness/RmlRun.lean`).
Test corpus: `third_party/testing/rml-modules/<module>/test-cases`, with the
specification text under `third_party/testing/rml-modules/<module>/spec/section`.

## Scores at this date

| Module | Pass | Fail | Not scored | Total |
|---|---|---|---|---|
| rml-core | 75 | 0 | 1 fixture defect | 76 |
| rml-io | 61 | 0 | 11 fixture defect, 1 database source | 73 |
| rml-cc | 35 | 0 | 0 | 35 |
| rml-star | 10 | 0 | 8 fixture defect | 18 |
| rml-fnml | 20 | 0 | 0 | 20 |

A fixture defect is a case whose own files cannot be satisfied by any
processor (see "Fixture defects" below). The runner prints one score line per
module and exits 1 when any case fails.

## Layers

A mapping is RDF. Five layers read it and run it; each layer is a total
function of its inputs.

| Layer | Module | Input to output |
|---|---|---|
| Model | `RML/Model.lean`, `RML/Mapping.lean` | the mapping as a value (triples maps, term maps, gather maps, star maps, function executions) |
| Reader | `RML/FromGraph.lean` | mapping graph to model |
| Validation | `RML/Validate.lean` | mapping graph to the list of MUST clauses it breaks, without reading any source |
| Sources | `RML/Open.lean`, `RML/Record.lean`, `RML/Encoding.lean`, `RML/Compression.lean` | bytes of a file to the list of logical iterations (records) |
| Evaluation | `RML/Eval.lean`, `RML/Functions.lean`, `RML/Star.lean` | model and records to quads |
| Targets | `RML/Targets.lean` | quads to the files of the logical targets, and back |
| Entry | `RML/Run.lean` | validate, read, evaluate; a rejected run has no quads |

The library never reads a file. `FileAccess` is the one seam: a root and a path
to bytes. The runner supplies the files of the case directory.

## Errors

`RmlError` has four kinds. `mapping` (found by validation), `source` (a file
that cannot be read or is not a document of its format), `data` (a value from
which no valid RDF term can be built), `unsupported` (the mapping needs
something this port does not have; the case is not scored and its bucket is
printed). A negative case (`error=true` in the corpus metadata) passes when the
run is rejected by any of the first three kinds.

## Sources and codecs

CSV, JSONPath and XPath files; SPARQL `SELECT` over an RDF file
(`formats:SPARQL_Results_CSV`: one iteration per solution, one column per
variable, each value the lexical form the CSV results format writes). The
SPARQL engine reaches `RML/Open.lean` through `FileAccess.sparql`, supplied by
`RML/SparqlSource.lean`; `Open.lean` does not import the SPARQL parser, because
that import puts `SPARQL.xsdInteger` (a string) into the import closure of
`SPARQL/StoreBackend.lean` and its dependents, where it shadows `RDF.xsdInteger`
(an IRI) wherever `RDF` is open. Without an engine such a source is `unsupported`.
Encodings UTF-8 and UTF-16. Compression gzip, zip, tar.gz and tar.xz, read
and written: `Codec/Inflate.lean`, `Codec/Archive.lean`, `Codec/Lzma.lean`
(LZMA and LZMA2), `Codec/Xz.lean` (the xz container with the checks none,
CRC32, CRC64 and SHA-256). The xz writer emits uncompressed LZMA2 chunks; its
output passes `xz -t` and `tar -xJ`. The xz reader is checked against streams
written by liblzma (`Codec/XzTests.lean`). A database source needs a relational
database and stays `unsupported`.

A reference to a CSV column that the header does not name is a data error
(RML-FNML, Definitions, Input: references must be references to records that
exist in the logical source). A NULL value (`rml:null`) leaves the column
without a cell, so a reference to it selects nothing and is not an error.

## RML-star

A quoted triple becomes the reifier of an RDF 1.2 triple term: a blank node `r`
with `r rdf:reifies <<( s p o )>>`. A quoted triple in subject or object
position is `r`. The label of `r` is a function of the triple term
(`RML/Star.lean`), so one quoted triple has one reifier. A star map takes the
triples its quoted triples map generates for the same iteration, or for the
parent iterations that the join conditions select. An
`rml:NonAssertedTriplesMap` emits no triples of its own.

RDF 1.2 Turtle gives each `<< s p o >>` a new reifier, so the expected files
(legacy `<< >>` syntax in `.nt` files) are read as Turtle in RDF 1.2 mode and
the reifiers of the same triple term are merged in both datasets before the
comparison (`mergeReifiers`).

## RML-FNML

`RML/Functions.lean` is a registry keyed by function IRI. An entry holds the
FnO description (parameters with `fno:required`, returns in order) and the
implementation. Validation rejects a function the registry lacks, a parameter
or a return the function does not have, and a required parameter without an
input. The runner compares the registry with the FnO file of the corpus
(`functions.ttl`): 8 functions described, 8 implemented with the same
parameters and returns.

An input value map is read as a source value, not as a term: a template input
is the text it expands to. Multi-valued inputs combine as a cartesian product.
A NULL result generates no term. The empty string generates a term. A
function-valued map has the term type literal unless the map or its position
says otherwise. `rml:condition` generates the terms of its map when the
condition function returns `true`.

## Decisions

Each decision is an interpretation made by the implementer, not a ruling by the
owner.

1. `rml:UnsafeIRI` keeps the weak IRI test (a scheme and nothing else), because
   the specification's own example contains a space.
2. A graph map may state `rml:termType rml:BlankNode`: the graph map example
   does, the term map list does not.
3. For rml-cc the base IRI is `http://example.com/base/`. It is inferred from
   the expected outputs; the corpus metadata does not state it.
4. A resource with `rml:logicalSource`, `rml:subjectMap`, `rml:subject` or
   `rml:predicateObjectMap` is a triples map without an `rdf:type` (the FNML
   cases are untyped).
5. A triples map is `rml:AssertedTriplesMap` or `rml:NonAssertedTriplesMap`, not
   both (`shapes/star.ttl` of rml-star).

## Fixture defects

A case is a fixture defect when its files contradict each other or the
specification. The runner decides in three ways, each with evidence.

| Rule | Cases | Evidence |
|---|---|---|
| The expected output cannot be read | rml-core `RMLTC0027b` | `output.nq` has a space in an IRI |
| The metadata says `error=true` and the case ships an output | rml-io `RMLSTC0009a` | the two statements cannot both hold |
| The case passes after the test generator's label line `**Input N**` is removed from a CSV file | rml-star `RMLSTARTC001b` to `008b` | the first line of each `data2.csv` is the label |
| The case is on `datatypeDefects` in the runner | rml-io `RMLTTC0004a`, `0004c`, `0004f`, `0004g`, `0005b`, `0006b`, `0006c`, `0006d`, `0006e`, `RMLSTC0003` | the datasets differ only in literal datatypes, and the source or the sibling dumps show which side is wrong |

A datatype-only mismatch of a case that is not on the list is a failure, and so
is a listed case that passes. A rule that classified every datatype-only
mismatch as a fixture defect would hide a library that drops the datatype of
every JSON number.

## Shortfalls

A shortfall needs a failing test and an open issue (CLAUDE.md, 2026-09-07). The
issues are not yet filed; the coordinator files them and replaces the markers.

| Shortfall | Test that fails when fixed | Issue |
|---|---|---|
| Database source (`rml:SQL2008Table`, D2RQ database): `RMLSTC0006a` | the case is in the bucket `database source` of the `rml-io` score line | NOT YET FILED |
| Case mapping is ASCII only: Lean `String.toUpper`, shared with SPARQL `UCASE` and XPath `fn:upper-case` | `FunctionTests`/`Functions.lean` guard on `grel:toUpperCase` of `é` | NOT YET FILED |
| `grel:escape` mode `html` escapes `& < > "` and writes no named entity for a non-ASCII character | `Functions.lean` guard on `grelEscape "é" "html"` | NOT YET FILED |
