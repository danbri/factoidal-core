#!/usr/bin/env python3
"""Scaling assertions for the Lean command line (l4factoidal).

For each row below the script generates an input of size x and one of size
4x, runs the Lean command on both (the minimum wall time of RUNS runs each),
and checks

    time(4x)  <=  BOUND * max(time(x), FLOOR)

with BOUND = 9.0 and FLOOR = 0.05 s. A linear or n log n command gives a
ratio of about 4 to 6; a quadratic command gives about 16. The floor keeps the
fixed cost of starting the process from turning timer noise into a failure.
This is the n, 2n, 4n assertion of skills/danbri-function-precrime-checkers,
for the paths that the survey of 2026-10-10 found quadratic and that were
repaired (docs/designissues/2026-10-10-lean-vs-fstar-performance.md):

  rdfs-closure-*   RDFS closure of a wide, a dense and a tree-shaped schema
  owlrl-closure-chain  OWL RL closure of a chain of subclass axioms. The closure
                   of n axioms has n(n-1)/2 triples, so 4x input is 16x output
                   and the row uses the bound 20.0 (ROW_BOUND)
  trig-parse       TriG parse, many small graph blocks
  trig-big-graph   TriG parse, one graph block with all the triples
  turtle-serialize Turtle pretty-printer over slices of a real life-sciences file
  turtle-object-list  Turtle parse of one statement whose object list has n
                   objects (`ex:s ex:p 0, 1, ... .`), 25,000 against 100,000
                   (https://github.com/danbri/factoidal/issues/754; the object
                   list was built with `acc ++ ...`: 10.33 s at 25,000 and no
                   result in 120 s at 100,000 before the repair, 0.058 s and
                   0.403 s after, measured 2026-10-12)
  rdfc-iri         RDFC-1.0 canonicalisation of a graph with no blank nodes
  rdfc-person      RDFC-1.0 canonicalisation of a graph with one blank node per person
  rdfc-bnode-unique  RDFC-1.0 canonicalisation of n persons, each a blank node with an
                   rdf:type, a name and an age (3n quads, every first-degree hash
                   unique): the input of the npm speed gate's canonicalize row
                   (https://github.com/danbri/factoidal/issues/745; 0.54 s to 9.49 s
                   for 4x input before the blank node to quads map, 0.18 s to 1.19 s
                   after)
  rdfc-bnode-collide  RDFC-1.0 canonicalisation of n blank nodes that share one
                   first-degree hash, so Hash N-Degree Quads runs for each
                   (https://github.com/danbri/factoidal/issues/751; 0.16 s to
                   2.66 s CPU for 4x input before the blank node to quads map
                   reached Hash N-Degree Quads and the issuer got a search tree,
                   0.07 s to 0.36 s after, measured 2026-10-13)
  group-by-few     SPARQL GROUP BY with 6 groups over many rows
  group-by-many    SPARQL GROUP BY with one group per subject
  count-distinct   SPARQL COUNT(DISTINCT ?s): the aggregate's DISTINCT
                   (https://github.com/danbri/factoidal/issues/722; 1.4 s to
                   22.8 s for 4x input before the repair, 0.12 s to 0.65 s after)
  count-distinct-star  SPARQL COUNT(DISTINCT *): DISTINCT rows inside an
                   aggregate (issue 722; 0.43 s to 11.7 s before, 0.11 s to 0.60 s after)
  query-vs-parse   `query` COUNT(*) against `parse` of the same 5,000 paragraphs of
                   gene.ttl: at most 2.0 times the CPU time and the peak memory
                   (https://github.com/danbri/factoidal/issues/724; 5.7 and 3.7
                   times before the command line stopped re-parsing N-Quads
                   text, 1.6 and 1.0 after)
  pack-trig-memory peak resident memory of `l4block-shard-pack` over TriG per source byte,
                   from 4 MB to 16 MB: at most 20 bytes
                   (https://github.com/danbri/factoidal/issues/769; 70.7 on the
                   whole-source route, 11.9 on the chunk route)
  rdfxml-write, jsonld-write
                   `l4source-convert` (the library serialisers) writes a dataset of
                   2,000, then 8,000 subjects (`tests/sbm11/syntax/gen_multi.py`, 8
                   triples for each subject) as RDF/XML or as JSON-LD. Expected
                   failures: https://github.com/danbri/factoidal/issues/845 (the
                   RDF/XML writer scans the graph for each subject) and
                   https://github.com/danbri/factoidal/issues/712 (the JSON-LD
                   `fromRdf` node list). Measured 2026-10-14, total wall time of the
                   command: RDF/XML 1.1 s and 12.8 s, JSON-LD 0.75 s and 17.1 s (the
                   Turtle writer: 0.45 s and 1.5 s)
  sbm11-pack-ttl-memory, sbm11-pack-trig-memory
                   peak resident memory of `l4sbm11-pack` per source byte over Turtle
                   and TriG, measured at x, 2x and 4x (25,000, 50,000 and 100,000
                   statements of about 400 source bytes each, 10 MB to 40 MB): the
                   slope from x to 4x is at most 0.75 byte per source byte
                   (https://github.com/danbri/factoidal/issues/837; measured
                   2026-10-14: -0.13 to 0.28 for Turtle and -0.14 to 0.21 for TriG, because
                   the packer spills its runs to disk at 20,000 terms and the readers
                   keep no source text). A reader that keeps the source (1 byte per
                   byte for the text alone, 24 for a character list) fails the row.
  sbm11-pack-rdfxml-memory, sbm11-pack-jsonld-memory
                   the same slope over RDF/XML and JSON-LD at 5,000, 10,000 and
                   20,000 statements (2 MB to 8 MB). Expected failures:
                   https://github.com/danbri/factoidal/issues/838 and
                   https://github.com/danbri/factoidal/issues/839. Both readers
                   take the whole document before they parse it
                   (`Source.Reader.whole`): measured 2026-10-14 in three runs, 11.3 to
                   14.5 bytes of peak RSS per source byte for both syntaxes.
  sbm11-export-nq-memory, sbm11-export-ttl-memory, sbm11-export-trig-memory
                   peak resident memory of `l4sbm11 export` per byte of output, measured
                   at x, 2x and 4x (25,000, 50,000 and 100,000 statements of about 400
                   source bytes each, 11 MB to 44 MB of N-Quads, Turtle or TriG output;
                   the TriG source has 100 graph names, which the SPO order interleaves):
                   the slope from x to 4x is at most 0.75 byte per output byte. The
                   serialiser layer (`L4Factoidal/RDF/Sink.lean`) writes N-Quads one line
                   for each quad, Turtle and TriG one statement for each subject, so the
                   export holds one block of the generation, the dictionary page cache
                   and a 64 KiB output buffer (https://github.com/danbri/factoidal/issues/837
                   item 6). A writer that keeps the quads (1 to 3 bytes per output byte) fails.
  sbm11-export-rdfxml-memory, sbm11-export-jsonld-memory
                   the same slope for RDF/XML and JSON-LD at 2,000, 4,000 and 8,000 statements
                   (0.9 MB to 3.6 MB). Expected failures:
                   https://github.com/danbri/factoidal/issues/846 and
                   https://github.com/danbri/factoidal/issues/847. Both library writers take
                   the whole graph or dataset (`graphToRdfXml`, `fromRdf`), so
                   `Sink.Writer.whole` keeps the quads until the end.
  sbm11-dump-time, sbm11-export-nq-time
                   CPU time of `l4sbm11 dump` and of `l4sbm11 export --format nquads`
                   (both with `--verify merkle`, the default for a generation that no
                   CURRENT pointer names) over generations of 100,000, 200,000 and
                   400,000 statements (the source of `sbm11_ttl`: 370 characters of
                   literal for each statement, so the generation is 38 MB, 76 MB and
                   152 MB): time(4x) at most SBM11_READ_TIME_BOUND (5.25) times time(x).
                   A pass over one permutation is linear in the statements, which gives
                   4.0. The bound lies between 4.5 (the highest ratio in three runs of each
                   row after the repair, the second and third with a load average of 3)
                   and 6.0 (the lowest ratio before it).
                   Issue https://github.com/danbri/factoidal/issues/854: the Merkle proof
                   of each chunk of the dictionary was computed from all the leaves of the
                   file (`proofWith?`), so a pass over the dictionary hashed n * (n - 1)
                   tree nodes for n chunks. Measured 2026-10-14 (CPU time at 100,000,
                   200,000 and 400,000 statements), before the repair (expected failures):
                   dump 6.2 s, 13.3 s and 37.0 s (6.0 for 4x input); export 5.5 s,
                   13.0 s and 37.0 s (6.7); after the proof table (`BlockMerkle.Tree`)
                   and the byte copy in `concat`: dump 3.5 s, 6.9 s and 13.7 s (3.9);
                   export 3.1 s, 5.8 s and 12.0 s (3.9); a second run with a load
                   average of 3: dump 4.1 s, 6.9 s and 13.5 s (3.3); export 2.8 s,
                   6.3 s and 12.3 s (4.5); a third: dump 4.1 s, 7.3 s and 15.2 s (3.7);
                   export 3.5 s, 6.8 s and 11.9 s (3.4). With `--verify none` (no proof; unchanged by
                   the repair) dump takes 3.2 s and 11.5 s to 13.1 s at 100,000 and
                   400,000 statements.
  sbm11-dump-memory
                   peak resident memory of `l4sbm11 dump --verify merkle` over the same
                   generations (100,000, 200,000 and 400,000 statements): the slope from x to
                   4x is at most 0.75 byte per output byte, as for the export rows. The peak is
                   the VmHWM that the command prints. Issue
                   https://github.com/danbri/factoidal/issues/859: `dump` kept every
                   dictionary chunk and every chunk of the permutation that it had verified.
                   Measured 2026-10-14 (peak RSS at 100,000, 200,000 and 400,000 statements),
                   before the repair (expected failure): 184, 238 and 390 MB (1.66 bytes per
                   output byte, 719 per statement); after: 60 to 62 MB at 100,000 and 200,000
                   statements and 64 MB or 78 MB at 400,000 (0.02 to 0.13 bytes per output
                   byte, 9 to 54 per statement).
  merkle-range-read-time
                   user CPU time (minimum of 5 runs) of one call of
                   `PosixRangeIO.readVerifiedRange?`, through `l4merkle-range-read read
                   --reader leaves`, over a whole file of 512, 1,024 and 2,048 chunks of
                   65,536 bytes (32 MB to 128 MB; `l4merkle-range-read make` writes the
                   file, its sidecar and its root): time(4x) at most SBM11_READ_TIME_BOUND
                   (5.25) times time(x). Issue https://github.com/danbri/factoidal/issues/859:
                   the reader computed the Merkle proof of each chunk from all the leaves, so
                   it took `c * (n - 1)` node hashes to read `c` chunks of a file of `n`.
                   Measured 2026-10-14, before the repair (expected failure): 0.332 s, 1.229 s
                   and 4.011 s (12.1 for 4x chunks); after (`BlockMerkle.Tree`, built once for
                   the file): 0.153 s, 0.320 s and 0.630 s (4.1; seven runs gave 3.5 to 4.7).
                   The row bounds the user time and prints the system time (page faults of the
                   reader's buffers: 0.02 s to 0.4 s here, 0.2 s to 1.9 s for 64 MB in other
                   runs). Before it measures, the row reads the smallest file with `--check`
                   and with one changed byte, which the reader must refuse. A first version of
                   the row packed a shard with `l4block-shard-pack` and read it with
                   `l4block-shard-merkle-pread`: the packer cuts blocks at 2 MiB, so a shard
                   has at most about 64 chunks for each artifact, and a statement with a
                   literal of 8 MB to 32 MB (128 to 512 chunks) gave 0.070 s, 0.149 s and
                   0.342 s, 4.9 for 4x chunks, under the bound on the unrepaired reader. In
                   user time the quadratic term was 0.8 microsecond for each pair of chunks
                   and the linear work about 0.35 ms for each chunk (fit to 512 and 2,048
                   chunks), so the term is the larger one from about 450 chunks.
  sbm11-update-memory
                   peak resident memory of one `l4sbm11 update` per byte of the log it writes,
                   measured at x, 2x and 4x solutions (12,500, 25,000 and 50,000 statements of
                   the form `ex:s<i> ex:p "v<i>"`, each request
                   `DELETE { ?s ex:p ?o } INSERT { ?s ex:q ?o } WHERE { ?s ex:p ?o }`, so 2n
                   entries and 3 MB, 6 MB and 12 MB of log): the slope from x to 4x is at most
                   SBM11_UPDATE_MEMORY_BOUND bytes of peak RSS per log byte. Issue
                   https://github.com/danbri/factoidal/issues/857: `appendPlan?` encoded the batch
                   as a `List UInt8` (a list cell for each byte, three or more copies of it), so
                   the peak grew 64 bytes for each byte of log: 2,310,880 kB for the 35,919,852
                   bytes of the 101,632-solution update of the olympics generation.
  sbm11-open-log-memory
                   peak resident memory of opening a generation that has a delta log
                   (`l4sbm11 query GEN 'ASK { ?s ?p ?o }'` replays the whole log), per byte of the
                   log: logs of 25,000, 50,000 and 100,000 entries (3 MB, 6 MB and 12 MB; a
                   remove and an add for each of the first n/2 statements of a generation of
                   200,000 statements, `tests/sbm11/gen_dlog.py`), the slope from x to 4x is at
                   most SBM11_OPEN_MEMORY_BOUND bytes per log byte. Issue
                   https://github.com/danbri/factoidal/issues/851: the reader parsed the log as a
                   `List UInt8`, and the replay holds every entry as a Lean object.
  sbm11-replay-time
                   CPU time of the same open: the replay maps the terms of the log to ids, and
                   the cost for each entry (the slope from x to 4x) is at most
                   SBM11_REPLAY_US_BOUND microseconds, and time(4x) at most
                   SBM11_READ_TIME_BOUND times time(x). Issue
                   https://github.com/danbri/factoidal/issues/858: the replay looked every term of
                   every entry up in the dictionary (about 28 positioned reads for each lookup,
                   each read an open, fstat, pread and close of the file): 258 to 295 microseconds
                   for each entry on this fixture, 283 on the olympics generation (203,264
                   entries: 57.9 s). Since 2026-10-14 the replay looks the distinct terms of the
                   log up in dictionary order with a finger (`Dict.lookupWalkM`).
  sbm11-pack-nt-vs-nq  `l4sbm11-pack` over 100,000 N-Triples statements takes at most
                   2.0 times the CPU time of the same pack over the same triples as
                   N-Quads text (one graph name on every line). N-Triples was read
                   as RDF 1.2 with a fuel of `r5.length + 1` per statement, the
                   length of the rest of the chunk (`readTriple12`): phase 1 took
                   2,996 ms for 8.3 MB against 477 ms for the same quads as
                   N-Quads (4 workers, 2026-10-14), 272 ms after `lineFuel`
  sbm11-pack-ttl-workers, sbm11-pack-trig-workers
                   `l4sbm11-pack --workers 4` reads a Turtle or a TriG source with more
                   than one worker (the pack prints `workers=K`). Expected failures:
                   https://github.com/danbri/factoidal/issues/842. N-Triples and N-Quads are cut into byte
                   ranges at line starts; Turtle and TriG are read by one worker, so
                   phase 1 of the pack takes 2.8 to 3.2 times as long per quad (Turtle)
                   and 3.6 to 6.6 times (TriG) as the same quads as N-Quads text, and
                   8.0 to 9.2 times as long per source byte (880,000 quads, 4 workers
                   requested, 4 CPUs, 2026-10-14)
  query-memory     peak resident memory of `query` COUNT(*) per input byte, from
                   x to 4x paragraphs of gene.ttl: at most 32 bytes
                   (https://github.com/danbri/factoidal/issues/729; 36.6 before
                   the Turtle reader stopped building the whole document as a
                   character list, 27 after)
  query-memory-fstar  the same slope against 3 times the F* engine's (2.0 bytes
                   per input byte on the same files): at most 6 bytes. Expected
                   failure naming issue 729 until the index and the solution
                   sequence stop growing with the data
  select-star      `query` SELECT * over 1,250 and 5,000 paragraphs of gene.ttl:
                   every row is printed. The command line parses the JSON
                   envelope the op returns, and `JSON.parseItems` appended
                   each item with `acc ++ [v]`
                   (https://github.com/danbri/factoidal/issues/729; 0.32 s to
                   6.24 s for 4x input before the reverse-accumulator parser,
                   0.24 s to 0.61 s after, measured 2026-10-12; F*: 1.43 s at
                   5,000)
  sparql-collection-parse  `query` SELECT over one collection of 2,000 and
                   8,000 members (one triple of data, no answer). An expected
                   failure until 2026-10-13 (issue 818 item 2: `freshBnodeId`
                   walked the remaining token list once per cell; issue 802:
                   the tokenizer was quadratic): 0.086 s and 1.230 s before
                   both repairs
  sparql-tokenize  `query` ASK over one triple with a VALUES block of 2,000,
                   4,000 and 8,000 IRIs, measured at x, 2x and 4x like
                   owl-consistent-cl (each doubling at most DOUBLING, 4x at most
                   BOUND): the SPARQL tokenizer reads every token of the
                   request. Before the repair of
                   https://github.com/danbri/factoidal/issues/802 it took the
                   length of the rest of the input three times per token
                   (`tokenizeLoop`'s progress test and `skipWs`'s fuel):
                   0.52 s, 1.92 s, 6.97 s; after, 0.017 s, 0.032 s, 0.040 s
                   (2026-10-13)
  sparql-collection-scope  the same query over 10,000 and 40,000 members, past
                   the constant fuel 10,000 (a parse error before the repair
                   of https://github.com/danbri/factoidal/issues/818). An
                   expected failure until 2026-10-13
                   (https://github.com/danbri/factoidal/issues/824): the blank
                   node scope check (`validateBnodeScope`, §19.6) walked the
                   join chain of the collection once per join (0.44 s and
                   9.05 s); after `validateBnodeScope_eq_fast` (one pass, a
                   work list) 0.061 s and 0.164 s
  sparql-update-insert  `update` INSERT DATA of 2,000 and 8,000 triples into an
                   empty dataset (issue 802: DELETE DATA of 4,000 quads took
                   61.8 s in the SBM11 store). 5.11 s and 89.4 s before the
                   tokenizer repair, 0.18 s and 2.01 s after. An expected
                   failure until 2026-10-13
                   (https://github.com/danbri/factoidal/issues/821): the parser
                   appended each triple to the end of the block's BGP list, and
                   `Dataset.insertQuads` scanned and copied the graph for each
                   quad. After the triples accumulator (`pTriplesBlock_eq_ref`)
                   and the graph index (`insertQuads_eq_fast`): 0.032 s and
                   0.105 s
  sparql-update-insert-bnodes  the same with a blank-node subject in each
                   triple, 4,000 and 16,000 triples: the INSERT DATA blank node
                   label checks (§19.6) scanned a list of labels per label
                   (0.17 s and 2.00 s, 2026-10-13); after
                   `bnodesInBgp_eq_fast` and `bnodeLabelsUnique_eq_fast` (a set
                   of labels) 0.049 s and 0.257 s
  shacl-person     SHACL Core validation (l4shacl, a one-entry manifest) of n
                   ex:Person nodes against 4 property shapes
                   (https://github.com/danbri/factoidal/issues/723; 0.31 s to
                   3.82 s for 4x input before the data index, 0.043 s to 0.139 s after)
  termwire-page-decode  decode of one PTD2 page of n IRI terms (term codec v2,
                   the IBK5 dictionary page), 100 times, through
                   `l4termwire-page-decode`. Bound 6.0 (ROW_BOUND). Before the
                   repair of https://github.com/danbri/factoidal/issues/783
                   `TermWireV2.parseInline` took `List.length` of the rest of the
                   page for each term: 1,000 to 4,000 terms, 5 decodes, went from
                   0.20 s to 5.30 s (ratio 26); after, 0.015 s to 0.049 s
  owl-consistent-cl  `owl-consistent` (OWL 2 RL closure, then the tableau
                   refuter) on the first 10,000, 20,000 and 40,000 lines of the
                   Cell Ontology as sorted N-Triples (the reproduction of
                   https://github.com/danbri/factoidal/issues/760). Measured at
                   x, 2x and 4x in CPU time: each doubling at most DOUBLING
                   (3.0) times the time before it, and 4x at most BOUND. Before
                   the repair: 19.3 s, 105 s and not finished at 600 s (the
                   class-size counting rung built its linear system by scanning
                   the graph once per IRI); after: 1.05 s, 2.74 s, 7.48 s,
                   measured 2026-10-12, most of it the OWL 2 RL closure
  owl-species      the OWL 2 species check (`l4owl-species`,
                   `OWL.SyntaxDL.speciesViolations`) of a generated OWL 2 DL
                   document of n units: a class with a restriction on a blank
                   node, a union over an RDF list, an individual typed with the
                   class, a language-tagged label, a data value and an object
                   property assertion to a blank node (an anonymous individual
                   with one named link). 2,000 against 8,000 units
                   (https://github.com/danbri/factoidal/issues/766: the check
                   counted the named links of each blank node with a scan of
                   the graph, and read each (subject, predicate) pair with a
                   scan; QUDT 3.4.0 took 253 s of CPU time before the indexes,
                   2.3 s after)
  owl-species-bnode-edges  the same check over n pairs of blank nodes linked by
                   an object property assertion (`_:x p _:y`), each pair with
                   one named link: the anonymous-individual graph has n
                   components. 8,000 against 32,000 pairs. An expected
                   failure until 2026-10-13 (https://github.com/danbri/factoidal/issues/812):
                   `componentsOf` looked for the component of each end with a
                   scan of all components (1.09 s at 8,000 pairs, 14.79 s at
                   32,000); after `componentsOf_eq_fast`, which skips the scans
                   for vertices in no component, 0.34 s and 1.57 s
  owl-species-bnode-chain  the same check over one chain of n blank nodes
                   (`_:x0 p _:x1 . _:x1 p _:x2 ...`), 8,000 against 32,000:
                   each edge touches a vertex that is already in a component.
                   0.49 s and 9.18 s before issue 812; after, the first
                   component is extended without a scan (`addEdge_head_left`,
                   the components are disjoint): 0.22 s and 0.81 s
  delta-log-merge  `l4wasm-cli call deltaLogMerge` (the merge on read of the
                   browser update log, hub post 18) of a log of n records, each
                   an INSERT DATA of one distinct triple, over an empty base:
                   8,000, 16,000 and 32,000 records, the n, 2n, 4n assertion of
                   owl-consistent-cl. The engine writes the log
                   (`l4wasm-cli callseq` of `deltaLogEncode`), and
                   `deltaLogDecode` must find every batch, before the row is
                   timed. An expected failure until 2026-10-13
                   (https://github.com/danbri/factoidal/issues/822): each add
                   went through `Graph.add`, a membership scan and an append on
                   a list (1.33 s at 8,000 records, 4.53 s at 16,000, 17.23 s
                   at 32,000 CPU); after `applyBatches_eq_fast` (a hash set of
                   each graph carried through the batches) 0.36 s, 0.81 s and
                   1.80 s
  turtle-prefixes  `l4wasm-cli call serializeTurtleWith` with a table of n prefixes, every one
                   used (one triple for each: the subject lies under namespace i, the
                   object under namespace i + 1), n = 8,000, 16,000 and 32,000, measured at
                   x, 2x and 4x like owl-consistent-cl, on the user CPU time (the run holds
                   up to 550 MB; see SERIES_ROWS). Issue
                   https://github.com/danbri/factoidal/issues/864: `tsUserUsed` kept a list
                   of the namespaces it had seen and scanned the IRIs of the graph for each
                   prefix, `tsFindPrefix` scanned the table for each IRI, and a filter of
                   `turtleOfGraphOpts` compared each namespace of the graph with each row
                   covered. Before the repair (expected failure): 2.36 s, 12.1 s and 56.7 s
                   (ratios 5.1 and 4.7 for the two doublings); after: 0.24 s, 0.49 s and
                   1.0 s (2.1 and 2.0).
  turtle-prefixes-open
                   `l4wasm-cli callseq` of one `datasetOpen` of a Turtle document with n
                   `@prefix` lines (and n triples with full IRIs), n = 16,000, 32,000 and
                   64,000, on the user CPU time. Issue 864: `declarationOrderPrefixes` kept a
                   list of the labels it had seen (the parser alone, `l4factoidal parse`,
                   takes 0.36 s and 0.80 s at 16,000 and 32,000). Before the repair
                   (expected failure): 1.24 s, 7.15 s and 33.0 s (ratios 5.8 and 4.6);
                   after: 0.43 s, 0.87 s and 1.76 s (2.0 and 2.0).
  turtle-nest-time `l4source-convert --nest-check n`: one triple whose object is a triple term
                   nested n levels deep, written as Turtle by the batch writer and by the
                   stream writer, n = 25,000, 50,000 and 100,000. Issue 864: `tsTermToTurtle`
                   built the text of each level from the text of the level below it, so it
                   copied the text built so far at each level. Before the repair (expected
                   failure): 0.50 s, 1.76 s and 10.2 s CPU (ratios 3.5 and 5.8; about 121 s
                   at 300,000); after: 0.061 s, 0.116 s and 0.241 s (1.9 and 2.1; 0.8 s at
                   300,000).
  turtle-read-prefixes
                   `l4factoidal parse` of a Turtle document with n `@prefix` lines and n triples
                   whose three terms are prefixed names (the subject and the predicate under
                   prefix i, the object under prefix i + 1; 7 MB at n = 64,000), n = 16,000,
                   32,000 and 64,000, measured at x, 2x and 4x like owl-consistent-cl. The
                   command must print n, the number of triples. Issue
                   https://github.com/danbri/factoidal/issues/865: the reader kept the
                   prefixes in a list and looked each name up with `List.find?`, a scan of
                   the prefixes declared after it. Before the repair (expected failure): 2.59 s,
                   16.4 s and 78.8 s CPU (ratios 6.3 and 4.8 for the two doublings; 30.4 for 4x
                   input).
  sbm11-export-prefixes-time
                   `l4sbm11 export --format turtle --verify none` of a generation of n statements
                   (the subject of statement i under namespace i, the object under namespace
                   i + 1) with a table of n prefixes, every one used, from n `--prefix LABEL=IRI`
                   arguments: n = 4,000, 8,000 and 16,000 (16,000 prefixes are 740 KB of
                   arguments, and ARG_MAX is 2 MB), the rule of turtle-read-prefixes. The
                   Turtle must declare n prefixes. Issue 865: `Sink.bodyPush` scanned the
                   table for the prefix of each IRI, and `parseOpts` appended each prefix to
                   the end of the list of the others. Before the repair (expected failure):
                   0.252 s, 0.828 s and 3.41 s CPU (ratios 3.3 and 4.1; 13.5 for 4x input).
  startup          process start: `l4factoidal version` must take at most
                   STARTUP_BUDGET (20 ms) of CPU time, minimum of 15 runs
                   (305 million instructions and 43 ms before the fixtures were
                   moved out of the executable's modules; 25 million and 7 ms
                   after)

Expected failures (CLAUDE.md, "A stated shortfall is a failing test plus an
open issue"; skills/test-suites/SKILL.md, "Expected failures"): a row listed in
XFAIL is a cost that is known and not yet repaired. It still runs. When it
fails the bound it prints "XFAIL" with its issue URL and counts as
expected-fail, not as a pass; when it PASSES it prints "UNEXPECTED PASS" and
counts as a failure, so the run is red until the row is removed from XFAIL
(the repair turns the row into a real assertion) and the issue is closed.
A row of the table ROWS or of the SBM11 packer (sbm11-pack-*) that cannot
measure (the command exits with an error or times out, the binary is missing,
the pack's summary line is missing) prints "FAIL ... cannot measure" and counts
as a failure, also when the row is in XFAIL: an expected failure must fail the
bound, not the measurement.

The script measures; it does not compare with the F* engine. Exit status 0
when every pair passes or fails as expected, 1 when a pair fails or an
expected failure passes, 2 when the binary is missing. Scores print as
"N pass, M fail, K expected-fail (out of T)".

Usage:  tests/stack/lean_scaling.py [--runs N] [--only ROW[,ROW...]]
Env:    L4_BIN     path of l4factoidal (default formal/lean4/.lake/build/bin/l4factoidal)
        L4_SHACL_BIN   path of l4shacl (default: beside L4_BIN)
        L4_TERMWIRE_BIN  path of l4termwire-page-decode (default: beside L4_BIN)
        L4_SPECIES_BIN   path of l4owl-species (default: beside L4_BIN)
        L4_WASMCLI_BIN   path of l4wasm-cli (default: beside L4_BIN)
        L4_SBM11_PACK_BIN  path of l4sbm11-pack (default: beside L4_BIN)
        L4_SOURCE_CONVERT_BIN  path of l4source-convert (default: beside L4_BIN)
        L4_SBM11_BIN  path of l4sbm11, for the export rows (default: beside L4_BIN)
        L4_SCALING_FIXTURES  fixture directory (default: $STACK_FIXTURES/lean-scaling
                   when STACK_FIXTURES is set, else /tmp/factoidal-lean-scaling)
        L4_SCALING_CAP   seconds per run before it counts as a failure (default 120)
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import bench_closure as bc  # noqa: E402  (closure shape generators)
import bench_lean_vs_fstar as bl  # noqa: E402  (real-data slices)

BOUND = 9.0
FLOOR = 0.05
BIN = Path(os.environ.get("L4_BIN", ROOT / "formal/lean4/.lake/build/bin/l4factoidal"))
SHACL_BIN = Path(os.environ.get("L4_SHACL_BIN", BIN.parent / "l4shacl"))
TERMWIRE_BIN = Path(os.environ.get("L4_TERMWIRE_BIN", BIN.parent / "l4termwire-page-decode"))
SPECIES_BIN = Path(os.environ.get("L4_SPECIES_BIN", BIN.parent / "l4owl-species"))
WASMCLI_BIN = Path(os.environ.get("L4_WASMCLI_BIN", BIN.parent / "l4wasm-cli"))
SOURCE_CONVERT_BIN = Path(os.environ.get("L4_SOURCE_CONVERT_BIN", BIN.parent / "l4source-convert"))
SBM11_BIN = Path(os.environ.get("L4_SBM11_BIN", BIN.parent / "l4sbm11"))
CAP = float(os.environ.get("L4_SCALING_CAP", "120"))
# A fixture directory of one's own (hazard #43 of
# skills/workflow-gotchas-debugging: runs that share a directory delete each
# other's files): L4_SCALING_FIXTURES, else a directory under STACK_FIXTURES.
FIX = Path(os.environ.get("L4_SCALING_FIXTURES")
           or (os.environ["STACK_FIXTURES"] + "/lean-scaling" if os.environ.get("STACK_FIXTURES")
               else "/tmp/factoidal-lean-scaling"))
EX = "http://example.org/"
# Rows whose OUTPUT grows faster than their input use a larger bound.
ROW_BOUND = {"owlrl-closure-chain": 20.0, "termwire-page-decode": 6.0}
# Rows that fail today, each with the open issue that tracks the cost. A row
# leaves this table in the commit that repairs it.
XFAIL: dict[str, str] = {
    "query-memory-fstar": "https://github.com/danbri/factoidal/issues/729",
    "sbm11-pack-rdfxml-memory": "https://github.com/danbri/factoidal/issues/838",
    "sbm11-pack-jsonld-memory": "https://github.com/danbri/factoidal/issues/839",
    "rdfxml-write": "https://github.com/danbri/factoidal/issues/845",
    "jsonld-write": "https://github.com/danbri/factoidal/issues/712",
    "sbm11-pack-ttl-workers": "https://github.com/danbri/factoidal/issues/842",
    "sbm11-pack-trig-workers": "https://github.com/danbri/factoidal/issues/842",
    "sbm11-export-rdfxml-memory": "https://github.com/danbri/factoidal/issues/846",
    "sbm11-export-jsonld-memory": "https://github.com/danbri/factoidal/issues/847",
    "turtle-read-prefixes": "https://github.com/danbri/factoidal/issues/865",
    "sbm11-export-prefixes-time": "https://github.com/danbri/factoidal/issues/865",
}
# A run longer than this is not repeated: the minimum of several runs only
# removes timer and load noise, which is small against a run this long.
REPEAT_LIMIT = 5.0


def fixture(name: str, text_fn) -> Path:
    FIX.mkdir(parents=True, exist_ok=True)
    p = FIX / name
    if not p.exists():
        p.write_text(text_fn(), encoding="utf-8")
    return p


def multi_nt(n: int) -> Path:
    """multi.nt of tests/sbm11/syntax/gen_multi.py for n subjects: 8 triples for
    each subject, default graph, no blank nodes."""
    d = FIX / f"multi-{n}"
    p = d / "multi.nt"
    if not p.exists():
        d.mkdir(parents=True, exist_ok=True)
        subprocess.run([sys.executable, str(ROOT / "tests/sbm11/syntax/gen_multi.py"), str(d), str(n)],
                       check=True, timeout=CAP)
    return p


def rdfc_persons(n: int) -> str:
    """n blank-node persons, as tests/perf/l4_vs_fstar_wasm_bench.mjs writes
    them for its canonicalize row: every first-degree hash is unique."""
    rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
    xsd_int = "http://www.w3.org/2001/XMLSchema#integer"
    out = []
    for i in range(n):
        out.append(f"_:p{i} <{rdf_type}> <{EX}Person> .")
        out.append(f'_:p{i} <{EX}name> "Person {i}" .')
        out.append(f'_:p{i} <{EX}age> "{18 + i % 60}"^^<{xsd_int}> .')
    return "\n".join(out) + "\n"


def rdfc_collide(n: int) -> str:
    """n blank nodes with one quad each and the same first-degree hash."""
    rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
    return "".join(f"_:p{i} <{rdf_type}> <{EX}Person> .\n" for i in range(n))


def trig_blocks(n: int) -> str:
    per = 50
    out = [f"@prefix ex: <{EX}> ."]
    for j in range((n + per - 1) // per):
        out.append(f"ex:g{j} {{")
        for i in range(per):
            k = j * per + i
            if k < n:
                out.append(f"  ex:s{k} ex:p ex:o{k} .")
        out.append("}")
    return "\n".join(out) + "\n"


def trig_one_graph(n: int) -> str:
    body = "\n".join(f"  ex:s{i} ex:p ex:o{i} ." for i in range(n))
    return f"@prefix ex: <{EX}> .\nex:g {{\n{body}\n}}\n"


def sparql_collection_ask(n: int) -> str:
    return "SELECT ?s WHERE { ?s ?p ( %s ) }\n" % " ".join(str(i) for i in range(n))


def sparql_values_ask(n: int) -> str:
    """ASK with a trailing VALUES block of n IRIs (about 40 characters each):
    n tokens to read, one triple of data to match."""
    return "ASK { ?s ?p ?o } VALUES ?x { %s }\n" % " ".join(
        f"<{EX}item/{i:08d}>" for i in range(n))


def sparql_insert_data(n: int) -> str:
    return "INSERT DATA {\n%s}\n" % "".join(
        f'  <{EX}s{i}> <{EX}p> "value {i}" .\n' for i in range(n))


def sparql_insert_data_bnodes(n: int) -> str:
    return "INSERT DATA {\n%s}\n" % "".join(
        f'  _:b{i} <{EX}p> "value {i}" .\n' for i in range(n))


OWL = "http://www.w3.org/2002/07/owl#"
RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDFS = "http://www.w3.org/2000/01/rdf-schema#"
XSD = "http://www.w3.org/2001/XMLSchema#"


def owl_species_doc(n: int) -> str:
    """An OWL 2 DL document of n units, as N-Triples (the species check reads
    N-Triples). Every unit is DL, so `l4owl-species` exits 0."""
    ty = f"<{RDF}type>"
    out = [f"<{EX}o> {ty} <{OWL}Ontology> .",
           f"<{EX}p> {ty} <{OWL}ObjectProperty> .",
           f"<{EX}q> {ty} <{OWL}DatatypeProperty> ."]
    for i in range(n):
        c, c2 = f"<{EX}C{i}>", f"<{EX}C{i + 1}>"
        out += [f"{c} {ty} <{OWL}Class> .",
                f"{c2} {ty} <{OWL}Class> .",
                f"{c} <{RDFS}subClassOf> _:r{i} .",
                f"_:r{i} {ty} <{OWL}Restriction> .",
                f"_:r{i} <{OWL}onProperty> <{EX}p> .",
                f"_:r{i} <{OWL}someValuesFrom> {c2} .",
                f"<{EX}U{i}> {ty} <{OWL}Class> .",
                f"<{EX}U{i}> <{OWL}unionOf> _:l{i}a .",
                f"_:l{i}a <{RDF}first> {c} .",
                f"_:l{i}a <{RDF}rest> _:l{i}b .",
                f"_:l{i}b <{RDF}first> {c2} .",
                f"_:l{i}b <{RDF}rest> <{RDF}nil> .",
                f"<{EX}a{i}> {ty} {c} .",
                f'<{EX}a{i}> <{RDFS}label> "a{i}"@en .',
                f'<{EX}a{i}> <{EX}q> "{i}"^^<{XSD}integer> .',
                f"<{EX}a{i}> <{EX}p> _:x{i} .",
                f"_:x{i} {ty} {c2} ."]
    return "\n".join(out) + "\n"


def owl_species_bnode_chain(n: int) -> str:
    """One chain of n + 1 blank nodes linked by an object property assertion,
    with one named link at its start."""
    ty = f"<{RDF}type>"
    out = [f"<{EX}o> {ty} <{OWL}Ontology> .",
           f"<{EX}p> {ty} <{OWL}ObjectProperty> .",
           f"<{EX}C> {ty} <{OWL}Class> .",
           f"<{EX}a> {ty} <{EX}C> .",
           f"<{EX}a> <{EX}p> _:x0 ."]
    out += [f"_:x{i} <{EX}p> _:x{i + 1} ." for i in range(n)]
    return "\n".join(out) + "\n"


def owl_species_bnode_edges(n: int) -> str:
    """n pairs of blank nodes linked by an object property assertion, each
    pair with one named link."""
    ty = f"<{RDF}type>"
    out = [f"<{EX}o> {ty} <{OWL}Ontology> .",
           f"<{EX}p> {ty} <{OWL}ObjectProperty> .",
           f"<{EX}C> {ty} <{OWL}Class> ."]
    for i in range(n):
        out += [f"<{EX}a{i}> {ty} <{EX}C> .",
                f"<{EX}a{i}> <{EX}p> _:x{i} .",
                f"_:x{i} <{EX}p> _:y{i} ."]
    return "\n".join(out) + "\n"


def turtle_object_list(n: int) -> str:
    """One statement, one subject, one predicate, n objects."""
    objs = ", ".join(str(i) for i in range(n))
    return f"@prefix ex: <{EX}> .\nex:s ex:p {objs} .\n"


# row id -> (small size, make input path, command builder)
ROWS = {
    "rdfs-closure-wideflat": (
        1000,
        lambda n: fixture(f"clo-wideflat-{n}.ttl", lambda: bc.GENERATORS["wideflat"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "rdfs", "--format", "turtle"]),
    "rdfs-closure-dense": (
        250,
        lambda n: fixture(f"clo-dense-{n}.ttl", lambda: bc.GENERATORS["dense"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "rdfs", "--format", "turtle"]),
    "rdfs-closure-tree": (
        256,
        lambda n: fixture(f"clo-tree-{n}.ttl", lambda: bc.GENERATORS["tree"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "rdfs", "--format", "turtle"]),
    "owlrl-closure-chain": (
        20,
        lambda n: fixture(f"clo-chain-{n}.ttl", lambda: bc.GENERATORS["chain"](n)),
        lambda p: [str(BIN), "closure", str(p), "--regime", "owl-rl", "--format", "turtle"]),
    "trig-parse": (
        2500,
        lambda n: fixture(f"trig-blocks-{n}.trig", lambda: trig_blocks(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "trig"]),
    "trig-big-graph": (
        2500,
        lambda n: fixture(f"trig-one-{n}.trig", lambda: trig_one_graph(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "trig"]),
    "turtle-object-list": (
        25000,
        lambda n: fixture(f"turtle-object-list-{n}.ttl", lambda: turtle_object_list(n)),
        lambda p: [str(BIN), "parse", str(p), "--format", "turtle"]),
    "turtle-serialize": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "parse", str(p), "--format", "turtle", "--out", "turtle"]),
    # RDF/XML, one rdf:Description per triple, count only: the name
    # resolution and the walk of the children of rdf:RDF are linear
    # (https://github.com/danbri/factoidal/issues/814).
    "parse-rdfxml": (
        12500,
        lambda n: bl.gen_rdfxml(n),
        lambda p: [str(BIN), "parse", str(p), "--format", "rdfxml"]),
    "rdfc-iri": (
        1000,
        lambda n: bl.gen_canon("iri", n),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "rdfc-person": (
        125,
        lambda n: bl.gen_canon("person", n),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "rdfc-bnode-unique": (
        2000,
        lambda n: fixture(f"rdfc-bnode-unique-{n}.nq", lambda: rdfc_persons(n)),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "rdfc-bnode-collide": (
        2000,
        lambda n: fixture(f"rdfc-bnode-collide-{n}.nq", lambda: rdfc_collide(n)),
        lambda p: [str(BIN), "canonicalize", str(p), "--format", "nquads"]),
    "group-by-few": (
        2500,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT ?p (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?p"]),
    "group-by-many": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT ?s (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?s"]),
    "count-distinct": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT (COUNT(DISTINCT ?s) AS ?c) WHERE { ?s ?p ?o }"]),
    "count-distinct-star": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT (COUNT(DISTINCT *) AS ?c) WHERE { ?s ?p ?o }"]),
    "select-star": (
        1250,
        lambda n: bl.gene_slice(n),
        lambda p: [str(BIN), "query", str(p), "--format", "turtle", "--query-string",
                   "SELECT * WHERE { ?s ?p ?o }"]),
    "termwire-page-decode": (
        1000,
        lambda n: n,
        lambda n: [str(TERMWIRE_BIN), str(n), "100"]),
    "sparql-collection-parse": (
        2000,
        lambda n: fixture(f"sparql-collection-select-{n}.rq", lambda: sparql_collection_ask(n)),
        lambda p: [str(BIN), "query",
                   str(fixture("one-triple.nq", lambda: f"<{EX}s> <{EX}p> <{EX}o> .\n")),
                   "--query", str(p), "--format", "nquads"]),
    "sparql-collection-scope": (
        10000,
        lambda n: fixture(f"sparql-collection-select-{n}.rq", lambda: sparql_collection_ask(n)),
        lambda p: [str(BIN), "query",
                   str(fixture("one-triple.nq", lambda: f"<{EX}s> <{EX}p> <{EX}o> .\n")),
                   "--query", str(p), "--format", "nquads"]),
    "sparql-update-insert": (
        2000,
        lambda n: fixture(f"sparql-insert-data-{n}.ru", lambda: sparql_insert_data(n)),
        lambda p: [str(BIN), "update", str(fixture("empty.nq", lambda: "")),
                   "--update", str(p), "--format", "nquads"]),
    "sparql-update-insert-bnodes": (
        4000,
        lambda n: fixture(f"sparql-insert-data-bnodes-{n}.ru", lambda: sparql_insert_data_bnodes(n)),
        lambda p: [str(BIN), "update", str(fixture("empty.nq", lambda: "")),
                   "--update", str(p), "--format", "nquads"]),
    "owl-species": (
        2000,
        lambda n: fixture(f"owl-species-{n}.nt", lambda: owl_species_doc(n)),
        lambda p: [str(SPECIES_BIN), str(p)]),
    "owl-species-bnode-edges": (
        8000,
        lambda n: fixture(f"owl-species-bnode-edges-{n}.nt", lambda: owl_species_bnode_edges(n)),
        lambda p: [str(SPECIES_BIN), str(p)]),
    "owl-species-bnode-chain": (
        8000,
        lambda n: fixture(f"owl-species-bnode-chain-{n}.nt", lambda: owl_species_bnode_chain(n)),
        lambda p: [str(SPECIES_BIN), str(p)]),
    "shacl-person": (
        500,
        lambda n: bl.shacl_manifest(*bl.gen_shacl(n)),
        lambda p: [str(SHACL_BIN), "--conforms-only", str(p)]),
    # The library serialisers, through the tool that writes test data
    # (formal/lean4/Harness/SourceConvert.lean). The N-Triples text is read as
    # N-Quads (the quad reader is linear), so the time is the writer's.
    "rdfxml-write": (
        2000,
        lambda n: multi_nt(n),
        lambda p: [str(SOURCE_CONVERT_BIN), str(p), str(FIX / "write-out.rdf"),
                   "--from", "nquads", "--to", "rdfxml"]),
    "jsonld-write": (
        2000,
        lambda n: multi_nt(n),
        lambda p: [str(SOURCE_CONVERT_BIN), str(p), str(FIX / "write-out.jsonld"),
                   "--from", "nquads", "--to", "jsonld"]),
}


def best_of(cmd, runs):
    best = None
    for _ in range(runs):
        t0 = time.perf_counter()
        try:
            r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                               timeout=CAP)
        except subprocess.TimeoutExpired:
            return None, f"timeout after {CAP:.0f} s"
        except FileNotFoundError as e:
            return None, f"cannot run {cmd[0]}: {e.strerror}"
        dt = time.perf_counter() - t0
        if r.returncode != 0:
            return None, f"exit {r.returncode}: {r.stderr.decode('utf-8', 'replace')[:200]}"
        best = dt if best is None else min(best, dt)
        if dt > REPEAT_LIMIT:
            break
    return best, None


STARTUP_BUDGET = 0.020

# Rows that compare a verb with `parse` of the SAME input (gene.ttl, 4x the
# base size): the verb may take at most RATIO times the CPU time and RATIO
# times the peak resident memory of the parse. A COUNT(*) query reads the
# file once and counts; its cost above the parse is the evaluation. The
# command line used to write the parsed dataset as N-Quads text and parse the
# text again (https://github.com/danbri/factoidal/issues/724): 5.7 times the
# CPU time and 3.7 times the memory of `parse` before the repair, 1.6 and 1.0
# after (RDF/DatasetNormalize.lean, Wasm/Ops/FromDataset.lean).
PARSE_RATIO = 2.0
PARSE_RATIO_ROWS = {
    "query-vs-parse": (1250, "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }"),
}


def best_cpu_rss(cmd, runs):
    """Minimum CPU time of `runs` runs and the peak RSS (KB) of that run."""
    best = None
    for _ in range(runs):
        t = bl.run_once(cmd, CAP)
        if t["status"] != "ok":
            return None, f"exit status {t['status']}"
        if best is None or t["cpu"] < best["cpu"]:
            best = t
        if t["wall"] > REPEAT_LIMIT:
            break
    return best, None


def parse_ratio_row(rid, runs):
    if rid in SBM11_PACK_RATIO_ROWS:
        return sbm11_pack_ratio_row(rid, runs)
    if rid in SBM11_WORKERS_ROWS:
        return sbm11_workers_row(rid)
    x, sparql = PARSE_RATIO_ROWS[rid]
    p = bl.gene_slice(4 * x)
    q, e1 = best_cpu_rss([str(BIN), "query", str(p), "--format", "turtle",
                          "--query-string", sparql], runs)
    r, e2 = best_cpu_rss([str(BIN), "parse", str(p), "--format", "turtle"], runs)
    if e1 or e2:
        return False, f"n={4 * x}: {e1 or e2}"
    ok = (q["cpu"] <= PARSE_RATIO * max(r["cpu"], FLOOR)
          and q["rss_kb"] <= PARSE_RATIO * r["rss_kb"])
    return ok, (f"n={4 * x}: query {q['cpu']:.3f} s CPU {q['rss_kb'] / 1024:.0f} MB, "
                f"parse {r['cpu']:.3f} s CPU {r['rss_kb'] / 1024:.0f} MB "
                f"(ratios {q['cpu'] / max(r['cpu'], 1e-9):.1f} and "
                f"{q['rss_kb'] / max(r['rss_kb'], 1):.1f}; bound {PARSE_RATIO})")


# Rows that bound the peak resident memory of a verb PER INPUT BYTE
# (https://github.com/danbri/factoidal/issues/729). The measure is the slope
#
#     (peak RSS at 4x - peak RSS at x) / (input bytes at 4x - input bytes at x)
#
# so the fixed memory of a started process (about 12 MB) does not enter it,
# and a ratio to the input is not read as a trend (the error recorded in
# docs/designissues/2026-09-05-shard-pack-profile-and-memory.md section 3).
# Peak RSS does not move with load, so one run per size is enough.
#
# query-memory: 32 bytes. The whole document as a Lean `List Char` costs 34
# bytes of peak RSS per input byte on its own (`l4query-phases --stop-after
# chars`), so any path that builds it again fails the row. Measured 36.6
# before the repair (parseTurtle's `text.toList`), 27 after
# (`Syntax.parseTurtleText`), 10,000 to 40,000 paragraphs.
# query-memory-fstar: 6 bytes, 3 times the F* engine's slope on the same
# files (2.0: 16 MB at 10,000 and 42 MB at 160,000 paragraphs). This is the
# survey's memory rule (section 2 of the design record) as a gate row.
MEMORY_ROWS = {
    "query-memory": (10000, "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }", 32.0),
    "query-memory-fstar": (10000, "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }", 6.0),
}


# The strict `parse FILE` of N-Triples and Turtle reads the file in 64 KiB
# chunks (https://github.com/danbri/factoidal/issues/813). With `--out nquads`
# it writes each chunk's lines and keeps none, so its peak RSS does not grow
# with the input: bound 1 byte per input byte. Before the repair the whole
# file was one `String`, the N-Triples reader built its `List Char`, and the
# whole dataset and its N-Quads text were built before the first line was
# written. The count (`parse` without `--out`) keeps the set of distinct
# triples (RDF 1.1 Concepts section 3), which grows with the input: bound 12.
# Measured 2026-10-13 (peak RSS through /usr/bin/time), before the repair
# (`d371f1d9`) and after: parse-nt-memory 37.1 and 0.2, parse-ttl-memory 30.2
# and 0.0, count-nt-memory 37.5 and 6.2 bytes per input byte.
# Each value is (base size, file maker, extra arguments, bound).
PARSE_MEMORY_ROWS = {
    "parse-nt-memory": (25000, bl.gen_nt, ["--format", "ntriples", "--out", "nquads"], 1.0),
    "parse-ttl-memory": (20000, bl.gene_slice, ["--format", "turtle", "--out", "nquads"], 1.0),
    "count-nt-memory": (25000, bl.gen_nt, ["--format", "ntriples"], 12.0),
    # RDF/XML (https://github.com/danbri/factoidal/issues/771): the document
    # characters are one array of 8 bytes per character, and the triples, the
    # N-Quads text and the parser's notes grow with the input; no element tree
    # of rdf:RDF is built (`RdfXml.parseRdfXml_eq_stream`). Measured
    # 2026-10-13 with gen_rdfxml (one rdf:Description per triple), 25,000 and
    # 100,000 triples: 55.1 bytes of peak RSS per input byte on `main`
    # `80dc8ffc` (the document as `List Char`, then the element tree), 12.3
    # after the repair.
    "parse-rdfxml-memory": (25000, bl.gen_rdfxml, ["--format", "rdfxml", "--out", "nquads"], 16.0),
}


def peak_rss_run(cmd):
    """Run `cmd` under /usr/bin/time and take the peak RSS (KB) from it.

    `bl.run_once` takes `ru_maxrss` from `os.wait4`, and the maximum of a
    child forked from this Python process includes the pages it shared with
    the parent before `exec`: on 2026-10-13 every row below read 94 MB, the
    harness's own size, at both sizes, so a command that holds 24 MB and one
    that holds 90 MB gave the same slope, 0.0 (found while adding the
    `parse-*-memory` rows of https://github.com/danbri/factoidal/issues/813).
    `/usr/bin/time` forks the command from its own small process, as
    `tools/sota-bench.py` does."""
    tfile = FIX / "peak-rss.time"
    FIX.mkdir(parents=True, exist_ok=True)
    if os.path.exists("/usr/bin/time"):
        wrap = ["/usr/bin/time", "-f", "%M", "-o", str(tfile)]
    else:  # the CCR image has no /usr/bin/time; the wrapper is a small process too
        wrap = [sys.executable, str(ROOT / "tests/trig-pack/peak_rss.py"), "--kb-file", str(tfile)]
    t = bl.run_once(wrap + cmd, CAP)
    if t["status"] == "ok":
        try:
            t["rss_kb"] = int(tfile.read_text().strip().splitlines()[-1])
        except (OSError, ValueError, IndexError):
            t["status"] = "no /usr/bin/time output"
    return t


# The TriG shard pack reads its source in 65,536-byte chunks
# (https://github.com/danbri/factoidal/issues/769). Before that, `l4block-shard-pack`
# read the whole file and `parseTriG` built its `List Char` (24 bytes per
# source byte) beside the dataset. The row packs a generated TriG file
# (tests/trig-pack/gen_trig.py, 60 graphs, one contiguous block each) at x and
# 4x and bounds the slope of peak RSS. Measured 2026-10-14: 3.9 bytes of peak
# RSS per source byte over the whole of a 100 MB pack (the key-result target
# is 12), but 11.9 between 4 MB and 16 MB, because the open runs fill up to
# `maxCarriedRows` before the first flush. Bound 20 therefore leaves room for
# that start-up growth and still fails a pack that reads the whole source:
# `L4_PACK_BUFFERED=1` (the whole-source route) measured 70.7.
PACK_MEMORY_ROWS = {
    "pack-trig-memory": (4_000_000, 20.0),
}
PACK_BIN = Path(os.environ.get("L4_PACK_BIN",
                               ROOT / "formal/lean4/.lake/build/bin/l4block-shard-pack"))


def gen_trig_fixture(nbytes):
    FIX.mkdir(parents=True, exist_ok=True)
    p = FIX / f"pack-{nbytes}.trig"
    if not p.exists():
        subprocess.run([sys.executable, str(ROOT / "tests/trig-pack/gen_trig.py"), str(p),
                        str(nbytes)], check=True, timeout=CAP)
    return p


def pack_memory_row(rid):
    import shutil
    x, bound = PACK_MEMORY_ROWS[rid]
    if not PACK_BIN.exists():
        return False, f"{PACK_BIN} not built (cd formal/lean4 && lake build l4block-shard-pack)"
    pts = []
    for n in (x, 4 * x):
        p = gen_trig_fixture(n)
        out = FIX / f"pack-out-{n}"
        shutil.rmtree(out, ignore_errors=True)
        t = peak_rss_run([str(PACK_BIN), str(p), str(out), "ibk4"])
        shutil.rmtree(out, ignore_errors=True)
        if t["status"] != "ok":
            return False, f"n={n}: exit status {t['status']}"
        pts.append((n, p.stat().st_size, t["rss_kb"]))
    (n1, b1, r1), (n4, b4, r4) = pts
    slope = (r4 - r1) * 1024 / max(b4 - b1, 1)
    return slope <= bound, (f"{b1} bytes {r1 / 1024:.0f} MB -> {b4} bytes {r4 / 1024:.0f} MB: "
                            f"{slope:.1f} bytes of peak RSS per source byte (bound {bound})")


# The SBM11 packer, one row per source syntax it reads
# (https://github.com/danbri/factoidal/issues/837). `l4sbm11-pack` reads a source
# in 65,536-byte chunks through `RDF/Source.lean`, spills the runs of a batch to
# disk when 20,000 terms (--run-terms) or 1,048,576 quads are in memory, and
# sorts the rows of its permutations in runs of 50,000 (--sort-rows). The rows
# below pack n statements of the form `ex:s<i> ex:p "<payload>"`, a payload of
# about 370 characters that differs in every statement, at n, 2n and 4n, and
# bound the slope of peak RSS
#
#     (peak RSS at 4n - peak RSS at n) / (source bytes at 4n - source bytes at n)
#
# The payload makes the source large against the packer's own state per
# statement (about 40 bytes of row), so a source of 5 MB to 21 MB shows whether
# the reader keeps the text. A dataset of short statements would not: its rows
# grow with the number of quads up to the batch cap, at 1 to 4 bytes per source
# byte (measured with `ex:s<i> ex:p ex:o<i>`: 4.1 bytes per source byte from 2.7 MB to
# 11.4 MB of Turtle). The packer runs one worker, because Turtle, TriG, RDF/XML and
# JSON-LD are read by one worker. The peak of the 4n pack varies between runs by up to
# 10 MB (a sort task of the packer overlaps the read, or it does not). The bound of 0.75
# allows 22 MB of growth over the 30 MB between the n and 4n sources. The largest growth
# seen is 8 MB, and a reader that keeps the source adds 30 MB or more and fails.
# Measured 2026-10-14 (peak RSS through the wrapper, MB): Turtle 75 to 78 at n and 71 to
# 85 at 4n (slope -0.13 to 0.28); TriG 75 to 79 at n and 71 to 83 at 4n (-0.14 to 0.21);
# RDF/XML 51 to 58, 78 to 90 and 147 at 5,000, 10,000 and 20,000 statements (13.4 to
# 14.5); JSON-LD 56 to 58, 78 to 88 and 129 to 140 (11.3 to 13.5). Each value is
# (statements at x, fixture maker, file extension, bound).
SBM11_PACK_BIN = Path(os.environ.get("L4_SBM11_PACK_BIN", BIN.parent / "l4sbm11-pack"))
SBM11_PACK_ARGS = ["--workers", "1", "--run-terms", "20000", "--sort-rows", "50000"]


def sbm11_payload(i: int) -> str:
    return f"record {i}: " + "the quick brown fox jumps over the lazy dog; " * 8


def sbm11_ttl(n: int) -> str:
    return f"@prefix ex: <{EX}> .\n" + "".join(
        f'ex:s{i} ex:p "{sbm11_payload(i)}" .\n' for i in range(n))


def sbm11_trig(n: int) -> str:
    """Graph blocks of 1,000 statements, 100 different graph names."""
    per = 1000
    out = [f"@prefix ex: <{EX}> ."]
    for j in range((n + per - 1) // per):
        out.append(f"ex:g{j % 100} {{")
        out.extend(f'  ex:s{i} ex:p "{sbm11_payload(i)}" .'
                   for i in range(j * per, min(n, (j + 1) * per)))
        out.append("}")
    return "\n".join(out) + "\n"


def sbm11_rdfxml(n: int) -> str:
    return ('<?xml version="1.0"?>\n<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" '
            f'xmlns:ex="{EX}">\n' + "".join(
                f'  <rdf:Description rdf:about="{EX}s{i}"><ex:p>{sbm11_payload(i)}</ex:p>'
                f'</rdf:Description>\n' for i in range(n)) + "</rdf:RDF>\n")


def sbm11_jsonld(n: int) -> str:
    return "[" + ",\n".join(
        f'{{"@id":"{EX}s{i}","{EX}p":"{sbm11_payload(i)}"}}' for i in range(n)) + "]\n"


SBM11_PACK_MEMORY_ROWS = {
    "sbm11-pack-ttl-memory": (25000, sbm11_ttl, "ttl", 0.75),
    "sbm11-pack-trig-memory": (25000, sbm11_trig, "trig", 0.75),
    "sbm11-pack-rdfxml-memory": (5000, sbm11_rdfxml, "rdf", 0.75),
    "sbm11-pack-jsonld-memory": (5000, sbm11_jsonld, "jsonld", 0.75),
}


class MeasurementError(RuntimeError):
    """A row could not measure: the run is red whatever XFAIL says. An
    expected failure must fail because of the bound, not because the command
    crashed or printed nothing (skills/measuring-inference)."""


def sbm11_need_pack_bin():
    if not SBM11_PACK_BIN.exists():
        raise MeasurementError(
            f"{SBM11_PACK_BIN} not built (cd formal/lean4 && lake build l4sbm11-pack)")


def sbm11_pack_memory_row(rid):
    import shutil
    x, make, ext, bound = SBM11_PACK_MEMORY_ROWS[rid]
    sbm11_need_pack_bin()
    pts = []
    for n in (x, 2 * x, 4 * x):
        p = fixture(f"{rid}-{n}.{ext}", lambda n=n: make(n))
        out = FIX / f"{rid}-out-{n}"
        shutil.rmtree(out, ignore_errors=True)
        t = peak_rss_run([str(SBM11_PACK_BIN), str(p), str(out)] + SBM11_PACK_ARGS)
        shutil.rmtree(out, ignore_errors=True)
        if t["status"] != "ok":
            raise MeasurementError(f"{rid}: n={n}: exit status {t['status']}")
        pts.append((n, p.stat().st_size, t["rss_kb"]))
    (n1, b1, r1), (n2, b2, r2), (n4, b4, r4) = pts
    slope = (r4 - r1) * 1024 / max(b4 - b1, 1)
    return slope <= bound, (f"n={n1} {r1 / 1024:.0f} MB ({b1} bytes) -> n={n2} {r2 / 1024:.0f} MB -> "
                            f"n={n4} {r4 / 1024:.0f} MB ({b4} bytes): {slope:.2f} bytes of peak RSS "
                            f"per source byte (bound {bound})")


# `l4sbm11 export` over a generation (https://github.com/danbri/factoidal/issues/837
# item 6). The export reads the SPO permutation block by block and gives each quad
# to the serialiser layer, which writes N-Quads one line for each quad and Turtle and
# TriG one statement for each subject; the output goes to a file in 64 KiB writes. The
# rows pack n statements of the form `ex:s<i> ex:p "<payload>"` (a payload of about 370
# characters; for TriG the source of `sbm11_trig`, 100 graph names in blocks of 1,000
# statements), export the generation, and bound the slope of peak RSS
#
#     (peak RSS at 4n - peak RSS at n) / (output bytes at 4n - output bytes at n)
#
# as the pack rows do. The packing is not measured. A writer that keeps the quads
# adds the payload strings (about 1 byte per output byte) and the quads themselves, and
# fails the bound of 0.75. RDF/XML and JSON-LD are written whole by the library
# (issues 846 and 847): expected failures at 2,000, 4,000 and 8,000 statements, sizes at
# which the quadratic RDF/XML writer (issue 845) still finishes in seconds.
# Each value is (statements at x, fixture maker, source extension, export format,
# bound).
SBM11_EXPORT_MEMORY_ROWS = {
    "sbm11-export-nq-memory": (25000, sbm11_ttl, "ttl", "nquads", 0.75),
    "sbm11-export-ttl-memory": (25000, sbm11_ttl, "ttl", "turtle", 0.75),
    "sbm11-export-trig-memory": (25000, sbm11_trig, "trig", "trig", 0.75),
    "sbm11-export-rdfxml-memory": (2000, sbm11_ttl, "ttl", "rdfxml", 0.75),
    "sbm11-export-jsonld-memory": (2000, sbm11_ttl, "ttl", "jsonld", 0.75),
}
_EXPORT_GENS: dict = {}


def sbm11_export_generation(kind, make, ext, n):
    """The generation of n statements of fixture `kind`, packed once for the run."""
    import shutil
    key = (kind, n)
    if key not in _EXPORT_GENS:
        p = fixture(f"sbm11-export-{kind}-{n}.{ext}", lambda: make(n))
        gen = FIX / f"sbm11-export-{kind}-gen-{n}"
        shutil.rmtree(gen, ignore_errors=True)
        t = bl.run_once([str(SBM11_PACK_BIN), str(p), str(gen)] + SBM11_PACK_ARGS, CAP)
        if t["status"] != "ok":
            raise MeasurementError(f"pack of {p.name}: exit status {t['status']}")
        _EXPORT_GENS[key] = gen
    return _EXPORT_GENS[key]


def sbm11_export_memory_row(rid):
    x, make, ext, fmt, bound = SBM11_EXPORT_MEMORY_ROWS[rid]
    sbm11_need_pack_bin()
    if not SBM11_BIN.exists():
        raise MeasurementError(f"{SBM11_BIN} not built (cd formal/lean4 && lake build l4sbm11)")
    kind = make.__name__
    pts = []
    for n in (x, 2 * x, 4 * x):
        gen = sbm11_export_generation(kind, make, ext, n)
        out = FIX / f"{rid}-out-{n}"
        out.unlink(missing_ok=True)
        t = peak_rss_run([str(SBM11_BIN), "export", str(gen), "--format", fmt, "--out", str(out)])
        if t["status"] != "ok":
            raise MeasurementError(f"{rid}: n={n}: exit status {t['status']}")
        size = out.stat().st_size
        out.unlink(missing_ok=True)
        if size == 0:
            raise MeasurementError(f"{rid}: n={n}: the export wrote no byte")
        pts.append((n, size, t["rss_kb"]))
    (n1, b1, r1), (n2, b2, r2), (n4, b4, r4) = pts
    slope = (r4 - r1) * 1024 / max(b4 - b1, 1)
    return slope <= bound, (f"n={n1} {r1 / 1024:.0f} MB ({b1} bytes out) -> n={n2} {r2 / 1024:.0f} MB -> "
                            f"n={n4} {r4 / 1024:.0f} MB ({b4} bytes out): {slope:.2f} bytes of peak RSS "
                            f"per output byte (bound {bound})")


# CPU time of one pass over a generation (https://github.com/danbri/factoidal/issues/854).
# `l4sbm11 dump` and `l4sbm11 export --format nquads` read the SPO permutation block by
# block and turn each id into a term; the work for one quad does not depend on the size
# of the store, so the time is linear in the statements and time(4x) is 4.0 times time(x).
# The bound is 5.25: it lies between the highest ratio after the repair (4.5; three runs
# of each row, the second and third with a load average of 3: CPU time of the child, not
# wall time, but the caches of the 4 vCPUs are shared) and the lowest before it (6.0 for
# dump, 6.7 for export). The sizes are the ones of the issue (100,000 to 400,000
# statements): the quadratic term is a cost for each chunk of the dictionary that grows
# with the number of chunks, so it is small beside the linear cost below 100 MB of
# dictionary (the ratio at 25,000 to 100,000 statements was 3.8 before the repair, so
# a smaller x does not show the defect). Both rows read the same three generations,
# packed once for the run.
SBM11_READ_TIME_BOUND = 5.25
SBM11_READ_TIME_ROWS = {
    "sbm11-dump-time": (
        100000, lambda gen, out: [str(SBM11_BIN), "dump", str(gen), "--verify", "merkle"]),
    "sbm11-export-nq-time": (
        100000, lambda gen, out: [str(SBM11_BIN), "export", str(gen), "--format", "nquads",
                                  "--out", str(out), "--verify", "merkle"]),
}


def sbm11_read_time_row(rid):
    x, cmd_of = SBM11_READ_TIME_ROWS[rid]
    sbm11_need_pack_bin()
    if not SBM11_BIN.exists():
        raise MeasurementError(f"{SBM11_BIN} not built (cd formal/lean4 && lake build l4sbm11)")
    pts = []
    for n in (x, 2 * x, 4 * x):
        gen = sbm11_export_generation(sbm11_ttl.__name__, sbm11_ttl, "ttl", n)
        out = FIX / f"{rid}-out-{n}"
        out.unlink(missing_ok=True)
        t = bl.run_once(cmd_of(gen, out), CAP)
        if t["status"] != "ok":
            raise MeasurementError(f"{rid}: n={n}: exit status {t['status']}")
        if rid == "sbm11-dump-time":
            lines = t["out_lines"]
        else:
            lines = sum(1 for _ in out.open("rb")) if out.exists() else 0
            out.unlink(missing_ok=True)
        if lines != n:
            raise MeasurementError(f"{rid}: n={n}: the command wrote {lines} lines")
        pts.append((n, t["cpu"]))
    (n1, t1), (n2, t2), (n4, t4) = pts
    ok = t4 <= SBM11_READ_TIME_BOUND * max(t1, FLOOR)
    return ok, (f"n={n1} {t1:.3f} s -> n={n2} {t2:.3f} s -> n={n4} {t4:.3f} s CPU "
                f"(ratios {t2 / max(t1, 1e-9):.1f} and {t4 / max(t2, 1e-9):.1f} per doubling; "
                f"{t4 / max(t1, 1e-9):.1f} for 4x input, bound {SBM11_READ_TIME_BOUND})")


# CPU time of `l4sbm11 export --format turtle` with a table of n prefixes, every one used
# (https://github.com/danbri/factoidal/issues/865). The generation has n statements, the
# subject of statement i under namespace i and the object under namespace i + 1 (modulo n),
# so the table of n `--prefix LABEL=IRI` arguments is used in full. The table can come from
# the command line only, and a command line holds a few tens of thousands of them (n = 16,000
# is about 740 KB of arguments; ARG_MAX is 2 MB). The row measures the time at n = 4,000,
# 8,000 and 16,000 with the series rule of `doubling_check` and no proof (`--verify none`), so
# that the work that does not depend on the table is as small as the command allows. Two
# costs grew with the table: `parseOpts` appended each prefix to the end of the list that
# held the others, and `Sink.bodyPush` scanned the table for the prefix of each IRI.
SBM11_PREFIX_TIME_X = 4000


def sbm11_pfx_nt(n: int) -> str:
    return "".join(f"<{EX}n{i}/s> <{EX}p> <{EX}n{(i + 1) % n}/o> .\n" for i in range(n))


def sbm11_export_prefixes_time_row(rid):
    sbm11_need_pack_bin()
    if not SBM11_BIN.exists():
        raise MeasurementError(f"{SBM11_BIN} not built (cd formal/lean4 && lake build l4sbm11)")
    pts = []
    for n in (SBM11_PREFIX_TIME_X, 2 * SBM11_PREFIX_TIME_X, 4 * SBM11_PREFIX_TIME_X):
        gen = sbm11_export_generation(sbm11_pfx_nt.__name__, sbm11_pfx_nt, "nt", n)
        out = FIX / f"{rid}-out-{n}"
        cmd = [str(SBM11_BIN), "export", str(gen), "--format", "turtle", "--out", str(out),
               "--verify", "none"]
        for i in range(n):
            cmd += ["--prefix", f"n{i}={EX}n{i}/"]
        out.unlink(missing_ok=True)
        t = bl.run_once(cmd, CAP)
        if t["status"] != "ok":
            raise MeasurementError(f"{rid}: n={n}: exit status {t['status']}")
        with out.open(encoding="utf-8") as f:
            declared = sum(1 for line in f if line.startswith("@prefix "))
        out.unlink(missing_ok=True)
        if declared != n:
            raise MeasurementError(f"{rid}: n={n}: the Turtle declares {declared} prefixes")
        pts.append((n, t["cpu"]))
    return doubling_check(pts, "CPU")


SBM11_PREFIX_TIME_ROWS = {"sbm11-export-prefixes-time": sbm11_export_prefixes_time_row}


# Peak resident memory of `l4sbm11 dump --verify merkle`
# (https://github.com/danbri/factoidal/issues/859). `dump` reads the SPO permutation
# block by block and turns each id into a term, as `export` does. Under `merkle` it
# kept every chunk of the dictionary (GDV1, GDX1) and of the permutation file that it
# had verified, so its peak grew with the store, as the dictionary text does: about 1 byte
# for each output byte (the `export` rows above fail at 0.75 for a writer that keeps the
# quads). The row measures the slope
#
#     (peak RSS at 4n - peak RSS at n) / (output bytes at 4n - output bytes at n)
#
# at 100,000, 200,000 and 400,000 statements (the source of `sbm11_ttl`: generations of 38
# MB, 76 MB and 152 MB, N-Quads of 43 MB, 86 MB and 173 MB). The peak is the VmHWM that
# the command prints on stderr (`peak-rss=... kB`): the same number as `/usr/bin/time -f
# %M`, and the command writes its output to a pipe that this script counts, so the
# measurement needs no wrapper. The sizes start at 100,000 statements. The repaired
# `dump` keeps at most 16 MiB of dictionary chunks for each file (`chunkKeepBytes`), and its
# peak RSS is 43, 62 and 61 MB at 25,000, 50,000 and 100,000 statements: it stops rising at
# about 50,000 statements, where the dictionary (19 MB) is above that budget. The row
# measures the slope on that plateau. The bound is the one of the export rows: 0.75 byte per
# output byte allows 97 MB of growth over the 130 MB between the outputs at n and 4n, and a
# reader that keeps the dictionary (150 MB at 400,000 statements) fails it.
SBM11_DUMP_MEMORY_ROWS = {"sbm11-dump-memory": (100000, 0.75)}


def sbm11_dump_memory_row(rid):
    import re
    x, bound = SBM11_DUMP_MEMORY_ROWS[rid]
    sbm11_need_pack_bin()
    if not SBM11_BIN.exists():
        raise MeasurementError(f"{SBM11_BIN} not built (cd formal/lean4 && lake build l4sbm11)")
    pts = []
    for n in (x, 2 * x, 4 * x):
        gen = sbm11_export_generation(sbm11_ttl.__name__, sbm11_ttl, "ttl", n)
        t = bl.run_once([str(SBM11_BIN), "dump", str(gen), "--verify", "merkle"], CAP)
        if t["status"] != "ok":
            raise MeasurementError(f"{rid}: n={n}: exit status {t['status']}")
        m = re.search(r"\bpeak-rss=(\d+) kB", t["stderr"])
        if not m:
            raise MeasurementError(f"{rid}: n={n}: the summary line on stderr has no peak-rss")
        if t["out_lines"] != n:
            raise MeasurementError(f"{rid}: n={n}: the command wrote {t['out_lines']} lines")
        pts.append((n, t["out_bytes"], int(m.group(1))))
    (n1, b1, r1), (n2, b2, r2), (n4, b4, r4) = pts
    slope = (r4 - r1) * 1024 / max(b4 - b1, 1)
    return slope <= bound, (f"n={n1} {r1 / 1024:.0f} MB ({b1} bytes out) -> n={n2} {r2 / 1024:.0f} MB -> "
                            f"n={n4} {r4 / 1024:.0f} MB ({b4} bytes out): {slope:.2f} bytes of peak RSS "
                            f"per output byte, {(r4 - r1) * 1024 / (n4 - n1):.0f} per statement "
                            f"(bound {bound} per output byte)")


# CPU time of a verified range read that has no chunk cache
# (https://github.com/danbri/factoidal/issues/859). `PosixRangeIO.readVerifiedRange?` reads
# a range of a file: every 65,536-byte chunk that the range touches is admitted by a Merkle
# proof against the root of the manifest. The reader computed the proof of a chunk from all
# the leaves of the file (`BlockMerkle.proofWith?`, `n - 1` node hashes for `n` chunks), so a
# read of `c` chunks of a file of `n` cost `c * (n - 1)` hashes: the square of the file when
# the range is most of the file. `l4block-shard-merkle-pread` and `l4block-shard-merkle-scan`
# call it, and the shard packer cuts its blocks at 2 MiB, so a shard directory that it writes
# has no artifact above about 64 chunks. One statement with a literal of 16 MB makes one
# artifact of 257 chunks (the packer needs 11 s and 1.1 GB), and one of 64 MB makes 1,024
# chunks (43 s and 3.0 GB). With 128, 256 and 512 chunks of a packed shard the time at 4x
# chunks was 4.9 times the time at x (0.070 s, 0.149 s and 0.342 s of CPU time on
# 2026-10-14), under the bound: the linear work and the process start are most of the time
# below about 500 chunks. The row therefore reads files that
# `l4merkle-range-read make` writes (a file of n chunks of pseudo-random bytes, its
# `.merkle` sidecar and its root, in about 1 s for 128 MB), with
# `l4merkle-range-read read --reader leaves`, the call of `readVerifiedRange?`, over the whole
# file: 512, 1,024 and 2,048 chunks (32 MB, 64 MB and 128 MB). The user CPU time of the read
# (the minimum of 5 runs) at 4x chunks is bounded by SBM11_READ_TIME_BOUND times the time at x
# (with the floor FLOOR of the other rows). The bound lies between 4.7 (the highest ratio in
# seven runs of the row after the repair; the lowest was 3.5) and 10.5 (the lowest ratio
# before it, by hand; the row gave 12.1). The row bounds the USER time and prints the system
# time: the reader holds the chunks, their concatenation and the copy of the range (6 bytes of
# memory for each byte of the range, 770 MB for 128 MB), and the page faults for that memory
# cost 0.2 s to 1.9 s of system time for the same read of 64 MB on this VM, which is more
# than the repaired reader's user time. The hashing is user time. Linear work is one pread, one
# SHA-256 and one copy for each chunk, 4.0 for 4x chunks; measured on the reader of 2026-10-13
# (user time, minimum of 5 runs): 0.148 s, 0.389 s, 1.097 s and 4.088 s at 256, 512, 1,024 and
# 2,048 chunks, 10.5 for 512 to 2,048 chunks.
# Before running a measured row the harness reads the smallest file with `--check` (the bytes
# are those of the file, read without any check) and reads it again with one byte changed,
# which the reader must refuse: a reader that admits a changed byte cannot be timed.
MERKLE_RANGE_TIME_ROWS = {"merkle-range-read-time": 512}
RANGE_BIN = Path(os.environ.get("L4_MERKLE_RANGE_BIN", BIN.parent / "l4merkle-range-read"))
MERKLE_RANGE_RUNS = 5


def merkle_range_time_row(rid):
    import shutil
    x = MERKLE_RANGE_TIME_ROWS[rid]
    if not RANGE_BIN.exists():
        raise MeasurementError(f"{RANGE_BIN} not built (cd formal/lean4 && lake build l4merkle-range-read)")
    pts = []
    for chunks in (x, 2 * x, 4 * x):
        d = FIX / f"{rid}-{chunks}"
        shutil.rmtree(d, ignore_errors=True)
        try:
            t = bl.run_once([str(RANGE_BIN), "make", str(d), str(chunks)], CAP)
            if t["status"] != "ok":
                raise MeasurementError(f"{rid}: make {chunks} chunks: exit status {t['status']}")
            if chunks == x:
                t = bl.run_once([str(RANGE_BIN), "read", str(d), "--check"], CAP)
                if t["status"] != "ok" or "match=true" not in t["first_line"]:
                    raise MeasurementError(f"{rid}: the check of {chunks} chunks: {t['status']} {t['first_line'][:200]!r}")
            best = sysbest = None
            for _ in range(MERKLE_RANGE_RUNS):
                t = bl.run_once([str(RANGE_BIN), "read", str(d), "--reader", "leaves"], CAP)
                if t["status"] != "ok":
                    raise MeasurementError(f"{rid}: chunks={chunks}: exit status {t['status']}: {t['stderr'][-160:]}")
                want = f"verified-bytes={chunks * 65536} chunks=0-{chunks - 1}"
                if want not in t["first_line"]:
                    raise MeasurementError(f"{rid}: chunks={chunks}: printed {t['first_line'][:160]!r}, not {want!r}")
                best = t["user"] if best is None else min(best, t["user"])
                sysbest = t["cpu"] - t["user"] if sysbest is None else min(sysbest, t["cpu"] - t["user"])
            if chunks == x:
                with open(d / "file.bin", "r+b") as f:
                    f.seek((chunks // 2) * 65536 + 100)
                    byte = f.read(1)
                    f.seek(-1, 1)
                    f.write(bytes([byte[0] ^ 1]))
                t = bl.run_once([str(RANGE_BIN), "read", str(d), "--reader", "leaves"], CAP)
                if t["status"] != "rc1":
                    raise MeasurementError(f"{rid}: a changed byte was not refused (status {t['status']})")
        finally:
            shutil.rmtree(d, ignore_errors=True)
        pts.append((chunks, best, sysbest))
    (n1, t1, s1), (n2, t2, s2), (n4, t4, s4) = pts
    ok = t4 <= SBM11_READ_TIME_BOUND * max(t1, FLOOR)
    return ok, (f"{n1} chunks {t1:.3f} s -> {n2} chunks {t2:.3f} s -> {n4} chunks {t4:.3f} s user CPU "
                f"(ratios {t2 / max(t1, 1e-9):.1f} and {t4 / max(t2, 1e-9):.1f} per doubling; "
                f"{t4 / max(t1, 1e-9):.1f} for 4x chunks, bound {SBM11_READ_TIME_BOUND}, "
                f"floor {FLOOR} s; system time {s1:.2f}, {s2:.2f} and {s4:.2f} s, not bounded)")


# The delta log of an SBM11 generation: the update that writes it, and the open that replays it
# (https://github.com/danbri/factoidal/issues/857, https://github.com/danbri/factoidal/issues/851
# and https://github.com/danbri/factoidal/issues/858; record:
# docs/designissues/2026-10-12-sbm11-stage5.md sections 4 and 10).
#
# sbm11-update-memory. A generation of n statements `<ex:s{i}> <ex:p> "v{i}"` is packed and
# activated, and the request `DELETE { ?s ex:p ?o } INSERT { ?s ex:q ?o } WHERE { ?s ex:p ?o }`
# is applied with `l4sbm11 update`: n solutions on the id path, 2n entries in ONE batch. The
# request text is a few bytes, so the memory is the batch's. The log is 123 bytes for each entry.
# The row measures the slope
#
#     (peak RSS at 4n - peak RSS at n) / (log bytes at 4n - log bytes at n)
#
# at n = 12,500, 25,000 and 50,000 (3 MB, 6 MB and 12 MB of log). The peak RSS is the one of
# /usr/bin/time, and the log bytes are the size of `deltas.dlog`. Measured 2026-10-14 on the
# unrepaired encoder: see SBM11_UPDATE_MEMORY_BOUND below.
#
# sbm11-open-log-memory, sbm11-replay-time. A generation of 200,000 statements (the same
# `<ex:s{i}> <ex:p> "v{i}"`, 6,251 dictionary pages) is packed and activated once. For each size
# the generation is copied and given a log of n entries by `tests/sbm11/gen_dlog.py` (a remove of
# (s{i}, p, "v{i}") and an add of (s{i}, q, "v{i}") for each of n/2 statements: the shape of the
# update above, every term but q in the dictionary), n = 25,000, 50,000 and 100,000 entries. The
# log is written by Python, so these rows test the reader at any size, whatever the writer does.
# `l4sbm11 query GEN 'ASK { ?s ?p ?o }'` opens the generation, which replays the log, and the
# row requires the summary line to say that it replayed `entries n`. Both rows read the same
# three runs.
SBM11_LOG_STATEMENTS = 200000
SBM11_UPDATE_SIZES = (12500, 25000, 50000)
SBM11_OPEN_SIZES = (25000, 50000, 100000)
SBM11_UPDATE_REQUEST = ("DELETE { ?s <" + EX + "p> ?o } INSERT { ?s <" + EX + "q> ?o } "
                        "WHERE { ?s <" + EX + "p> ?o }")
GEN_DLOG = ROOT / "tests/sbm11/gen_dlog.py"


def sbm11_log_nt(n: int) -> str:
    return "".join(f'<{EX}s{i}> <{EX}p> "v{i}" .\n' for i in range(n))


def sbm11_need_sbm11():
    sbm11_need_pack_bin()
    if not SBM11_BIN.exists():
        raise MeasurementError(f"{SBM11_BIN} not built (cd formal/lean4 && lake build l4sbm11)")


def sbm11_packed_root(name: str, n: int) -> Path:
    """A new collection root `FIX/name` with the activated generation `gen` of n statements."""
    import shutil
    root = FIX / name
    shutil.rmtree(root, ignore_errors=True)
    src = fixture(f"sbm11-log-{n}.nt", lambda: sbm11_log_nt(n))
    t = bl.run_once([str(SBM11_PACK_BIN), str(src), str(root / "gen")] + SBM11_PACK_ARGS, CAP)
    if t["status"] != "ok":
        raise MeasurementError(f"{name}: pack of {n} statements: exit status {t['status']}")
    t = bl.run_once([str(SBM11_BIN), "activate", str(root), "gen"], CAP)
    if t["status"] != "ok":
        raise MeasurementError(f"{name}: activation: exit status {t['status']}")
    return root


def sbm11_update_memory_row(rid):
    import re
    import shutil
    bound = SBM11_UPDATE_MEMORY_BOUND
    sbm11_need_sbm11()
    pts = []
    for n in SBM11_UPDATE_SIZES:
        root = sbm11_packed_root(f"{rid}-{n}", n)
        t = peak_rss_run([str(SBM11_BIN), "update", str(root), SBM11_UPDATE_REQUEST])
        if t["status"] != "ok":
            raise MeasurementError(f"{rid}: n={n}: exit status {t['status']}: {t['stderr'][-160:]}")
        m = re.search(r"\bops=(\d+)\b", t["first_line"])
        if not m or int(m.group(1)) != 2 * n:
            raise MeasurementError(f"{rid}: n={n}: the update printed {t['first_line'][:200]!r}, not ops={2 * n}")
        log = (root / "gen" / "deltas.dlog").stat().st_size
        shutil.rmtree(root, ignore_errors=True)
        pts.append((n, log, t["rss_kb"]))
    (n1, b1, r1), (n2, b2, r2), (n4, b4, r4) = pts
    slope = (r4 - r1) * 1024 / max(b4 - b1, 1)
    return slope <= bound, (f"n={n1} solutions: {b1} bytes of log, peak RSS {r1 / 1024:.0f} MB -> n={n2}: {b2} bytes, "
                            f"{r2 / 1024:.0f} MB -> n={n4}: {b4} bytes, {r4 / 1024:.0f} MB: {slope:.1f} bytes of peak "
                            f"RSS per log byte (bound {bound})")


_OPEN_BASE: list = []
_OPEN_RUNS: dict = {}


def sbm11_open_run(n: int) -> dict:
    """The open (replay) of a generation with a log of n entries, run three times (the result
    is kept for the rest of the process): the least CPU time, the least peak RSS, the log
    bytes, and the replay time that the command reports in the run of least CPU time. The
    user CPU time of one binary on one fixture varies by 15 % to 20 % on this VM."""
    import re
    import shutil
    if n in _OPEN_RUNS:
        return _OPEN_RUNS[n]
    sbm11_need_sbm11()
    if not GEN_DLOG.exists():
        raise MeasurementError(f"{GEN_DLOG} missing")
    if not _OPEN_BASE:
        _OPEN_BASE.append(sbm11_packed_root("sbm11-open-base", SBM11_LOG_STATEMENTS))
    work = FIX / f"sbm11-open-{n}"
    shutil.rmtree(work, ignore_errors=True)
    shutil.copytree(_OPEN_BASE[0], work)
    r = subprocess.run([sys.executable, "-I", str(GEN_DLOG), str(work / "gen" / "deltas.dlog"), str(n)],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=CAP)
    if r.returncode != 0:
        raise MeasurementError(f"gen_dlog.py {n}: exit {r.returncode}: {r.stderr.decode()[-160:]}")
    log = (work / "gen" / "deltas.dlog").stat().st_size
    runs = []
    for _ in range(3):
        t = peak_rss_run([str(SBM11_BIN), "query", str(work), "ASK { ?s ?p ?o }"])
        if t["status"] != "ok":
            shutil.rmtree(work, ignore_errors=True)
            raise MeasurementError(f"open of a log of {n} entries: exit status {t['status']}: {t['stderr'][-160:]}")
        err = t.get("stderr_full", "")
        m = re.search(r"delta batches (\d+), entries (\d+),.*?replay ms ([0-9.]+)", err)
        if not m or int(m.group(1)) != 1 or int(m.group(2)) != n:
            shutil.rmtree(work, ignore_errors=True)
            raise MeasurementError(f"open of a log of {n} entries: the summary line says {err[:260]!r}")
        runs.append({"cpu": t["cpu"], "rss_kb": t["rss_kb"], "replay_ms": float(m.group(3))})
    shutil.rmtree(work, ignore_errors=True)
    best = min(runs, key=lambda r: r["cpu"])
    _OPEN_RUNS[n] = {"n": n, "log": log, "rss_kb": min(r["rss_kb"] for r in runs), "cpu": best["cpu"],
                     "replay_ms": best["replay_ms"]}
    return _OPEN_RUNS[n]


def sbm11_open_memory_row(rid):
    bound = SBM11_OPEN_MEMORY_BOUND
    runs = [sbm11_open_run(n) for n in SBM11_OPEN_SIZES]
    a, b, c = runs
    slope = (c["rss_kb"] - a["rss_kb"]) * 1024 / max(c["log"] - a["log"], 1)
    return slope <= bound, (f"{a['n']} entries ({a['log']} bytes of log): peak RSS {a['rss_kb'] / 1024:.0f} MB -> "
                            f"{b['n']}: {b['rss_kb'] / 1024:.0f} MB -> {c['n']} ({c['log']} bytes): "
                            f"{c['rss_kb'] / 1024:.0f} MB: {slope:.1f} bytes of peak RSS per log byte (bound {bound})")


def sbm11_replay_time_row(rid):
    runs = [sbm11_open_run(n) for n in SBM11_OPEN_SIZES]
    a, b, c = runs
    us = (c["cpu"] - a["cpu"]) * 1e6 / (c["n"] - a["n"])
    ratio = c["cpu"] / max(a["cpu"], FLOOR)
    ok = us <= SBM11_REPLAY_US_BOUND and ratio <= SBM11_READ_TIME_BOUND
    return ok, (f"{a['n']} entries {a['cpu']:.2f} s CPU -> {b['n']} {b['cpu']:.2f} s -> {c['n']} {c['cpu']:.2f} s "
                f"(replay ms {a['replay_ms']:.0f}, {b['replay_ms']:.0f}, {c['replay_ms']:.0f}): {us:.1f} microseconds for each "
                f"entry (bound {SBM11_REPLAY_US_BOUND}), {c['cpu'] / max(a['cpu'], 1e-9):.1f} for 4x entries "
                f"(bound {SBM11_READ_TIME_BOUND})")


# Bounds, with the measurements (2026-10-14, this VM). The bound lies between the number of the code
# before the repair and the number after it, closer to the second.
#
# sbm11-update-memory (issue 857). Before the byte array encoder (commit e0679410): peak RSS 191, 355
# and 759 MB for 3.1, 6.3 and 12.7 MB of log: 62.5 bytes of peak RSS per log byte. After
# (`Storage/DeltaLogBytes.lean`): 31, 43 and 68 MB, 4.1 bytes per log byte; what is left is the
# solutions and the entries of the request, as Lean objects (about 300 bytes for each entry of 125
# bytes of log). The olympics update of the issue (203,264 entries, 35,919,852 bytes of log): peak
# RSS 2,310,880 kB before.
SBM11_UPDATE_MEMORY_BOUND = 8.0
# sbm11-open-log-memory (issue 851). Before: 244, 480 and 1010 MB for 3.1, 6.3 and 12.7 MB of log:
# 84.3 bytes per log byte. After the byte array reader: 35, 55 and 94 MB, 6.4 bytes per log byte;
# the rest is the overlay (the replayed rows in four sorted orders, and the terms that are new)
# and the entries of the log as Lean objects.
SBM11_OPEN_MEMORY_BOUND = 12.0
# sbm11-replay-time (issue 858). 258 to 295 microseconds for each entry before the repair of the
# replay (25,000 entries 6.4 to 7.3 s CPU, 100,000 entries 25.7 to 29.4 s). After the replay in
# dictionary order (`Dict.lookupWalkM`, `Harness/Sbm11Query.lean` `prefillBaseIds`) and sized hash sets:
# 0.45, 0.79 and 1.46 s CPU (the least of three runs) for 25,000, 50,000 and 100,000 entries, 13.5
# microseconds for each entry, 3.3 for 4x the entries; single runs of the same code read 0.53, 0.89 and
# 1.72 s (15.9 microseconds). What is left is the decode of the log (the payload of each entry is
# parsed from a list of its bytes, about 7 microseconds), the sort of the keys, the step of the overlay
# and the cut of the overlay into four permutations. The bound is the 1,000 ms for 40,000 entries of the
# issue (25 microseconds for each entry).
SBM11_REPLAY_US_BOUND = 25.0

# `l4sbm11-pack` over N-Triples text takes at most SBM11_PACK_RATIO times the CPU
# time of the same pack over the same triples as N-Quads text. N-Triples is read
# by the strict triple reader, N-Quads by the quad reader; both are line streams
# of the same lexical rules, so their costs agree. Before `lineFuel` replaced
# `r5.length + 1` in `readTriple12` the triple reader walked the rest of the chunk
# for every statement: phase 1 took 2,996 ms for 8.3 MB of N-Triples and 477 ms
# for the same quads as N-Quads (4 workers; 11,000 subjects of
# tests/sbm11/syntax/gen_multi.py; 2026-10-14). After: 272 ms and 328 ms.
SBM11_PACK_RATIO = 2.0
SBM11_PACK_RATIO_ROWS = {"sbm11-pack-nt-vs-nq": 100000}


def sbm11_pack_ratio_row(rid, runs):
    import shutil
    n = SBM11_PACK_RATIO_ROWS[rid]
    sbm11_need_pack_bin()
    nt = fixture(f"{rid}-{n}.nt", lambda: "".join(
        f"<{EX}s{i}> <{EX}p> <{EX}o{i}> .\n" for i in range(n)))
    nq = fixture(f"{rid}-{n}.nq", lambda: "".join(
        f"<{EX}s{i}> <{EX}p> <{EX}o{i}> <{EX}g> .\n" for i in range(n)))
    cpu = []
    for p in (nt, nq):
        out = FIX / f"{rid}-out"
        best = None
        for _ in range(runs):
            shutil.rmtree(out, ignore_errors=True)
            t = bl.run_once([str(SBM11_PACK_BIN), str(p), str(out)] + SBM11_PACK_ARGS, CAP)
            if t["status"] != "ok":
                shutil.rmtree(out, ignore_errors=True)
                raise MeasurementError(f"{rid}: {p.name}: exit status {t['status']}")
            best = t["cpu"] if best is None else min(best, t["cpu"])
        shutil.rmtree(out, ignore_errors=True)
        cpu.append(best)
    ok = cpu[0] <= SBM11_PACK_RATIO * max(cpu[1], FLOOR)
    return ok, (f"n={n}: N-Triples {cpu[0]:.3f} s CPU ({nt.stat().st_size} bytes), N-Quads "
                f"{cpu[1]:.3f} s CPU ({nq.stat().st_size} bytes): ratio "
                f"{cpu[0] / max(cpu[1], 1e-9):.2f} (bound {SBM11_PACK_RATIO})")


# Phase 1 of `l4sbm11-pack` cuts an N-Triples or N-Quads source into K byte
# ranges at line starts and reads them in K workers. A Turtle or TriG statement
# can start anywhere and depends on the prefixes, the base and the blank node
# scope of the text before it, so `Source.planRanges` gives one range and the
# pack prints `workers=1` whatever --workers says. The rows below pack a
# generated dataset of 1,500 subjects (tests/sbm11/syntax/gen_multi.py) with
# --workers 4 and require more than one worker.
SBM11_WORKERS_ROWS = {"sbm11-pack-ttl-workers": "multi.ttl",
                      "sbm11-pack-trig-workers": "multi.trig"}
GEN_MULTI = ROOT / "tests/sbm11/syntax/gen_multi.py"


def sbm11_workers_row(rid):
    import re
    import shutil
    name = SBM11_WORKERS_ROWS[rid]
    sbm11_need_pack_bin()
    n = 1500
    d = FIX / f"sbm11-multi-{n}"
    p = d / name
    if not p.exists():
        d.mkdir(parents=True, exist_ok=True)
        subprocess.run([sys.executable, str(GEN_MULTI), str(d), str(n)], check=True, timeout=CAP)
    out = FIX / f"{rid}-out"
    shutil.rmtree(out, ignore_errors=True)
    r = subprocess.run([str(SBM11_PACK_BIN), str(p), str(out), "--workers", "4"],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=CAP)
    shutil.rmtree(out, ignore_errors=True)
    text = r.stdout.decode("utf-8", "replace")
    if r.returncode != 0:
        raise MeasurementError(f"{rid}: {name}: exit {r.returncode}: {text[-200:]}")
    m = re.search(r"\bsource=\S+ format=\S+ source-bytes=\d+ workers=(\d+)", text)
    if not m:
        raise MeasurementError(f"{rid}: {name}: the pack printed no summary line with workers=")
    workers = int(m.group(1))
    return workers > 1, f"{name}: 4 workers requested, the pack read the source with {workers}"


SBM11_LOG_MEMORY_ROWS = {"sbm11-update-memory": sbm11_update_memory_row,
                         "sbm11-open-log-memory": sbm11_open_memory_row}
SBM11_LOG_TIME_ROWS = {"sbm11-replay-time": sbm11_replay_time_row}


def memory_row(rid):
    if rid in SBM11_LOG_MEMORY_ROWS:
        return SBM11_LOG_MEMORY_ROWS[rid](rid)
    if rid in SBM11_PACK_MEMORY_ROWS:
        return sbm11_pack_memory_row(rid)
    if rid in SBM11_EXPORT_MEMORY_ROWS:
        return sbm11_export_memory_row(rid)
    if rid in SBM11_DUMP_MEMORY_ROWS:
        return sbm11_dump_memory_row(rid)
    if rid in PACK_MEMORY_ROWS:
        return pack_memory_row(rid)
    if rid in PARSE_MEMORY_ROWS:
        x, make, extra, bound = PARSE_MEMORY_ROWS[rid]
        cmd_of = lambda p: [str(BIN), "parse", str(p)] + extra
    else:
        x, sparql, bound = MEMORY_ROWS[rid]
        make = bl.gene_slice
        cmd_of = lambda p: [str(BIN), "query", str(p), "--format", "turtle",
                            "--query-string", sparql]
    pts = []
    for n in (x, 4 * x):
        p = make(n)
        t = peak_rss_run(cmd_of(p))
        if t["status"] != "ok":
            return False, f"n={n}: exit status {t['status']}"
        pts.append((n, p.stat().st_size, t["rss_kb"]))
    (n1, b1, r1), (n4, b4, r4) = pts
    slope = (r4 - r1) * 1024 / max(b4 - b1, 1)
    ok = slope <= bound
    return ok, (f"n={n1} {r1 / 1024:.0f} MB ({b1} bytes) -> n={n4} {r4 / 1024:.0f} MB "
                f"({b4} bytes): {slope:.1f} bytes of peak RSS per input byte (bound {bound})")


# Rows measured at x, 2x and 4x (the n, 2n, 4n assertion of
# skills/danbri-function-precrime-checkers), in CPU time, minimum of the runs:
# time(2x) <= DOUBLING * time(x), time(4x) <= DOUBLING * time(2x), and
# time(4x) <= BOUND * max(time(x), FLOOR). A linear or n log n command gives
# about 2 per doubling; a quadratic one 4. The command must also print the
# expected first line.
DOUBLING = 3.0
CL_SOURCE = ROOT / "third_party/ontologies/cl-basic/cl-basic.owl"


def cl_prefix(n: int) -> Path:
    """The first n lines of the Cell Ontology basic edition as N-Triples:
    parsed by the Lean RDF/XML reader, one line per distinct triple, sorted
    by code point (the reproduction of issue 760, `sort -u` in the C locale)."""
    FIX.mkdir(parents=True, exist_ok=True)
    full = FIX / "cl-basic.sorted.nt"
    if not full.exists():
        r = subprocess.run([str(BIN), "parse", str(CL_SOURCE), "--format", "rdfxml",
                            "--out", "nquads"], stdout=subprocess.PIPE, timeout=CAP, check=True)
        lines = sorted({ln for ln in r.stdout.decode("utf-8").split("\n") if ln.strip()})
        full.write_text("\n".join(lines) + "\n", encoding="utf-8")
    p = FIX / f"cl-basic.{n}.nt"
    if not p.exists():
        with full.open(encoding="utf-8") as f:
            head = [next(f) for _ in range(n)]
        p.write_text("".join(head), encoding="utf-8")
    return p


def delta_log_merge_args(n: int) -> Path:
    """The arguments of `deltaLogMerge` (an empty base and a log of n
    records, each an INSERT DATA of one distinct triple), as a JSON file. The
    engine writes the records (`l4wasm-cli callseq` of `deltaLogEncode`); the
    file is written only after `deltaLogDecode` finds n batches and no torn
    record, so a fixture the engine does not read is an error, never a fast
    row."""
    import json
    FIX.mkdir(parents=True, exist_ok=True)
    p = FIX / f"delta-log-merge-{n}.json"
    if p.exists():
        return p
    seq = FIX / f"delta-log-merge-{n}.seq.json"
    seq.write_text(json.dumps([
        ["deltaLogEncode",
         [f'INSERT DATA {{ <{EX}s{i}> <{EX}p> "v{i}" . }}', str(i), "0"]]
        for i in range(n)]), encoding="utf-8")
    out = subprocess.run([str(WASMCLI_BIN), "callseq", str(seq)], stdout=subprocess.PIPE,
                         timeout=CAP, check=True).stdout.decode("utf-8")
    seq.unlink()
    records = [json.loads(line)["hex"] for line in out.splitlines() if line.strip()]
    log = "\n".join(records)
    check = FIX / f"delta-log-merge-{n}.decode.json"
    check.write_text(json.dumps([log]), encoding="utf-8")
    dec = json.loads(subprocess.run([str(WASMCLI_BIN), "call", "deltaLogDecode", str(check)],
                                    stdout=subprocess.PIPE, timeout=CAP, check=True).stdout)
    check.unlink()
    if len(records) != n or dec.get("batches") != n or dec.get("torn") is not False:
        raise RuntimeError(f"delta-log-merge fixture: {len(records)} records, "
                           f"decode {dec.get('batches')} batches, torn {dec.get('torn')}")
    p.write_text(json.dumps(["", log]), encoding="utf-8")
    return p


def pfx_triples(n: int) -> str:
    """n triples for n prefixes: the subject under namespace i, the object under namespace
    i + 1 (modulo n), the predicate under none (tests/stack/gen_cases.py writes the same)."""
    return "".join(f"<{EX}n{i}/s> <{EX}p> <{EX}n{(i + 1) % n}/o> .\n" for i in range(n))


def turtle_prefixes_args(n: int) -> Path:
    """The arguments of `serializeTurtleWith` for a table of n prefixes, every one used: the
    N-Quads text and the options `{"prefixes": {"n<i>": "http://example.org/n<i>/"}}`."""
    import json

    def text():
        opts = json.dumps({"prefixes": {f"n{i}": f"{EX}n{i}/" for i in range(n)}},
                          separators=(",", ":"))
        return json.dumps([pfx_triples(n), opts])
    return fixture(f"turtle-prefixes-{n}.json", text)


def turtle_prefixes_open_seq(n: int) -> Path:
    """A `callseq` file of one `datasetOpen` of a Turtle document with n `@prefix` lines and
    the triples of `pfx_triples`, in full IRIs (no prefixed name for the parser to look up)."""
    import json

    def text():
        ttl = "".join(f"@prefix n{i}: <{EX}n{i}/> .\n" for i in range(n)) + pfx_triples(n)
        return json.dumps([["datasetOpen", [ttl, "turtle", ""]]])
    return fixture(f"turtle-prefixes-open-{n}.seq.json", text)


def turtle_read_prefixes_ttl(n: int) -> Path:
    """A Turtle document with n `@prefix` lines and n triples whose three terms are prefixed
    names: the subject and the predicate under prefix i, the object under prefix i + 1
    (modulo n). The reader looks each name up in the table of the prefixes declared so far."""
    def text():
        return "".join(f"@prefix n{i}: <{EX}n{i}/> .\n" for i in range(n)) + "".join(
            f"n{i}:s n{i}:p n{(i + 1) % n}:o .\n" for i in range(n))
    return fixture(f"turtle-read-prefixes-{n}.ttl", text)


# row id -> (x, make input, command, expected first line (a string, or a
# predicate on the line, or on the line and the size n), a file the row needs or None[, the time to bound: "cpu"
# (user plus system, the default) or "user"]). A row that holds 100 MB to 500 MB
# bounds the user time: the system time of such a run, the page faults of the
# virtual machine, took from 0.03 s to 1.4 s for the same command (2026-10-15,
# turtle-prefixes-open at 64,000 prefixes), while the user time varied by 6 percent.
SERIES_ROWS = {
    "owl-consistent-cl": (
        10000, cl_prefix,
        lambda p: [str(BIN), "owl-consistent", str(p), "--format", "nquads"], "true",
        CL_SOURCE),
    "sparql-tokenize": (
        2000,
        lambda n: fixture(f"sparql-values-ask-{n}.rq", lambda: sparql_values_ask(n)),
        lambda p: [str(BIN), "query",
                   str(fixture("one-triple.nq", lambda: f"<{EX}s> <{EX}p> <{EX}o> .\n")),
                   "--query", str(p), "--format", "nquads"], "true", None),
    "delta-log-merge": (
        8000, delta_log_merge_args,
        lambda p: [str(WASMCLI_BIN), "call", "deltaLogMerge", str(p)],
        lambda line: line.startswith('{"ok":true,"nquads":"<' + EX + 's0> '),
        WASMCLI_BIN),
    # The Turtle writer with a table of n prefixes (issue 864). The first line is the
    # start of the JSON envelope: the first two `@prefix` lines of the table, in the
    # caller's order.
    "turtle-prefixes": (
        8000, turtle_prefixes_args,
        lambda p: [str(WASMCLI_BIN), "call", "serializeTurtleWith", str(p)],
        lambda line: line.startswith('{"ok":true,"turtle":"@prefix n0: <' + EX
                                     + 'n0/> .\\n@prefix n1: <' + EX + 'n1/> .\\n'),
        WASMCLI_BIN, "user"),
    "turtle-prefixes-open": (
        16000, turtle_prefixes_open_seq,
        lambda p: [str(WASMCLI_BIN), "callseq", str(p)],
        lambda line: line.startswith('{"ok":true,"handle":"h1","count":'),
        WASMCLI_BIN, "user"),
    # A triple term nested n deep, written as Turtle (issue 864). The harness compares
    # both writers with the text a loop builds and prints failures=0 when they agree.
    "turtle-nest-time": (
        25000, lambda n: n,
        lambda n: [str(SOURCE_CONVERT_BIN), "--nest-check", str(n)],
        lambda line: line.startswith("turtle-nest-check: depth=") and line.endswith("failures=0"),
        SOURCE_CONVERT_BIN),
    # The Turtle reader with n prefixes declared and a prefixed name looked up for each of
    # three terms in n triples (issue 865). `parse` prints the number of triples: n.
    "turtle-read-prefixes": (
        16000, turtle_read_prefixes_ttl,
        lambda p: [str(BIN), "parse", str(p), "--format", "turtle"],
        lambda line, n: line == str(n),
        None),
    # The OWL 2 RL closure of the same prefixes (semi-naive rounds since
    # 2026-10-13, https://github.com/danbri/factoidal/issues/756 item 2).
    # No first-line check: the output is the closure, one triple per line.
    "owlrl-closure-cl": (
        10000, cl_prefix,
        lambda p: [str(BIN), "closure", str(p), "--format", "nquads", "--regime", "owl-rl"],
        None, CL_SOURCE),
}


def first_ok(first, got, n):
    """The check of the first line a row prints: a string (equal), a function of the line, or
    a function of the line and the size n of the input."""
    if callable(first):
        return first(got, n) if first.__code__.co_argcount == 2 else first(got)
    return got == first


def doubling_check(pts, label):
    """The n, 2n, 4n assertion on three points [(n, seconds)]: each doubling at most DOUBLING
    times the time before it, and 4x at most BOUND times the first (FLOOR keeps timer noise from
    failing it). Returns (ok, the text that reports the three times and the ratios)."""
    (n1, t1), (n2, t2), (n4, t4) = pts
    r2, r4 = t2 / max(t1, 1e-9), t4 / max(t2, 1e-9)
    ok = (t2 <= DOUBLING * max(t1, FLOOR) and t4 <= DOUBLING * max(t2, FLOOR)
          and t4 <= BOUND * max(t1, FLOOR))
    return ok, (f"n={n1} {t1:.3f} s -> n={n2} {t2:.3f} s -> n={n4} {t4:.3f} s {label} "
                f"(ratios {r2:.1f} and {r4:.1f} per doubling, bound {DOUBLING}; "
                f"{t4 / max(t1, 1e-9):.1f} for 4x input, bound {BOUND})")


def series_row(rid, runs):
    x, make, cmd, first, needs = SERIES_ROWS[rid][:5]
    metric = SERIES_ROWS[rid][5] if len(SERIES_ROWS[rid]) > 5 else "cpu"
    label = "CPU" if metric == "cpu" else "user CPU"
    if needs is not None and not needs.exists():
        return False, f"{needs} missing"
    pts = []
    for n in (x, 2 * x, 4 * x):
        best = None
        try:
            arg = make(n)
        except Exception as e:  # a fixture that cannot be made fails the row
            return False, f"n={n}: fixture: {e}"
        for _ in range(runs):
            t = bl.run_once(cmd(arg), CAP)
            if t["status"] != "ok":
                return False, f"n={n}: exit status {t['status']}"
            got = t["first_line"].decode("utf-8", "replace") if isinstance(
                t["first_line"], bytes) else str(t["first_line"])
            if first is not None and not first_ok(first, got.strip(), n):
                return False, f"n={n}: printed {got.strip()[:120]!r}, not the expected answer"
            best = t[metric] if best is None else min(best, t[metric])
            if t["wall"] > REPEAT_LIMIT:
                break
        pts.append((n, best))
    return doubling_check(pts, label)


def startup_row():
    """Minimum CPU time (user + system) of `l4factoidal version`."""
    best = None
    for _ in range(15):
        t = bl.run_once([str(BIN), "version"], CAP)
        if t["status"] != "ok":
            return None, f"exit status {t['status']}"
        best = t["cpu"] if best is None else min(best, t["cpu"])
    return best, None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--only", default="")
    args = ap.parse_args()
    if not BIN.exists():
        print(f"lean_scaling: {BIN} not built (cd formal/lean4 && lake build l4factoidal)",
              file=sys.stderr)
        return 2
    names = [r for r in args.only.split(",") if r]
    rows = [r for r in names if r in ROWS] or ([] if names else list(ROWS))
    ratio_rows = [r for r in names if r in PARSE_RATIO_ROWS or r in SBM11_PACK_RATIO_ROWS
                  or r in SBM11_WORKERS_ROWS] or (
        [] if names else list(PARSE_RATIO_ROWS) + list(SBM11_PACK_RATIO_ROWS)
        + list(SBM11_WORKERS_ROWS))
    memory_rows = [r for r in names if r in MEMORY_ROWS or r in PARSE_MEMORY_ROWS
                   or r in PACK_MEMORY_ROWS or r in SBM11_PACK_MEMORY_ROWS
                   or r in SBM11_EXPORT_MEMORY_ROWS or r in SBM11_DUMP_MEMORY_ROWS
                   or r in SBM11_LOG_MEMORY_ROWS] or (
        [] if names else list(MEMORY_ROWS) + list(PARSE_MEMORY_ROWS) + list(PACK_MEMORY_ROWS)
        + list(SBM11_PACK_MEMORY_ROWS) + list(SBM11_EXPORT_MEMORY_ROWS)
        + list(SBM11_DUMP_MEMORY_ROWS) + list(SBM11_LOG_MEMORY_ROWS))
    series_rows = [r for r in names if r in SERIES_ROWS] or (
        [] if names else list(SERIES_ROWS))
    time_rows = [r for r in names if r in SBM11_READ_TIME_ROWS or r in MERKLE_RANGE_TIME_ROWS
                 or r in SBM11_LOG_TIME_ROWS or r in SBM11_PREFIX_TIME_ROWS] or (
        [] if names else list(SBM11_READ_TIME_ROWS) + list(MERKLE_RANGE_TIME_ROWS)
        + list(SBM11_LOG_TIME_ROWS) + list(SBM11_PREFIX_TIME_ROWS))
    run_startup = (not names) or ("startup" in names)
    passed = failed = xfailed = 0
    print(f"Lean scaling assertion: time(4x) <= {BOUND} * max(time(x), {FLOOR} s) "
          f"(rows in ROW_BOUND use their own bound); "
          f"minimum of {args.runs} runs; load average {os.getloadavg()[0]:.2f}")
    for rid in rows:
        x, make, cmd = ROWS[rid]
        issue = XFAIL.get(rid)
        t1, e1 = best_of(cmd(make(x)), args.runs)
        t4, e4 = best_of(cmd(make(4 * x)), args.runs)
        if e1 or e4:
            failed += 1
            print(f"  FAIL {rid}: cannot measure: n={x} -> n={4 * x}: {e1 or e4}")
            continue
        bound = ROW_BOUND.get(rid, BOUND)
        ok = t4 <= bound * max(t1, FLOOR)
        detail = (f"n={x} {t1:.3f} s -> n={4 * x} {t4:.3f} s "
                  f"(ratio {t4 / max(t1, 1e-9):.1f} for 4x input)")
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    for rid in ratio_rows:
        issue = XFAIL.get(rid)
        try:
            ok, detail = parse_ratio_row(rid, args.runs)
        except MeasurementError as e:
            failed += 1
            print(f"  FAIL {rid}: cannot measure: {e}")
            continue
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    for rid in memory_rows:
        issue = XFAIL.get(rid)
        try:
            ok, detail = memory_row(rid)
        except MeasurementError as e:
            failed += 1
            print(f"  FAIL {rid}: cannot measure: {e}")
            continue
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    for rid in time_rows:
        issue = XFAIL.get(rid)
        try:
            ok, detail = (merkle_range_time_row if rid in MERKLE_RANGE_TIME_ROWS
                          else SBM11_LOG_TIME_ROWS[rid] if rid in SBM11_LOG_TIME_ROWS
                          else SBM11_PREFIX_TIME_ROWS[rid] if rid in SBM11_PREFIX_TIME_ROWS
                          else sbm11_read_time_row)(rid)
        except MeasurementError as e:
            failed += 1
            print(f"  FAIL {rid}: cannot measure: {e}")
            continue
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    for rid in series_rows:
        issue = XFAIL.get(rid)
        ok, detail = series_row(rid, args.runs)
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    if run_startup:
        cpu, err = startup_row()
        if err:
            failed += 1
            print(f"  FAIL startup: {err}")
        else:
            ok = cpu <= STARTUP_BUDGET
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} startup: l4factoidal version {cpu * 1000:.1f} ms CPU "
                  f"(budget {STARTUP_BUDGET * 1000:.0f} ms)")
    print(f"scaling: {passed} pass, {failed} fail, {xfailed} expected-fail "
          f"(out of {passed + failed + xfailed})")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
