# MLP first 100 queries: parser and original rewriter

Run on 24 November 2026 using the first 100 template records in the checked-in
Martin Poulter corpus; they are ordered, not a random sample. The query text is
unexpanded wikitext template content; it is not necessarily the query sent by
the Wikidata UI. We used the Factoidal Lean WDQS-prefix parser (SPARQL 1.1) and
Wikimedia's checked-in executable JAR from checkout
`e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74`. The JAR SHA-256 is
`cc152896c4a5ae0111cae415136aa4ef4bab322ac591571b1e5def6cdbeb9e48`;
the checked-in binary was not independently built from the checkout.

| Measure | Result |
|---|---:|
| Inputs | 100 |
| Lean input accepted | 99 |
| Lean input rejected | 1 |
| Java rewriter: rewritten | 80 |
| Java rewriter: unchanged | 16 |
| Java rewriter: parse_error | 4 |
| Returned query strings accepted by Lean | 96 / 96 |

80 results include a label-service rewrite; two include an isSomeValue rewrite
(some results include more than one rule). 79 responses carry the upstream
warning about `[AUTO_LANGUAGE]` being passed through literally. The Lean parser
accepted three inputs for which the original rewriter returned parse_error;
no conclusion about which is correct is implied. Both rejected record 88, whose
source contains unexpanded `{{!}}{{!}}` wiki markup. Page headings, statuses,
warnings, errors, rule IDs, and revision links appear in the companion JSON.

Lean currently does not implement the Wikimedia rewrite rules, an equivalent
output printer, or a general execution comparison. This run does not compare
rewritten text between implementations, execute queries, compare result sets,
or establish semantic equivalence, correctness, or performance. Parse success
is not proof that WDQS accepts the query, or that the rewriter preserves its
results. In particular, upstream explicitly warns about `[AUTO_LANGUAGE]`.

Reproduce with a compatible `lake` in PATH and a local original JAR:

```
python3 tools/wikidata/compare_mlp.py --count 100 --jar /path/to/sparql-rewriter.jar --out /tmp/mlp-comparison.json
```

The runner records corpus and JAR hashes, verifies response IDs and source-query
hashes, and feeds all returned query strings back through the Lean parser. It
does not send queries over a network. The sample is not intended as a broad
conformance statistic.
