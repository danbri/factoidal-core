#!/usr/bin/env python3
"""Write the deterministic benchmark inputs of the wasm component experiments:
bench/data/people-<n>.ttl (a Turtle document of n people, about 6 triples
each: prefixes, `;` lists, typed and language-tagged literals) and
bench/data/q1.rq (a SPARQL 1.1 join with FILTER, ORDER BY and LIMIT).
Usage: gen-data.py <n> [<n> ...]"""
import os, sys
here = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')
os.makedirs(here, exist_ok=True)
for n in map(int, sys.argv[1:] or ['2000']):
    lines = ['@prefix ex: <http://example.org/> .',
             '@prefix foaf: <http://xmlns.com/foaf/0.1/> .',
             '@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .', '']
    for i in range(n):
        lines.append(f'ex:p{i} a foaf:Person ;\n'
                     f'  foaf:name "Person {i}"@en ;\n'
                     f'  foaf:age "{18 + i % 60}"^^xsd:integer ;\n'
                     f'  foaf:knows ex:p{(i * 7 + 1) % n} , ex:p{(i * 13 + 5) % n} ;\n'
                     f'  ex:score {i % 97}.5 .')
    open(os.path.join(here, f'people-{n}.ttl'), 'w').write('\n'.join(lines) + '\n')
open(os.path.join(here, 'q1.rq'), 'w').write('''PREFIX foaf: <http://xmlns.com/foaf/0.1/>
SELECT ?a ?bn WHERE {
  ?a foaf:knows ?b ; foaf:age ?age .
  ?b foaf:name ?bn .
  FILTER(?age > 70)
} ORDER BY ?bn LIMIT 20
''')
