#!/usr/bin/env python3
"""Deterministic RDF with cross-subject links and an independent answer oracle.

This is a controlled synthetic corpus, not LUBM, BSBM or SP2Bench. Construction
formulas determine the exact result sequences; no SPARQL evaluator is used.
"""


def groups(subjects):
    return min(subjects, 100)


def person(ordinal):
    return f"urn:rel:person:{ordinal:08d}"


def org(ordinal):
    return f"urn:rel:org:{ordinal:03d}"


def triple_count(subjects):
    return 5 * subjects + (subjects + 6) // 7 + (subjects + 10) // 11 + groups(subjects)


def fixture_bytes(subjects):
    def lines():
        for i in range(subjects):
            s = f"<{person(i)}>"
            yield f'{s} <urn:rel:type> <urn:rel:Person> .\n'
            yield f'{s} <urn:rel:name> "person-{i:08d}" .\n'
            yield f'{s} <urn:rel:next> <{person((i + 1) % subjects)}> .\n'
            yield f'{s} <urn:rel:org> <{org(i % groups(subjects))}> .\n'
            yield f'{s} <urn:rel:score> "{i % 1000}"^^<http://www.w3.org/2001/XMLSchema#integer> .\n'
            if i % 7 == 0:
                yield f'{s} <urn:rel:alias> "alias Ω-{i:08d}" .\n'
            if i % 11 == 0:
                yield f'{s} <urn:rel:alternateOrg> <{org((i + 1) % groups(subjects))}> .\n'
        for i in range(groups(subjects)):
            yield f'<{org(i)}> <urn:rel:label> "org-{i:03d}" .\n'
    return ''.join(lines()).encode('utf-8')


def workloads(subjects):
    def uri(value):
        return {"type": "uri", "value": value}

    def literal(value):
        return {"type": "literal", "value": value}

    def row(i, **bindings):
        return {"subject": uri(person(i)), **bindings}

    def select(name, query, variables, bindings):
        return {"name": name, "query": query,
                "expected": {"head": {"vars": variables}, "results": {"bindings": bindings}}}

    next_link = '?subject <urn:rel:next> ?next'
    final_name = '?next <urn:rel:name> ?name'
    values = list(range(0, subjects, max(1, subjects // 50)))[:50]
    # The descending key is the negative score, with ascending subject ties.
    numeric = sorted((i for i in range(subjects) if i % 1000 >= 950), key=lambda i: (-(i % 1000), i))[:25]
    return [
        select('chain-two', f'SELECT ?subject ?name WHERE {{ {next_link} . {final_name} }} ORDER BY ?subject',
               ['subject', 'name'], [row(i, name=literal(f'person-{(i + 1) % subjects:08d}')) for i in range(subjects)]),
        select('chain-three', 'SELECT ?subject ?name WHERE { ' + next_link +
               ' . ?next <urn:rel:next> ?last . ?last <urn:rel:name> ?name } ORDER BY ?subject',
               ['subject', 'name'], [row(i, name=literal(f'person-{(i + 2) % subjects:08d}')) for i in range(subjects)]),
        select('dimension-join', 'SELECT ?subject ?label WHERE { ?subject <urn:rel:org> ?org . '
               '?org <urn:rel:label> ?label } ORDER BY ?subject', ['subject', 'label'],
               [row(i, label=literal(f'org-{i % groups(subjects):03d}')) for i in range(subjects)]),
        select('selective-chain', f'SELECT ?subject ?name WHERE {{ ?subject <urn:rel:org> <{org(0)}> . '
               + next_link + ' . ' + final_name + ' } ORDER BY ?subject', ['subject', 'name'],
               [row(i, name=literal(f'person-{(i + 1) % subjects:08d}')) for i in range(0, subjects, groups(subjects))]),
        select('optional-alias', 'SELECT ?subject ?name ?alias WHERE { ?subject <urn:rel:name> ?name '
               'OPTIONAL { ?subject <urn:rel:alias> ?alias } } ORDER BY ?subject LIMIT 25',
               ['subject', 'name', 'alias'], [row(i, name=literal(f'person-{i:08d}'),
                   **({'alias': literal(f'alias Ω-{i:08d}')} if i % 7 == 0 else {}))
                   for i in range(min(subjects, 25))]),
        select('union-distinct', 'SELECT DISTINCT ?org WHERE { { ?subject <urn:rel:org> ?org } '
               'UNION { ?other <urn:rel:alternateOrg> ?org } } ORDER BY ?org', ['org'],
               [{'org': uri(org(i))} for i in range(groups(subjects))]),
        select('group-count-string', 'SELECT ?org (STR(COUNT(?subject)) AS ?count) WHERE { '
               '?subject <urn:rel:org> ?org } GROUP BY ?org ORDER BY ?org', ['org', 'count'],
               [{'org': uri(org(i)), 'count': literal(str(len(range(i, subjects, groups(subjects)))))}
                for i in range(groups(subjects))]),
        select('numeric-top', 'SELECT ?subject WHERE { ?subject <urn:rel:score> ?score '
               'FILTER(?score >= 950) } ORDER BY DESC(?score) ?subject LIMIT 25', ['subject'],
               [row(i) for i in numeric]),
        select('values-chain', 'SELECT ?subject ?name WHERE { VALUES ?subject { '
               + ' '.join(f'<{person(i)}>' for i in values) + ' } ' + next_link + ' . '
               + final_name + ' } ORDER BY ?subject', ['subject', 'name'],
               [row(i, name=literal(f'person-{(i + 1) % subjects:08d}')) for i in values]),
    ]
