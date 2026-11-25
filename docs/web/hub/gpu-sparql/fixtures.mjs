// Original demonstration data. This produces RDF source text only; the
// shipping engine parses it, plans every join and evaluates every query.
export function sampleDataset(people = 2048) {
  if (![64, 2048, 8192].includes(people)) throw new RangeError('Choose a listed sample size.');
  const lines = ['@prefix ex: <https://example.org/gpu/> .'];
  for (let project = 0; project < 8; project++)
    lines.push(`ex:project${project} ex:title "Project ${project + 1}" .`);
  for (let i = 0; i < people; i++) {
    const person = `ex:person${String(i).padStart(5, '0')}`;
    lines.push(`${person} ex:project ex:project${i % 8} ; ex:name "Person ${i + 1}" .`);
    if (i % 4 === 0) lines.push(`${person} ex:region "North" .`);
  }
  return lines.join('\n');
}

export const queries = {
  people: {
    label: 'People and projects · join + OPTIONAL',
    text: `PREFIX ex: <https://example.org/gpu/>
SELECT ?person ?name ?project ?region
WHERE {
  ?person ex:project ?project .
  ?person ex:name ?name .
  OPTIONAL { ?person ex:region ?region }
}
ORDER BY ?person
LIMIT 50`
  },
  counts: {
    label: 'Project totals · join + GROUP BY',
    text: `PREFIX ex: <https://example.org/gpu/>
SELECT ?project (COUNT(?person) AS ?members)
WHERE {
  ?person ex:project ?project .
  ?person ex:name ?name .
}
GROUP BY ?project
ORDER BY ?project`
  },
  bag: {
    label: 'Repeated project bindings · result bag',
    text: `PREFIX ex: <https://example.org/gpu/>
SELECT ?project
WHERE {
  ?person ex:project ?project .
  ?person ex:name ?name .
}
ORDER BY ?project`
  },
  construct: {
    label: 'Project memberships · CONSTRUCT',
    text: `PREFIX ex: <https://example.org/gpu/>
CONSTRUCT { ?project ex:member ?person }
WHERE {
  ?person ex:project ?project .
  ?person ex:name ?name .
}
ORDER BY ?person
LIMIT 50`
  },
  ask: {
    label: 'Any named project members? · ASK',
    text: `PREFIX ex: <https://example.org/gpu/>
ASK {
  ?person ex:project ?project .
  ?person ex:name ?name .
}`
  }
};
