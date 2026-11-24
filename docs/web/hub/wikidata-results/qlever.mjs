export const qleverUrl = 'https://query-next.wikidata.org/sparql';
export const batchSize = 5;

const rdfTypes = new Set(['application/n-triples', 'text/turtle', 'application/rdf+xml',
  'application/n-quads', 'application/trig', 'text/plain']);

export async function queryQlever(query, { signal, fetchResult = fetch } = {}) {
  const encoded = new URLSearchParams({ query });
  const get = encoded.toString().length < 7000;
  const response = await fetchResult(get ? `${qleverUrl}?${encoded}` : qleverUrl, {
    method: get ? 'GET' : 'POST',
    body: get ? undefined : encoded,
    headers: { Accept: 'application/sparql-results+json, application/n-triples;q=0.9, text/turtle;q=0.8, application/rdf+xml;q=0.5' },
    signal,
  });
  if (!response.ok) {
    const detail = (await response.text()).trim().slice(0, 320);
    const error = new Error(`HTTP ${response.status}${detail ? `. ${detail}` : ''}`);
    error.status = response.status;
    throw error;
  }
  const contentType = response.headers.get('content-type')?.split(';')[0]?.trim().toLowerCase();
  if (contentType?.endsWith('json')) {
    const data = await response.json();
    if (typeof data.boolean === 'boolean') return { kind: 'ask', data };
    if (Array.isArray(data.head?.vars) && Array.isArray(data.results?.bindings)) return { kind: 'select', data };
    throw new Error('The response is missing SPARQL result bindings.');
  }
  if (rdfTypes.has(contentType)) return { kind: 'rdf', data: await response.text(), contentType };
  throw new Error(`Unexpected media type ${contentType ?? 'unknown'}.`);
}

// The caller supplies distinct queries. Await each result before starting the
// next and stop on backpressure, leaving the remaining entries available.
export async function runBatch(entries, run, pause = () => new Promise(resolve => setTimeout(resolve, 450))) {
  for (const [index, entry] of entries.slice(0, batchSize).entries()) {
    if (index > 0) await pause();
    if (await run(entry) === false) break;
  }
}
