// Application storage orchestration. RDF parsing/querying and every LWS HTTP,
// authentication, redirect, listing, precondition and conflict decision remain
// in the public Lean-backed APIs. This module never persists a client/session.
export const KNOWN_PODS_KEY = 'factoidal.compositor.known-pods.v1';
const PIM = 'http://www.w3.org/ns/pim/space#';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const ROOT_QUERY = `SELECT ?subject ?predicate ?root WHERE {
  { ?subject <${PIM}storage> ?root . BIND(<${PIM}storage> AS ?predicate) }
  UNION
  { ?root <${RDF_TYPE}> <${PIM}Storage> . BIND(?root AS ?subject) BIND(<${RDF_TYPE}> AS ?predicate) }
  FILTER(isIRI(?root))
}`;

function httpUrl(value) {
  if (typeof value !== 'string' || !value || value.trim() !== value || /[\\\u0000-\u0020]/u.test(value))
    throw new TypeError('Expected an absolute HTTP(S) URL without whitespace or backslashes.');
  const parsed = new URL(value);
  if (!['https:', 'http:'].includes(parsed.protocol) || parsed.username || parsed.password || parsed.search || parsed.hash)
    throw new TypeError('HTTP(S) URLs must not contain credentials, a query, or a fragment.');
  // Refuse URL-parser repairs and ambiguous path encodings, rather than allow
  // a target to acquire a different identity during request construction.
  if (parsed.href !== value || /%(?:2f|5c|2e|25)/iu.test(parsed.pathname))
    throw new TypeError('Use a canonical URL without dot segments or encoded path separators.');
  return parsed;
}
function rootUrl(value) {
  const parsed = httpUrl(value);
  if (!parsed.pathname.endsWith('/')) throw new TypeError('A pod root must end with /.');
  return parsed.href;
}
function within(root, value) {
  const target = httpUrl(value);
  if (target.origin !== new URL(root).origin || !target.href.startsWith(root))
    throw new TypeError('The resource must be inside the selected pod root.');
  return target.href;
}
function readText(result) {
  if (typeof result?.body === 'string') return result.body;
  if (typeof result?.report?.body?.text === 'string') return result.report.body.text;
  // An empty body has no top-level body in the LWS result envelope.
  if (result?.body === undefined && result?.bodyBase64 === undefined && result?.report?.body?.base64 === '') return '';
  throw new TypeError('The LWS client did not return a UTF-8 text representation.');
}
function etagOf(result) {
  const tag = result?.report?.metadata?.etag ?? result?.report?.etag;
  return typeof tag === 'string' && tag ? tag : null;
}
function termText(term) {
  return term?.termType === 'BlankNode' ? '_:' + term.value : term?.value;
}

/** Discover only storage declarations present in this exact bootstrap graph.
 * No recursive profile/seeAlso traversal or implicit same-origin root guessing.
 * Discovery is provenance, not authorization or a storage conformance verdict. */
export async function discoverPods({ core, client, bootstrapUrl }) {
  const source = httpUrl(bootstrapUrl).href;
  const fetched = await client.read(source, { accept: 'text/turtle' });
  const dataset = await core.parse(readText(fetched), { format: 'turtle', baseIRI: source });
  try {
    const rows = await core.query(dataset, ROOT_QUERY);
    const roots = [], rejected = [], seen = new Set();
    for (const row of rows) {
      const root = row.get('root');
      if (root?.termType !== 'NamedNode') continue;
      const declaration = { url: root.value, bootstrapUrl: source,
        subject: termText(row.get('subject')), predicate: termText(row.get('predicate')) };
      try {
        declaration.url = rootUrl(declaration.url);
        const key = JSON.stringify(declaration);
        if (!seen.has(key)) { seen.add(key); roots.push(Object.freeze(declaration)); }
      } catch (error) { rejected.push({ ...declaration, message: error.message }); }
    }
    return { bootstrapUrl: source, roots, rejected };
  } finally { dataset.dispose(); }
}

function metadata(value) {
  if (!value || typeof value.subject !== 'string' || !value.subject ||
      ![PIM + 'storage', RDF_TYPE].includes(value.predicate)) throw new TypeError('Invalid pod provenance.');
  return { url: rootUrl(value.url), bootstrapUrl: httpUrl(value.bootstrapUrl).href,
    subject: value.subject, predicate: value.predicate };
}
/** Persist allowlisted discovery metadata only, never arbitrary input fields. */
export function rememberPods(discovery, storage = globalThis.localStorage) {
  const merged = new Map(loadKnownPods(storage).map(pod => [JSON.stringify(pod), pod]));
  for (const value of discovery.roots) { const pod = metadata(value); merged.set(JSON.stringify(pod), pod); }
  const pods = [...merged.values()];
  if (pods.length > 100) throw new TypeError('At most 100 pod declarations can be remembered.');
  storage.setItem(KNOWN_PODS_KEY, JSON.stringify(pods));
  return pods;
}
/** Stored metadata is untrusted and must be revalidated before a write. */
export function loadKnownPods(storage = globalThis.localStorage) {
  try {
    const parsed = JSON.parse(storage.getItem(KNOWN_PODS_KEY) ?? '[]');
    if (!Array.isArray(parsed) || parsed.length > 100) return [];
    return parsed.flatMap(value => { try { return [metadata(value)]; } catch { return []; } });
  } catch { return []; }
}
export async function revalidateKnownPod({ core, client, pod }) {
  const expected = metadata(pod);
  const discovery = await discoverPods({ core, client, bootstrapUrl: expected.bootstrapUrl });
  const current = discovery.roots.find(root => root.url === expected.url &&
    root.subject === expected.subject && root.predicate === expected.predicate);
  if (!current) throw new Error('The bootstrap no longer declares this pod; discover it again before saving.');
  return current;
}

/** Explicit caller-supplied client owns transient credentials. A remembered
 * root carries provenance and is re-read before every write. A string root
 * is a directly selected target, not a claim of discovered provenance. */
export function createPodStorage({ core, client, root }) {
  const pod = typeof root === 'string' ? null : metadata(root);
  const base = rootUrl(pod?.url ?? root);
  return Object.freeze({
    root: base,
    async list(containerUrl = base) {
      const container = within(base, containerUrl);
      const result = await client.list(container);
      // Do not expose an out-of-root member as an actionable editor target.
      const items = result?.report?.items;
      if (!Array.isArray(items)) throw new TypeError('The LWS client did not return a container listing.');
      return { items: items.map(item => ({ ...item, id: within(base, item.id) })), result };
    },
    async load(url) {
      const target = within(base, url);
      const result = await client.read(target, { accept: 'application/json' });
      return { url: target, text: readText(result), etag: etagOf(result) };
    },
    async save(url, text, { etag, create = false } = {}) {
      const target = within(base, url);
      if (typeof text !== 'string') throw new TypeError('Pipeline content must be text.');
      if (typeof create !== 'boolean') throw new TypeError('create must be a boolean.');
      if (create && etag !== undefined && etag !== null) throw new TypeError('Create must not supply an update ETag.');
      if (!create && (typeof etag !== 'string' || !etag.trim()))
        throw new TypeError('Updating requires the exact ETag returned when this pipeline was loaded.');
      if (pod) await revalidateKnownPod({ core, client, pod });
      const result = await client.update(target, { body: text, mediaType: 'application/json',
        precondition: create ? 'ifNoneMatchStar' : 'ifMatch', ...(create ? {} : { tag: etag }), retry412: 0 });
      return { url: target, etag: etagOf(result), result };
    },
  });
}

/** One editor-chosen filename below a selected root, never an arbitrary URL. */
export function rootedPath(root, filename) {
  const base = rootUrl(typeof root === 'string' ? root : root.url);
  if (typeof filename !== 'string' || !filename || filename.trim() !== filename ||
      filename === '.' || filename === '..' || /[/%\\?#\u0000-\u001f\u007f]/u.test(filename))
    throw new TypeError('Choose one filename without path separators, escapes, or control characters.');
  return within(base, base + encodeURIComponent(filename));
}
