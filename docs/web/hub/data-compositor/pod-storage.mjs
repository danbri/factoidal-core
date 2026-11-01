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

/** The engine's URL decisions for one pod (op containerPath,
 * formal/lean4/L4Factoidal/LWS/ContainerPath.lean). A refusal becomes a
 * TypeError here; no URL is parsed or compared in JavaScript. An engine
 * without the op refuses every pod operation. */
export async function podPaths(core) {
  const engine = await core.loadEngine();
  const ops = engine.call('ops', []).ops ?? [];
  if (!ops.includes('containerPath'))
    throw new TypeError('This engine has no containerPath op; pod storage needs @factoidal/core with containerPath (Lean URL checks).');
  const decide = (request, message) => {
    const r = engine.call('containerPath', [JSON.stringify(request)]);
    if (!r.allowed) throw new TypeError(message ? `${message} (${r.reason})` : `${r.reason}.`);
    return r.url;
  };
  return Object.freeze({
    /** An absolute HTTP(S) URL in canonical form (a bootstrap profile). */
    http: value => decide({ kind: 'target', url: value, canonical: true }, 'Expected a canonical absolute HTTP(S) URL without credentials, a query, or a fragment'),
    /** A pod root: canonical, ending with /. */
    root: value => decide({ kind: 'container', url: value, canonical: true }, 'A pod root must be a canonical HTTP(S) URL ending with /'),
    /** A URL inside the root, at a path-segment boundary (theorem within_canonical_under). */
    within: (root, value) => decide({ kind: 'within', root, url: value, canonical: true }, 'The resource must be inside the selected pod root'),
    /** One new filename inside a folder of the root (theorem segmentIn_under). */
    segment: (root, name) => decide({ kind: 'segment', root, name }, 'Choose one filename without path separators, escapes, or control characters'),
    /** The folder above `folder`, never above the root (theorem parentIn_under). */
    parent: (root, folder) => decide({ kind: 'parent', root, folder }, 'The folder must be inside the selected pod root'),
  });
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
  const paths = await podPaths(core);
  const source = paths.http(bootstrapUrl);
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
        declaration.url = paths.root(declaration.url);
        const key = JSON.stringify(declaration);
        if (!seen.has(key)) { seen.add(key); roots.push(Object.freeze(declaration)); }
      } catch (error) { rejected.push({ ...declaration, message: error.message }); }
    }
    return { bootstrapUrl: source, roots, rejected };
  } finally { dataset.dispose(); }
}

// The fields of a remembered pod, copied by name. Their URLs are decided by
// the engine (podPaths) in the storage worker before any request; the page
// that remembers them has no engine and makes no URL decision.
function metadata(value) {
  if (!value || typeof value.subject !== 'string' || !value.subject ||
      typeof value.url !== 'string' || typeof value.bootstrapUrl !== 'string' ||
      ![PIM + 'storage', RDF_TYPE].includes(value.predicate)) throw new TypeError('Invalid pod provenance.');
  return { url: value.url, bootstrapUrl: value.bootstrapUrl,
    subject: value.subject, predicate: value.predicate };
}
function checkedMetadata(paths, value) {
  const pod = metadata(value);
  return { ...pod, url: paths.root(pod.url), bootstrapUrl: paths.http(pod.bootstrapUrl) };
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
  const expected = checkedMetadata(await podPaths(core), pod);
  const discovery = await discoverPods({ core, client, bootstrapUrl: expected.bootstrapUrl });
  const current = discovery.roots.find(root => root.url === expected.url &&
    root.subject === expected.subject && root.predicate === expected.predicate);
  if (!current) throw new Error('The bootstrap no longer declares this pod; discover it again before saving.');
  return current;
}

/** Explicit caller-supplied client owns transient credentials. A remembered
 * root carries provenance and is re-read before every write. A string root
 * is a directly selected target, not a claim of discovered provenance. */
export function createPodStorage({ core, paths, client, root }) {
  const pod = typeof root === 'string' ? null : checkedMetadata(paths, root);
  const base = paths.root(pod?.url ?? root);
  const within = paths.within;
  return Object.freeze({
    root: base,
    /** One new filename inside `folder` (a folder of this root). */
    rooted(folder, filename) { return within(base, paths.segment(within(base, folder), filename)); },
    /** The folder above `folder` inside this root. */
    parent(folder) { return paths.parent(base, folder); },
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
export function rootedPath(paths, root, filename) {
  const base = paths.root(typeof root === 'string' ? root : root.url);
  return paths.within(base, paths.segment(base, filename));
}
