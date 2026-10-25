// An LWS storage as an RDF dataset: one named graph per RDF resource, the
// containment in the default graph, and the entity tag of every resource
// read (https://github.com/danbri/factoidal/issues/1011).
// Design record: docs/designissues/2026-10-25-lws-dataset-view.md
//
// WHAT THIS FILE IS ALLOWED TO DO
// Loop. Start at the storage root; ask the LWS client (lws/client.mjs) to
// list a container; give the engine the listing (op lwsViewPlan), which
// answers which members to list and which to read; read those with the
// client; give the engine every listing and read (op lwsDatasetView), which
// answers the dataset as N-Quads with the evidence; open that text as a
// Dataset. Every decision is Lean: which members are containers and which
// media types have an RDF reader (L4Factoidal/LWS/DatasetViewRead.lean), the
// entity tag and the graph of each read, and the view itself
// (L4Factoidal/LWS/DatasetView.lean). This file reads no header and chooses
// no media type.
//
// Limits (stated in API.md): a full crawl on every open; no search index;
// no caching; metadata resources are not crawled; the snapshot is a sequence
// of GETs, not one read of the storage.

import { loadEngine } from '../bin/engine.mjs'
import { parse } from '../index.mjs'
import { createLwsClient, LwsClientError } from './client.mjs'
import { FactoidalError } from '../lib/errors.mjs'

/** The engine ops this host needs, beyond the client's. */
export const LWS_DATASET_OPS = ['lwsViewPlan', 'lwsDatasetView']

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Whether the loaded engine carries the dataset-view ops.
 *
 * @param {object} engine the handle from `loadEngine()`
 * @returns {Promise<{available: boolean, reason: string}>}
 */
export async function lwsDatasetOpsAvailable (engine) {
  try {
    engine.call('lwsViewPlan', ['{}'])
    return { available: true, reason: 'lwsViewPlan answered' }
  } catch (error) {
    if (isUnknownOp(error)) {
      return {
        available: false,
        reason: 'the loaded l4factoidal WebAssembly module does not carry lwsViewPlan ' +
          '(rebuild formal/lean4/Wasm)'
      }
    }
    return { available: true, reason: 'lwsViewPlan answered with an engine error' }
  }
}

/**
 * Crawl an LWS storage and open it as a Dataset.
 *
 * @param {string} storageRootUrl the URL of the storage root container
 * @param {object} [options]
 * @param {Function} [options.fetch] the fetch to use (default `globalThis.fetch`)
 * @param {object} [options.auth] passed to `createLwsClient`:
 *   `{ subjectToken, subjectTokenType }`, `{ selfIssued }` or `{ session }`
 * @param {object} [options.engine] an engine handle to reuse
 * @param {number} [options.maxContainers] stop with an error after listing
 *   this many containers (default 10000)
 * @returns {Promise<object>} `{ dataset, evidence, skipped, graphs,
 *   query(sparql, options), dispose() }`
 */
export async function openLwsDataset (storageRootUrl, options = {}) {
  if (typeof storageRootUrl !== 'string') {
    throw new TypeError('openLwsDataset: storageRootUrl must be a string')
  }
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const probe = await lwsDatasetOpsAvailable(engine)
  if (!probe.available) {
    throw new FactoidalError(`openLwsDataset: ${probe.reason}`, { code: 'op.unknown' })
  }
  const auth = options.auth !== undefined && options.auth !== null ? options.auth : {}
  const client = await createLwsClient({ ...auth, engine, fetch: options.fetch })
  const maxContainers = typeof options.maxContainers === 'number' ? options.maxContainers : 10000

  const queue = [storageRootUrl]
  const listed = new Set()
  const listings = []
  const reads = []
  const skipped = []
  while (queue.length > 0) {
    const container = queue.shift()
    if (listed.has(container)) continue
    if (listed.size >= maxContainers) {
      throw new FactoidalError(`openLwsDataset: more than ${maxContainers} containers`,
        { code: 'lws.dataset.limit' })
    }
    listed.add(container)
    const done = await client.list(container)
    listings.push({ container, done })
    const plan = engine.call('lwsViewPlan', [JSON.stringify(done)])
    for (const c of plan.containers) queue.push(c)
    for (const s of plan.skipped) skipped.push(s)
    for (const resource of plan.resources) {
      try {
        reads.push({ resource, done: await client.read(resource) })
      } catch (error) {
        if (!(error instanceof LwsClientError)) throw error
        skipped.push({ resource, reason: `read: ${error.reason}` })
      }
    }
  }

  const view = engine.call('lwsDatasetView', [JSON.stringify({ listings, reads })])
  for (const s of view.skipped) skipped.push(s)
  const dataset = await parse(view.nquads, { format: 'nquads' })
  const evidence = view.evidence.map((e) => ({
    resource: e.resource, etag: e.etag, lastModified: e.lastModified
  }))

  return {
    dataset,
    /** Each RDF resource read: `{ resource, etag, lastModified }`. */
    evidence,
    /** Each member or read left out of the dataset: `{ resource, reason }`. */
    skipped,
    /** The number of named graphs (RDF resources). */
    graphs: view.graphs,
    /**
     * Run a SPARQL query over the dataset.
     * @returns {Promise<{result: *, evidence: Array<object>}>} `result` as
     *   `Dataset.query` answers; `evidence` the resources read
     */
    async query (sparql, queryOptions) {
      return { result: await dataset.query(sparql, queryOptions), evidence: evidence.slice() }
    },
    dispose () { dataset.dispose() }
  }
}
