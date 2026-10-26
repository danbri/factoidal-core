// @factoidal/core/sample-store - a small store made on demand (Node only).
//
// Owner, 2026-10-20, verbatim: "All the CLIs are still bundled i just didn't
// want any actual demo triples cluttering the file." So the package ships no
// store. sampleStorePath() packs the few triples below (written for this
// package, no third-party content) into a Shardborough store with the
// package's own `factoidal pack` and `factoidal activate`, under DIR or the
// OS temporary directory, and returns the collection root. A DIR that
// already holds CURRENT is returned as it is.

import { execFileSync } from 'node:child_process'
import { existsSync } from 'node:fs'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'

/** The triples of the sample store, as Turtle. */
export const SAMPLE_TURTLE = `@prefix skos: <http://www.w3.org/2004/02/skos/core#> .
@prefix ex: <http://example.org/codec/> .
ex:scheme a skos:ConceptScheme ; skos:prefLabel "Video codecs"@en .
ex:c1 a skos:Concept ; skos:inScheme ex:scheme ; skos:prefLabel "PAL"@en ; skos:notation "c1" .
ex:c2 a skos:Concept ; skos:inScheme ex:scheme ; skos:prefLabel "NTSC"@en ; skos:notation "c2" .
ex:c3 a skos:Concept ; skos:inScheme ex:scheme ; skos:prefLabel "SECAM"@en ; skos:notation "c3" ;
  skos:broader ex:c1 .
`

/** What the sample store holds. */
export const sampleStoreFacts = Object.freeze({
  triples: 15,
  source: 'SAMPLE_TURTLE in sample-store.mjs (written for this package)',
  layout: 'ibk5'
})

/**
 * Pack the sample store (if DIR holds no CURRENT) and return its root.
 * @param {string} [dir] the collection root to use; default a new
 *   directory under the OS temporary directory
 * @returns {string}
 */
export function sampleStorePath (dir) {
  if (typeof dir === 'string' && existsSync(join(dir, 'CURRENT'))) return dir
  const cli = fileURLToPath(new URL('./bin/factoidal.mjs', import.meta.url))
  const args = [cli, 'sample-store']
  if (typeof dir === 'string') args.push(dir)
  return execFileSync(process.execPath, args, { encoding: 'utf8' }).trim()
}

export default sampleStorePath
