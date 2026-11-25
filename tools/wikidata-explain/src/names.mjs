// Turn IRIs into readable names, using the dated label cache.
import fs from 'node:fs';

export const PREFIXES = {
  wd: 'http://www.wikidata.org/entity/',
  wdt: 'http://www.wikidata.org/prop/direct/',
  wdtn: 'http://www.wikidata.org/prop/direct-normalized/',
  p: 'http://www.wikidata.org/prop/',
  ps: 'http://www.wikidata.org/prop/statement/',
  psv: 'http://www.wikidata.org/prop/statement/value/',
  pq: 'http://www.wikidata.org/prop/qualifier/',
  pqv: 'http://www.wikidata.org/prop/qualifier/value/',
  pr: 'http://www.wikidata.org/prop/reference/',
  wdno: 'http://www.wikidata.org/prop/novalue/',
  wikibase: 'http://wikiba.se/ontology#',
  rdfs: 'http://www.w3.org/2000/01/rdf-schema#',
  rdf: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
  skos: 'http://www.w3.org/2004/02/skos/core#',
  schema: 'http://schema.org/',
  owl: 'http://www.w3.org/2002/07/owl#',
  xsd: 'http://www.w3.org/2001/XMLSchema#',
  geof: 'http://www.opengis.net/def/function/geosparql/',
  prov: 'http://www.w3.org/ns/prov#',
  bd: 'http://www.bigdata.com/rdf#',
  ontolex: 'http://www.w3.org/ns/lemon/ontolex#',
  dct: 'http://purl.org/dc/terms/',
};
// Longest namespace first, so ps: wins over p:, psv: over ps:.
const ORDERED = Object.entries(PREFIXES).sort((a, b) => b[1].length - a[1].length);

/** {prefix, local} for an IRI, or null. */
export function compact(iri) {
  for (const [pfx, ns] of ORDERED) if (iri.startsWith(ns)) return { prefix: pfx, local: iri.slice(ns.length) };
  return null;
}

/** Human names for well-known non-Wikidata IRIs. */
const VOCAB = {
  'rdfs:label': 'label', 'skos:altLabel': 'alias', 'schema:description': 'description',
  'schema:about': 'is about', 'schema:isPartOf': 'is part of (wiki)', 'schema:inLanguage': 'language',
  'schema:name': 'name', 'wikibase:badge': 'badge', 'wikibase:sitelinks': 'number of sitelinks',
  'wikibase:statements': 'number of statements', 'wikibase:identifiers': 'number of identifiers',
  'wikibase:rank': 'rank', 'wikibase:directClaim': 'direct-claim predicate',
  'wikibase:propertyType': 'property datatype', 'rdf:type': 'type', 'owl:sameAs': 'same as',
  'wikibase:timePrecision': 'time precision', 'wikibase:timeValue': 'time value',
};

export class Names {
  constructor(labelsPath) {
    const d = JSON.parse(fs.readFileSync(labelsPath, 'utf8'));
    this.meta = d.meta;
    this.entities = d.entities;
  }
  /** The Wikidata ID an IRI denotes (Q/P/L number), whatever the namespace. */
  wikidataId(iri) {
    const c = compact(iri);
    if (!c) return null;
    const m = /^(?:statement\/|value\/)?([PQL]\d+)$/.exec(c.local);
    return m && ['wd', 'wdt', 'wdtn', 'p', 'ps', 'psv', 'pq', 'pqv', 'pr', 'wdno'].includes(c.prefix) ? m[1] : null;
  }
  entity(id) { return this.entities[id] || null; }
  /** lower-cased label -> [ids], over the cache (built once). */
  labelIndex() {
    if (!this._byLabel) {
      this._byLabel = new Map();
      for (const [id, e] of Object.entries(this.entities)) if (e.label) {
        const k = e.label.toLowerCase();
        this._byLabel.set(k, [...(this._byLabel.get(k) || []), id]);
      }
    }
    return this._byLabel;
  }
  /** 'label (ID)', or 'ID [deleted]' / 'ID [redirect → X]' flags. */
  idName(id) {
    const e = this.entity(id);
    if (!e) return `${id} [label not cached]`;
    if (e.missing) return `${id} [deleted]`;
    const base = e.label ? `${e.label} (${id})` : id;
    return e.redirected_to ? `${base} [redirect → ${e.redirected_to}]` : base;
  }
  /** Readable name for any IRI. */
  iri(iri) {
    const id = this.wikidataId(iri);
    if (id) return this.idName(id);
    const c = compact(iri);
    if (c) return VOCAB[`${c.prefix}:${c.local}`] ? `${VOCAB[`${c.prefix}:${c.local}`]} (${c.prefix}:${c.local})` : `${c.prefix}:${c.local}`;
    return `<${iri}>`;
  }
  /** Short form as written in SPARQL (prefix:local or <iri>). */
  short(iri) {
    const c = compact(iri);
    return c ? `${c.prefix}:${c.local}` : `<${iri}>`;
  }
}
