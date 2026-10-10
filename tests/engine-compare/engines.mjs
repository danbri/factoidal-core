// The two engines a comparison case runs: the Lean engine of
// @factoidal/core (npm/factoidal/index.mjs) and the F* engine's npm-entry
// bundle, driven through the SAME typed layer (npm/factoidal/lib/api.mjs's
// buildApi). The F* entry has the op names and envelopes the Lean dispatch
// table answers, so one wrapper drives both; only the engine differs.
//
// The F* bundle path comes from $FACTOIDAL_FSTAR_ENTRY (run.sh sets it).

import { createRequire } from 'node:module';
import * as lean from '../../npm/factoidal/index.mjs';
import { buildApi } from '../../npm/factoidal/lib/api.mjs';

const require = createRequire(import.meta.url);

function loadFstarEntry() {
  const path = process.env.FACTOIDAL_FSTAR_ENTRY;
  if (!path) throw new Error('FACTOIDAL_FSTAR_ENTRY is not set; run tests/engine-compare/run.sh');
  const mod = require(path);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  if (!abi || typeof abi.queryDataset !== 'function') {
    throw new Error(`${path} registers no factoidalNpmEntry with a queryDataset op`);
  }
  return abi;
}

export const fstar = buildApi({ engineName: 'fstar-npm-entry', loadEntry: loadFstarEntry });
export { lean };

/** One binding row (Map<string, Term>) as a stable string. */
export function rowKey(row) {
  return JSON.stringify(
    [...row.entries()]
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
      .map(([name, term]) => [
        name, term.termType, term.value,
        term.termType === 'Literal' ? term.datatype.value : '',
        term.termType === 'Literal' ? term.language : '',
      ]));
}

/** A row list as a sorted multiset of row keys. */
export function rowMultiset(rows) {
  return rows.map(rowKey).sort();
}
