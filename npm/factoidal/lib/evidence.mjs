// The evidence logic of the node-composition API (issue 1002), kept apart
// from the engine so it runs, and is tested, without the wasm.
//
// Rule (owner-approved, issue 975 comment 6393905605 item 3): a stage that
// is not `proved` may run only after an explicit opt-in, and its evidence
// record says so. A result never reports a guarantee the path lacks:
// `proved` is true only when every record is `checked`.
//
// ES module, no Node built-ins.

import { FactoidalError } from './errors.mjs';

/** A stage is checked exactly when its registry status is `proved`. */
export const isChecked = (status) => status === 'proved';

/** The reason text of an unchecked step. */
export function reasonOf(n) {
  if (n.status === 'missing') return 'no contract';
  return n.assumptions.length > 0
    ? `status ${n.status}; assumptions: ${n.assumptions.join(', ')}`
    : `status ${n.status}`;
}

/**
 * The refusal for node `n` before anything runs, or null. `hasRunner` is
 * whether the package has a function that runs the stage.
 * Without the opt-in a `missing` stage refuses (op.failed). With it, a stage
 * runs when it has a runner; one with no runner refuses (op.unknown).
 */
export function refusalFor(n, unchecked, hasRunner) {
  if (!n.runnable && !unchecked) {
    return new FactoidalError(`run: stage '${n.stage}' has status ${n.status}: ` +
      'no contract and no test suite, so it does not run as a node ' +
      '(pass { unchecked: true } to run it without a guarantee)', { code: 'op.failed' });
  }
  if (!hasRunner) {
    return new FactoidalError(`run: stage '${n.stage}' has no package function that runs it`,
      { code: 'op.unknown' });
  }
  return null;
}

/**
 * One evidence record. `checked` is true iff the status is `proved`.
 * A step that ran under the opt-in and is not checked also carries
 * `unchecked: true` and `reason`.
 */
export function makeRecord(n, artefact, unchecked) {
  const checked = isChecked(n.status);
  const base = {
    stage: n.stage,
    status: n.status,
    contract: n.contract,
    assumptions: n.assumptions,
    checked,
    artefact: artefact === undefined ? null : artefact,
  };
  if (unchecked && !checked) {
    base.unchecked = true;
    base.reason = reasonOf(n);
  }
  return Object.freeze(base);
}

/** A record is checked; a record without `checked` (older producer) falls back to its status. */
export const recordChecked = (r) => (typeof r.checked === 'boolean' ? r.checked : isChecked(r.status));

/** The union of the named assumptions of the records, first-seen order. */
export function unionAssumptions(records) {
  const seen = new Set();
  const out = [];
  for (const r of records) {
    for (const a of r.assumptions) {
      if (!seen.has(a)) { seen.add(a); out.push(a); }
    }
  }
  return out;
}

/** `{ assumptions, proved, uncheckedSteps }` of a record list. */
export function summarize(records) {
  const uncheckedSteps = records.filter((r) => !recordChecked(r)).map((r) => r.stage);
  return { assumptions: unionAssumptions(records), proved: uncheckedSteps.length === 0, uncheckedSteps };
}
