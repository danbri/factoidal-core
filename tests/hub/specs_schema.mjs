// Checks the Hub Data and documents page's data files against docs/web/hub/specs/data.schema.json,
// with the validator of tests/hub/conformance_schema.mjs (the same JSON Schema subset).
//
//   node tests/hub/specs_schema.mjs DIR     checks DIR/data.json, DIR/history.json and the header of DIR/records.csv
//
// Exit 0 when every file matches, 1 with every mismatch listed.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {validate} from './conformance_schema.mjs';

const HERE = path.dirname(fileURLToPath(import.meta.url));
export const SCHEMA_PATH = path.join(HERE, '..', '..', 'docs', 'web', 'hub', 'specs', 'data.schema.json');
/** The columns of records.csv, in order (specs-data.py RECORD_FIELDS). */
export const RECORD_COLUMNS = ['suite', 'family', 'spec', 'version', 'technology', 'testType', 'population', 'manifest', 'source',
  'sourceKind', 'engine', 'platform', 'commit', 'run', 'finished', 'trigger', 'total', 'passed', 'failed', 'decided', 'undecided',
  'status', 'reason', 'stale', 'staleReason', 'current', 'headline', 'workflow'];

/** Mismatches of the files of a directory: {"data.json": [...], "history.json": [...], "records.csv": [...]}. */
export function checkDir(dir) {
  const schema = JSON.parse(fs.readFileSync(SCHEMA_PATH, 'utf8'));
  const result = {};
  for (const name of ['data.json', 'history.json']) {
    let value;
    try { value = JSON.parse(fs.readFileSync(path.join(dir, name), 'utf8')); }
    catch (e) { result[name] = [`not read: ${e.message}`]; continue; }
    result[name] = validate(value, schema[name], schema.definitions);
  }
  const csvPath = path.join(dir, 'records.csv');
  if (fs.existsSync(csvPath)) {
    const head = fs.readFileSync(csvPath, 'utf8').split('\n', 1)[0];
    result['records.csv'] = head === RECORD_COLUMNS.join(',') ? [] : [`header ${head} is not ${RECORD_COLUMNS.join(',')}`];
  }
  return result;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const dir = process.argv[2];
  if (!dir) { console.error('usage: node tests/hub/specs_schema.mjs DIR'); process.exit(2); }
  let bad = 0;
  for (const [file, errs] of Object.entries(checkDir(dir))) {
    for (const e of errs) { console.error(`${file}: ${e}`); bad++; }
    if (!errs.length) console.log(`${file}: ok`);
  }
  process.exit(bad ? 1 : 0);
}
