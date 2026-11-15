// Checks the Hub Conformance page's data files against docs/web/hub/conformance/data.schema.json.
// No dependencies: the schema uses a small JSON Schema subset (type, required, properties, items,
// additionalValues, enum, minimum, maximum, minItems, pattern, $ref to a name in "definitions").
//
//   node tests/hub/conformance_schema.mjs DIR        checks DIR/data.json and DIR/history.json
//
// Exit 0 when both files match, 1 with every mismatch listed.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
export const SCHEMA_PATH = path.join(HERE, '..', '..', 'docs', 'web', 'hub', 'conformance', 'data.schema.json');

const typeOf = v => v === null ? 'null' : Array.isArray(v) ? 'array' : Number.isInteger(v) ? 'integer' : typeof v;
const fits = (v, t) => t === typeOf(v) || (t === 'number' && typeof v === 'number' && Number.isFinite(v));

/** Every mismatch of `value` against `schema`, as "path: reason" strings. */
export function validate(value, schema, defs = {}, at = '$', out = []) {
  if (schema.$ref) return validate(value, defs[schema.$ref], defs, at, out);
  if (schema.type) {
    const types = [].concat(schema.type);
    if (!types.some(t => fits(value, t))) { out.push(`${at}: ${typeOf(value)}, expected ${types.join(' or ')}`); return out; }
  }
  if (value === null) return out;
  if (schema.enum && !schema.enum.includes(value)) out.push(`${at}: ${JSON.stringify(value)} not one of ${schema.enum.join(', ')}`);
  if (typeof value === 'number') {
    if (schema.minimum !== undefined && value < schema.minimum) out.push(`${at}: ${value} < ${schema.minimum}`);
    if (schema.maximum !== undefined && value > schema.maximum) out.push(`${at}: ${value} > ${schema.maximum}`);
  }
  if (typeof value === 'string' && schema.pattern && !new RegExp(schema.pattern).test(value)) out.push(`${at}: ${JSON.stringify(value)} does not match ${schema.pattern}`);
  if (Array.isArray(value)) {
    if (schema.minItems !== undefined && value.length < schema.minItems) out.push(`${at}: ${value.length} items, at least ${schema.minItems}`);
    if (schema.items) value.forEach((v, i) => validate(v, schema.items, defs, `${at}[${i}]`, out));
  } else if (typeof value === 'object') {
    for (const k of schema.required ?? []) if (!(k in value)) out.push(`${at}: no ${k}`);
    for (const [k, s] of Object.entries(schema.properties ?? {})) if (k in value) validate(value[k], s, defs, `${at}.${k}`, out);
    if (schema.additionalValues) for (const [k, v] of Object.entries(value)) if (!(schema.properties ?? {})[k]) validate(v, schema.additionalValues, defs, `${at}.${k}`, out);
  }
  return out;
}

/** Mismatches of the two files of a directory: {"data.json": [...], "history.json": [...]}. */
export function checkDir(dir) {
  const schema = JSON.parse(fs.readFileSync(SCHEMA_PATH, 'utf8'));
  const result = {};
  for (const name of ['data.json', 'history.json']) {
    let value;
    try { value = JSON.parse(fs.readFileSync(path.join(dir, name), 'utf8')); }
    catch (e) { result[name] = [`not read: ${e.message}`]; continue; }
    result[name] = validate(value, schema[name], schema.definitions);
  }
  return result;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const dir = process.argv[2];
  if (!dir) { console.error('usage: node tests/hub/conformance_schema.mjs DIR'); process.exit(2); }
  const result = checkDir(dir);
  let bad = 0;
  for (const [name, errs] of Object.entries(result)) {
    console.log(`${errs.length ? 'FAIL' : 'ok  '} ${name}${errs.length ? `: ${errs.length} mismatches` : ''}`);
    for (const e of errs.slice(0, 40)) console.log(`     ${e}`);
    bad += errs.length;
  }
  process.exit(bad ? 1 : 0);
}
