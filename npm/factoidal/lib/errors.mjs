// factoidal — the one error class of the package
// (https://github.com/danbri/factoidal/issues/882 item 4).
//
// Every function of the package rejects (or throws) with a FactoidalError.
// The engine decides its `code`, its `spec` section and its `position`
// (formal/lean4/Wasm/Ops/ErrorModel.lean); this file only copies them out
// of the error envelope. A TypeError is thrown only when an argument has the
// wrong JavaScript type (a number where a string is needed, and the like).
//
// ES module, no Node built-ins: the browser loads this file as it is.

/**
 * An engine refusal, or a host failure (`host.io`).
 *
 * - `code`: a stable machine code, one of the engine's `errorCodes` table
 *   (op engineTables; README "Errors").
 * - `position`: `{line, column, offset, byteOffset}` where the input defines
 *   one, else `null`. `line` and `column` are 1-based (`column` counts
 *   Unicode scalar values); `offset` is a UTF-16 index into the JavaScript
 *   string, so `text.slice(err.position.offset)` starts at the error;
 *   `byteOffset` counts UTF-8 bytes.
 * - `spec`: the URL of the specification section that defines the
 *   condition, or `null`.
 * - `cause`: the underlying error, when there is one.
 * - `format`, `formatInferred`: for a parse failure of text, the syntax it
 *   was read as and whether that syntax was inferred.
 */
export class FactoidalError extends Error {
  constructor(message, info) {
    const i = info || {};
    super(message, i.cause !== undefined ? { cause: i.cause } : undefined);
    this.name = 'FactoidalError';
    this.code = i.code || 'op.failed';
    this.position = i.position || null;
    this.spec = i.spec || null;
    if (i.format !== undefined) this.format = i.format;
    if (i.formatInferred !== undefined) this.formatInferred = i.formatInferred;
    if (typeof Error.captureStackTrace === 'function') {
      Error.captureStackTrace(this, FactoidalError);
    }
  }
}

// The engine counts `offset` in Unicode scalar values from the start of the
// input; a JavaScript string is indexed in UTF-16 code units, where a
// character at U+10000 or above takes two. This converts the count to the
// UTF-16 index of the same position (a unit conversion of the host string;
// a count past the end gives text.length).
export function utf16OffsetOf(text, scalarOffset) {
  if (typeof text !== 'string' || !Number.isInteger(scalarOffset) || scalarOffset < 0) {
    return scalarOffset;
  }
  let units = 0;
  let scalars = 0;
  for (const ch of text) {
    if (scalars >= scalarOffset) break;
    units += ch.length;
    scalars += 1;
  }
  return units;
}

/**
 * The FactoidalError of an error envelope ({"ok":false,"error",...}).
 * `text` is the input string the envelope's position counts into, when the
 * caller has it.
 */
export function errorFromEnvelope(env, text) {
  const p = env && env.position;
  let position = null;
  if (p && typeof p === 'object') {
    position = {
      line: p.line,
      column: p.column,
      offset: typeof text === 'string' ? utf16OffsetOf(text, p.offset) : p.offset,
      byteOffset: p.byteOffset,
    };
  }
  return new FactoidalError(String((env && env.error) || 'engine refusal'), {
    code: env && env.code,
    spec: env && env.spec,
    position,
    format: env && env.format,
  });
}

/** Unwrap one op envelope: the envelope object, or throw its FactoidalError. */
export function envelopeResult(jsonText, text) {
  const r = typeof jsonText === 'string' ? JSON.parse(jsonText) : jsonText;
  if (!r.ok) throw errorFromEnvelope(r, text);
  return r;
}

/** A host failure (file system, IndexedDB): code `host.io`, with its cause. */
export function hostError(message, cause) {
  return new FactoidalError(message, { code: 'host.io', cause });
}
