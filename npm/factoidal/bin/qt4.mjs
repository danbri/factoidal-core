// CLI transport only: read explicit files, call the existing Lean operation,
// display its JSON/serialization, and preserve the engine's QT4 error QName.
import { errorFromEnvelope } from '../lib/errors.mjs';

export class Qt4UsageError extends Error {}

export async function runQt4(command, positional, options, host) {
  const transform = command === 'xslt4';
  const key = transform ? 'stylesheet' : command === 'xpath4' ? 'expression' : 'query';
  const allowed = new Set([key, 'input', 'format', 'help', ...(transform ? [] : ['file'])]);
  for (const option of Object.keys(options)) {
    if (!allowed.has(option)) throw new Qt4UsageError(`unknown option --${option}`);
  }
  if (positional.length > 1) throw new Qt4UsageError('expected at most one positional argument');
  const sources = [positional[0], options[key], options.file].filter((value) => value !== undefined);
  if (sources.length !== 1 || typeof sources[0] !== 'string') {
    throw new Qt4UsageError(`supply exactly one ${key}${transform ? ' file' : ' text or --file PATH'}`);
  }
  if (options.input !== undefined && typeof options.input !== 'string') throw new Qt4UsageError('--input needs a file path');
  const format = options.format ?? 'json';
  const formats = transform ? ['json', 'output'] : ['json', 'adaptive', 'xml'];
  if (!formats.includes(format)) throw new Qt4UsageError(`--format must be ${formats.join(', ')}`);
  try {
    const expression = transform || options.file !== undefined ? host.readText(sources[0]) : sources[0];
    const input = options.input === undefined ? '' : host.readText(options.input);
    const op = transform ? 'xslt4Transform' : command === 'xpath4' ? 'xpath4Eval' : 'xqueryEval';
    const args = command === 'xpath4' ? [input, expression] : [expression, input];
    const result = (await host.loadEngine()).call(op, args);
    if (format === 'json') host.out(JSON.stringify(result, null, 2));
    else {
      const text = result[format];
      if (text === null || typeof text !== 'string') {
        host.err(`factoidal ${command}: result has no ${format} serialization; use --format json`);
        return 1;
      }
      host.out(text);
    }
    return 0;
  } catch (error) {
    // loadL4.call throws a plain Error with the original envelope. API wrappers
    // normalize it separately; the direct CLI call must preserve it here too.
    const envelope = error?.envelope;
    const problem = envelope && typeof envelope === 'object' && envelope.ok === false
      ? errorFromEnvelope(envelope) : error;
    host.err(JSON.stringify({ error: String(problem?.message ?? problem),
      ...(problem?.code ? { code: problem.code } : {}), ...(problem?.qtError ? { qtError: problem.qtError } : {}) }));
    return 1;
  }
}
