// Browser/Node/Deno transport only. RDF, state, geometry, SVG and policy
// decisions all run in the same Lean WASM module.
import createModule from './.build/engines/foafnaut-engine.mjs';

export async function loadFoafTransport() {
  const module = await createModule();
  return function call(name, types, values) {
    const pointer = module.ccall(name, 'number', types, values);
    if (!pointer) throw new Error('Lean FOAFNaut initialization/allocation failed');
    try {
      const result = JSON.parse(module.UTF8ToString(pointer));
      if (result.error) throw Object.assign(new Error(`Lean FOAFNaut: ${result.error}`), { report: result });
      return result;
    } finally { module.ccall('foafnaut_free', null, ['number'], [pointer]); }
  };
}
