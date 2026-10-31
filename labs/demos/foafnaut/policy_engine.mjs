// Portable transport for the Factoidal Lean policy API. No geometry or policy
// arithmetic lives here. Browsers, Deno and Node consume the same WASM bytes.
import createModule from './.build/engines/layout-policy-engine.mjs';

export async function loadLayoutPolicy() {
  const module = await createModule();
  function request(input) {
    const pointer = module.ccall('layout_policy', 'number', ['string'], [JSON.stringify(input)]);
    if (!pointer) throw new Error('Lean layout policy initialization/allocation failed');
    try {
      const result = JSON.parse(module.UTF8ToString(pointer));
      if (!result.ok) throw Object.assign(new Error(result.error), { report: result });
      return result;
    } finally { module.ccall('layout_policy_free', null, ['number'], [pointer]); }
  }
  function bind(application, configuration) {
    const checked = request({ op: 'configure', application, configuration });
    const app = Object.freeze(checked.application);
    const config = Object.freeze(checked.configuration);
    return Object.freeze({
      application: app, configuration: config, targetIntervalMs: checked.targetIntervalMs,
      check(viewport, footprints) {
        return request({ op: 'check', application: app, configuration: config, viewport, footprints });
      },
      retune(configuration) { return bind(app, configuration); },
    });
  }
  return Object.freeze({ request, defaults: () => request({ op: 'defaults' }), bind });
}
