// Hub-only wrappers for the demonstration maths ops of the Lean engine
// (Wasm/Ops/Maths.lean: matrixDeterminant, matrixScalarProduct,
// matrixVectorProduct, matrixOuterProduct, sigmoidPoints,
// sigmoidFormulaMathml). The npm package dropped these functions in 0.10.0
// (owner, 2026-10-20: demonstration functions leave the package); hub posts
// 28 and 34 still call them, so the hub page (docs/_includes/hub.njk,
// hubHelpers) and the post tests bind them from here. They only marshal
// JSON over `engine.call(op, args)`; every value is the engine's.

function envelope(r, op) {
  if (!r || r.ok === false) throw new Error(`${op}: ${r && r.error}`);
  return r;
}

function matrixCall(engine, op, ...args) {
  const r = envelope(engine.call(op, args.map((a) => JSON.stringify(a))), op);
  return { result: r.result, reason: r.reason || '' };
}

function arrays(op, ...xs) {
  if (!xs.every(Array.isArray)) throw new TypeError(`${op}: arguments must be arrays`);
}

export function matrixDeterminant(engine, matrix) {
  arrays('matrixDeterminant', matrix);
  return matrixCall(engine, 'matrixDeterminant', matrix);
}
export function matrixScalarProduct(engine, a, b) {
  arrays('matrixScalarProduct', a, b);
  return matrixCall(engine, 'matrixScalarProduct', a, b);
}
export function matrixVectorProduct(engine, a, b) {
  arrays('matrixVectorProduct', a, b);
  return matrixCall(engine, 'matrixVectorProduct', a, b);
}
export function matrixOuterProduct(engine, a, b) {
  arrays('matrixOuterProduct', a, b);
  return matrixCall(engine, 'matrixOuterProduct', a, b);
}

const scaled = (s) => ({ mantissa: s.mantissa, scale: s.scale, decimal: s.decimal });

export function sigmoidPoints(engine, params) {
  if (!params || typeof params !== 'object') throw new TypeError('sigmoidPoints: params must be an object');
  const wire = {
    k: String(params.k), x0: String(params.x0), l: String(params.l),
    xmin: String(params.xmin), xmax: String(params.xmax), n: String(params.n),
  };
  const r = envelope(engine.call('sigmoidPoints', [JSON.stringify(wire)]), 'sigmoidPoints');
  return r.points.map((p) => ({ x: scaled(p.x), y: scaled(p.y) }));
}

export function sigmoidFormulaMathml(engine) {
  return envelope(engine.call('sigmoidFormulaMathml', []), 'sigmoidFormulaMathml').mathml;
}

/** The six functions bound to an engine, as `fn` methods. */
export function demoMathsFor(loadEngine) {
  const names = { matrixDeterminant, matrixScalarProduct, matrixVectorProduct,
    matrixOuterProduct, sigmoidPoints, sigmoidFormulaMathml };
  const out = {};
  for (const [name, f] of Object.entries(names)) {
    out[name] = async (...args) => f(await loadEngine(), ...args);
  }
  return out;
}
