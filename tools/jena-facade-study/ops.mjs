const m = await import('/home/user/factoidal-core/npm/factoidal/index.mjs');
const e = await m.loadEngine();
const r = e.call('ops', []);
const j = typeof r === 'string' ? JSON.parse(r) : r;
console.log(j.abiVersion, j.ops.length); console.log(j.ops.join(' '));
