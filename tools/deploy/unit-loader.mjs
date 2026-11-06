// unit-loader.mjs: load a split engine. One primary wasm with the Lean runtime and heap; each
// other unit is a wasm module that imports the primary's memory, table and functions, so Lean
// objects and closures cross units as plain pointers. `readUnit(name)` gives the bytes.
// A call into an unloaded unit reaches a placeholder: readUnitSync loads it there, else it throws.
export async function createEngine({ factory, readUnit, readUnitSync, units }) {
  const loaded = new Set(); const pending = new Map(); let inst = null, table = null;
  const stats = { loads: [] };
  const primaryImports = exports_ => {
    const primary = {};
    for (const [k, v] of Object.entries(exports_)) primary[k] = v;
    return { primary };
  };
  const placeholder = (unit, slot) => (...args) => {
    if (!loaded.has(unit)) {
      if (!readUnitSync) throw new Error(`unit ${unit} not loaded: call ensure("${unit}") first`);
      finish(unit, new WebAssembly.Instance(new WebAssembly.Module(readUnitSync(unit)), primaryImports(inst.exports)));
      stats.loads.push({ unit, how: 'placeholder' });
    }
    return table.get(slot)(...args);
  };
  const finish = (unit) => { loaded.add(unit); };
  const module = await factory({
    instantiateWasm(imports, receive) {
      (async () => {
        const bytes = await readUnit('primary');
        const mod = await WebAssembly.compile(bytes);
        for (const i of WebAssembly.Module.imports(mod)) {
          if (!i.module.startsWith('placeholder.')) continue;
          const unit = i.module.slice('placeholder.'.length);
          (imports[i.module] ??= {})[i.name] = placeholder(unit, Number(i.name));
        }
        inst = await WebAssembly.instantiate(mod, imports);
        table = inst.exports.__indirect_function_table;
        receive(inst, mod);
      })().catch(e => { throw e; });
      return {};
    },
  });
  const ensure = unit => {
    if (loaded.has(unit)) return Promise.resolve();
    if (!pending.has(unit)) pending.set(unit, (async () => {
      const t0 = performance.now();
      const bytes = await readUnit(unit);
      const r = await WebAssembly.instantiate(bytes, primaryImports(inst.exports));
      finish(unit, r.instance);
      stats.loads.push({ unit, how: 'ensure', ms: +(performance.now() - t0).toFixed(1), bytes: bytes.byteLength });
    })());
    return pending.get(unit);
  };
  return { module, ensure, stats, isLoaded: u => loaded.has(u), units };
}
