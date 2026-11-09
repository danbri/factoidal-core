// native_html_engine.ts imports the build-generated Wasm runtime statically; the import map
// sends that import here. With the native library no call reaches this module's stand-in.
// With --wasm, useWasm names the runtime, which is then imported on the first createModule.
let runtime;
export function useWasm(url) { runtime = url; }
export default async function createModule() {
  if (runtime) return (await import(runtime)).default();
  const absent = () => { throw new Error("textnaut: this call needs the Wasm runtime"); };
  return { ccall: absent, UTF8ToString: absent, HEAPU8: new Uint8Array(0) };
}
