// TypeScript declarations for '@factoidal/core/api': the typed API over a
// Lean engine the caller loaded (api.mjs).

/**
 * A loaded Lean engine handle (the value `loadL4()` of
 * `@factoidal/core/l4-assets/l4factoidal.js` resolves to: an object with
 * `call(op, args)`), a Promise of one, or a zero-argument function
 * answering either.
 */
export type EngineSource =
  | object
  | Promise<object>
  | (() => object | Promise<object>);

export interface CreateApiOptions {
  /** Reported as the returned API's `engine` field. Default 'lean4-wasm'. */
  engineName?: string;
}

/**
 * The typed API (the functions `@factoidal/core` exports) over `engine`.
 * Throws a TypeError when `engine` is a plain object with no `call`
 * method. `openStore()` on the result takes a reader function only.
 */
export function createApi(
  engine: EngineSource,
  options?: CreateApiOptions
): typeof import('./index').default;

/**
 * The constructor createApi() is built on: a typed API over an ENTRY
 * object (one method per dispatch op, string arguments, a JSON envelope
 * string back), as entryFromEngine() builds it.
 */
export function buildApi(driver: {
  engineName: string;
  loadEntry: () => object | Promise<object>;
  storeReaderFor?: (root: string) => import('./index').StoreReader;
}): typeof import('./index').default;

/** The entry object over a loaded engine handle (lib/lean-entry.mjs). */
export function entryFromEngine(engine: object): Record<string, unknown>;

export const Dataset: typeof import('./index').Dataset;
export const DatasetHandle: typeof import('./index').DatasetHandle;
export const Store: typeof import('./index').Store;
export const dataFactory: import('./index').DataFactory;
/** The one error class; see index.d.ts's FactoidalError. */
export const FactoidalError: typeof import('./index').FactoidalError;
/** Package version string, e.g. '0.9.0'. */
export const version: string;

export default createApi;
