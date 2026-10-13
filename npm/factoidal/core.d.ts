// TypeScript declarations for '@factoidal/core/core' (core.mjs, core.js):
// the functions of the main entry (index.d.ts) over the core engine,
// l4factoidal-core.wasm (issue 713 stage 4). The types are the main entry's;
// a function the core engine does not serve rejects with an error naming
// '@factoidal/core', and capabilities() reports profile 'core'.

export * from './index';
export { default } from './index';
// Added in 0.10.0 (lib/pure.mjs).
export function aeadSeal(a: { key: Uint8Array; nonce: Uint8Array; plaintext?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function aeadOpen(a: { key: Uint8Array; nonce: Uint8Array; ciphertext: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function hpkeSeal(a: { skE: Uint8Array; pkR: Uint8Array; plaintext?: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<{ message: Uint8Array; enc: Uint8Array; ciphertext: Uint8Array }>;
export function hpkeOpen(a: { skR: Uint8Array; message: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function proofCheck(bundleJson: string): Promise<Record<string, unknown>>;
export function proofInspect(bundleJson: string): Promise<Record<string, unknown>>;
export function canonicalizeNQuads(nquads: string): Promise<string>;
export function normalizeNQuads(nquads: string): Promise<string>;
export function serveStore(root: string, options?: { port?: number; host?: string; queryPath?: string; gspPath?: string }): Promise<{ url: string; port: number; close(): Promise<void> }>;
