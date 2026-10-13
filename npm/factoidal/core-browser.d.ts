// TypeScript declarations for core-browser.js, the browser form of
// '@factoidal/core/core': the functions of browser.d.ts over the core engine,
// l4factoidal-core.wasm (issue 713 stage 4).

export * from './browser';
// Added in 0.10.0 (lib/pure.mjs).
export function aeadSeal(a: { key: Uint8Array; nonce: Uint8Array; plaintext?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function aeadOpen(a: { key: Uint8Array; nonce: Uint8Array; ciphertext: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function hpkeSeal(a: { skE: Uint8Array; pkR: Uint8Array; plaintext?: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<{ message: Uint8Array; enc: Uint8Array; ciphertext: Uint8Array }>;
export function hpkeOpen(a: { skR: Uint8Array; message: Uint8Array; info?: Uint8Array; aad?: Uint8Array }): Promise<Uint8Array>;
export function proofCheck(bundleJson: string): Promise<Record<string, unknown>>;
export function proofInspect(bundleJson: string): Promise<Record<string, unknown>>;
export function canonicalizeNQuads(nquads: string): Promise<string>;
export function normalizeNQuads(nquads: string): Promise<string>;
