// Types of adapter.mjs for the Deno hosts (deno check).
import type { ScriptSession } from '../session.d.ts';
export const VERIFIEDJS_ISSUE: string;
export function verifiedJSBinary(path?: URL | string): string | undefined;
export function verifiedJSAvailable(path?: URL | string): string;
export function moduleInterface(bytes: BufferSource): { imports: string[]; exports: string[] };
export function createVerifiedJSSession(options?: { binary?: string }): ScriptSession;
