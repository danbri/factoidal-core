// Types of session.mjs for the Deno hosts (deno check). The module is plain JavaScript.
export type ScriptBatch = {
  commands: unknown[]; listeners: { nodeId: number; type: string }[]; documentListeners: string[];
  logs: string[]; errors: string[]; defaultPrevented: boolean; timer: number | null; frame: boolean;
};
export type ScriptEvent = { type: string; nodeId?: number; key?: string; code?: string; shiftKey?: boolean; metaKey?: boolean; altKey?: boolean; ctrlKey?: boolean };
export type ScriptStart = { nodes: unknown[]; next?: number; source?: string; sources?: string[]; budgetMs?: number; document?: { source: string; url: string; commands: unknown[] } };
export interface ScriptSession {
  readonly listeners: { nodeId: number; type: string }[];
  readonly documentListeners: string[];
  readonly running: boolean;
  start(args: ScriptStart): Promise<ScriptBatch>;
  dispatch(event: ScriptEvent, options?: { budgetMs?: number }): Promise<ScriptBatch>;
  timers(options?: { budgetMs?: number }): Promise<ScriptBatch>;
  frame(options?: { budgetMs?: number }): Promise<ScriptBatch>;
  reset(): void;
}
export const EVENT_TYPES: string[];
export function validateBatch(batch: unknown, allowedIds: Set<number>): ScriptBatch;
export function createScriptSession(options?: { workerFactory?: () => Worker; wasmURL?: string; wasmBytes?: Uint8Array; watchdogMs?: number; leanModuleURL?: string; now?: () => number }): ScriptSession;
