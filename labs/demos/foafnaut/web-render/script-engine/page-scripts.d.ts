// Types of page-scripts.mjs for the Deno hosts (deno check).
import type { ScriptBatch, ScriptEvent, ScriptSession, ScriptStart } from './session.d.ts';
export type PageScriptStats = { turns: number; frames: number; timers: number; events: number; commands: number; compactions: number; errors: number };
export interface PageScripts {
  readonly commands: unknown[];
  readonly stopped: string | null;
  readonly listeners: { nodeId: number; type: string }[];
  readonly documentListeners: string[];
  readonly animating: boolean;
  readonly stats: PageScriptStats;
  start(args: ScriptStart): Promise<ScriptBatch>;
  dispatch(event: ScriptEvent): Promise<ScriptBatch>;
  wants(type: string, nodeId: number): boolean;
  stop(reason: string): void;
}
export function createPageScripts(options: {
  session: ScriptSession;
  compact?: (commands: unknown[]) => Promise<unknown[]>;
  onBatch?: (batch: ScriptBatch, kind: string) => Promise<void>;
  onStop?: (reason: string) => void;
  frameInterval?: number;
  setTimer?: (f: () => void, ms: number) => unknown;
  clearTimer?: (id: unknown) => void;
  now?: () => number;
}): PageScripts;
