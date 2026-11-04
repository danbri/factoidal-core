import { loadFoafTransport } from "./foafnaut_transport.mjs";
import { validateFoafFrame, type FoafFrame, type LayoutPolicy, type CheckedSVG } from "./foafnaut_engine.ts";
import type { UIEvent } from "./ui_engine.ts";

export type LiveFrame = FoafFrame & {
  presentation: {
    abi: "lean-foafnaut-live-v1"; available: boolean;
    status: "accepted" | "rejected" | "deferred" | "clockWentBack";
    candidateRevision: number; lastCheckMs: number | null; targetIntervalMs: number; renderToken: number;
  };
};
function clock(now: number): string {
  if (!Number.isSafeInteger(now) || now < 0) throw new Error("Invalid monotonic clock input");
  return String(now);
}
export function validateLiveFrame(value: unknown): LiveFrame {
  const frame = validateFoafFrame(value) as LiveFrame;
  const p = frame.presentation;
  if (!p || p.abi !== "lean-foafnaut-live-v1" || typeof p.available !== "boolean" ||
      !["accepted", "rejected", "deferred", "clockWentBack"].includes(p.status) ||
      !Number.isSafeInteger(p.candidateRevision) || p.candidateRevision < 0 ||
      !Number.isSafeInteger(p.renderToken) || p.renderToken < 0 ||
      (p.lastCheckMs !== null && (!Number.isSafeInteger(p.lastCheckMs) || p.lastCheckMs < 0)) ||
      !Number.isSafeInteger(p.targetIntervalMs) || p.targetIntervalMs <= 0 ||
      frame.layout?.enforced !== true || frame.layout?.withinBudget !== true)
    throw new Error("Invalid Lean live presentation response");
  return frame;
}

// This module transports input/time and validates the response ABI. The
// approved model, pending model, fixed policy, cadence and effects live in Lean.
// Each instance has one initialization attempt. Reconfiguration/restart uses a
// fresh loadFoafLive() so a previous session's render tokens cannot be reused.
export async function loadFoafLive(rdf: string) {
  if (typeof rdf !== "string" || rdf.includes("\0") || [...rdf].length > 65536)
    throw new Error("Invalid Turtle input ABI");
  const call = await loadFoafTransport();
  return {
    initialize(width = 1000, height = 700, policy?: LayoutPolicy, now = 0) {
      if (![width, height].every(n => Number.isInteger(n) && n >= 0 && n <= 0xffffffff))
        throw new Error("Invalid viewport ABI");
      return validateLiveFrame(call("foafnaut_live_start",
        ["string", "number", "number", "string", "string"],
        [rdf, width, height, policy === undefined ? "" : JSON.stringify(policy), clock(now)]));
    },
    step(event: UIEvent, now: number) {
      if (![event.kind, event.a, event.b].every(Number.isInteger) || event.kind < 0 || event.kind > 0xffffffff ||
          event.a < -0x80000000 || event.a > 0x7fffffff || event.b < -0x80000000 || event.b > 0x7fffffff)
        throw new Error("Invalid input event ABI");
      return validateLiveFrame(call("foafnaut_live_event", ["number", "number", "number", "string"],
        [event.kind, event.a, event.b, clock(now)]));
    },
    insertText(text: string, now: number) {
      if (typeof text !== "string" || text.includes("\0") || text.length > 1048576)
        throw new Error("Invalid committed text ABI");
      return validateLiveFrame(call("foafnaut_live_text", ["string", "string"], [text, clock(now)]));
    },
    present(now: number) {
      return validateLiveFrame(call("foafnaut_live_tick", ["string"], [clock(now)]));
    },
    acknowledge(token: number) {
      return validateLiveFrame(call("foafnaut_live_acknowledge", ["string"], [clock(token)]));
    },
    svg(): CheckedSVG {
      const value = call("foafnaut_live_export_svg", [], []);
      if (value.checked !== true || typeof value.svg !== "string") throw new Error("Invalid checked SVG response");
      return value;
    },
    dispose() { call("foafnaut_live_dispose", [], []); },
  };
}
