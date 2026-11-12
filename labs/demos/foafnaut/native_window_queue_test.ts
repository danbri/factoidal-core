// The window library keeps every discrete input event, in order, under a flood.
// Moves keep only the newest position; scroll steps add up.
import { libraryPath } from "./native_window.ts";
import { POINTER_CANCEL } from "./native_press.ts";

// The library hands out events only on the process main thread, which deno test
// does not use, so the test runs this file as a child process.
function flood() {
  const lib = Deno.dlopen(libraryPath(), {
    ng_test_event: { parameters: ["u32", "i32", "i32"], result: "void" },
    ng_next_event: { parameters: ["buffer"], result: "i32" },
    ng_events_dropped: { parameters: [], result: "u32" },
  });
  try {
    const N = 5000, s = lib.symbols;
    for (let i = 0; i < N; i++) {
      s.ng_test_event(2, i, 0); s.ng_test_event(3, i, 1); s.ng_test_event(3, i, 2);
      s.ng_test_event(5, i, 0); s.ng_test_event(4, i, 0); s.ng_test_event(POINTER_CANCEL, i, 0);
      s.ng_test_event(11, 1, 0); s.ng_test_event(11, 2, 0);
    }
    const bytes = new Uint8Array(16), view = new DataView(bytes.buffer), seen: Record<number, number> = {};
    let downs = 0, keys = 0, cancels = 0, scroll = 0, newestMove = true;
    while (s.ng_next_event(bytes)) {
      const kind = view.getUint32(0, true), a = view.getInt32(4, true);
      seen[kind] = (seen[kind] ?? 0) + 1;
      if (kind === 2 && a !== downs++) throw new Error(`click ${a} out of order`);
      if (kind === 5 && a !== keys++) throw new Error(`key ${a} out of order`);
      if (kind === POINTER_CANCEL && (a !== cancels++ || seen[4] !== cancels || downs !== cancels))
        throw new Error(`cancel ${a} out of order with press/release`);
      if (kind === 3 && view.getInt32(8, true) !== 2) newestMove = false;
      if (kind === 11) scroll += a;
    }
    if (downs !== N || keys !== N || seen[4] !== N || cancels !== N) throw new Error(`lost events: ${JSON.stringify(seen)}`);
    if (!newestMove || scroll !== 3 * N || s.ng_events_dropped() !== 0) throw new Error("coalescing changed input");
  } finally { lib.close(); }
}
function cancel() {
  const lib = Deno.dlopen(libraryPath(), {
    ng_test_event: { parameters: ["u32", "i32", "i32"], result: "void" },
    ng_next_event: { parameters: ["buffer"], result: "i32" },
  });
  try {
    const want = [[2, 10, 20], [3, 30, 40], [POINTER_CANCEL, 0, 0], [POINTER_CANCEL, 0, 0],
      [4, 30, 40], [2, 50, 60], [4, 50, 60]];
    for (const [kind, a, b] of want) lib.symbols.ng_test_event(kind, a, b);
    const bytes = new Uint8Array(16), view = new DataView(bytes.buffer), got: number[][] = [];
    while (lib.symbols.ng_next_event(bytes)) got.push([view.getUint32(0, true), view.getInt32(4, true), view.getInt32(8, true)]);
    if (JSON.stringify(got) !== JSON.stringify(want)) throw new Error(`cancel events ${JSON.stringify(got)}, not ${JSON.stringify(want)}`);
  } finally { lib.close(); }
}
// The off-screen window (run_html.ts --offscreen): never visible, the same queue, and resize
// events in backing pixels at the fixed scale, as a sweep needs them.
function offscreen() {
  const lib = Deno.dlopen(libraryPath(), {
    ng_create_offscreen: { parameters: ["u32", "u32", "f64"], result: "pointer" },
    ng_set_content_size: { parameters: ["u32", "u32"], result: "void" },
    ng_test_event: { parameters: ["u32", "i32", "i32"], result: "void" },
    ng_next_event: { parameters: ["buffer"], result: "i32" },
    ng_pump: { parameters: [], result: "void" },
    ng_surface_state: { parameters: ["buffer"], result: "void" },
  });
  const s = lib.symbols;
  if (!s.ng_create_offscreen(800, 500, 2)) throw new Error("no off-screen window");
  s.ng_test_event(2, 10, 20); s.ng_set_content_size(400, 300); s.ng_test_event(4, 10, 20); s.ng_pump();
  const bytes = new Uint8Array(16), view = new DataView(bytes.buffer), got: number[][] = [];
  while (s.ng_next_event(bytes)) got.push([view.getUint32(0, true), view.getInt32(4, true), view.getInt32(8, true)]);
  const want = [[1, 1600, 1000], [2, 10, 20], [1, 800, 600], [4, 10, 20]];
  if (JSON.stringify(got) !== JSON.stringify(want)) throw new Error(`off-screen events ${JSON.stringify(got)}, not ${JSON.stringify(want)}`);
  const state = new Float64Array(18); s.ng_surface_state(state);
  if (state[1] !== 0 || state[15] !== 0) throw new Error("the off-screen window became visible");
}
// Window edge and corner drags (issue 424): every edge and corner resizes, corners in
// both directions, the bottom or the side opposite the drag stays put, the minimum size
// holds, and the title bar buttons and the page keep their clicks.
function resize() {
  const lib = Deno.dlopen(libraryPath(), {
    ng_create_offscreen: { parameters: ["u32", "u32", "f64"], result: "pointer" },
    ng_test_mouse: { parameters: ["u32", "f64", "f64"], result: "void" },
    ng_test_window_frame: { parameters: ["buffer"], result: "void" },
    ng_next_event: { parameters: ["buffer"], result: "i32" },
    ng_pump: { parameters: [], result: "void" },
  });
  const s = lib.symbols, out = new Float64Array(6), bytes = new Uint8Array(16);
  if (!s.ng_create_offscreen(800, 500, 2)) throw new Error("no off-screen window");
  const frame = () => { s.ng_test_window_frame(out); return { x: out[0], y: out[1], w: out[2], h: out[3], hover: out[4], drag: out[5] }; };
  s.ng_pump(); while (s.ng_next_event(bytes));
  // [name, press point from the frame, drag, edges, frame after]
  type F = { x: number; y: number; w: number; h: number };
  const cases: [string, (f: F) => [number, number], [number, number], number, (f: F) => F][] = [
    ["bottom-right corner", (f) => [f.x + f.w - 8, f.y + 2], [40, -30], 6, (f) => ({ x: f.x, y: f.y - 30, w: f.w + 40, h: f.h + 30 })],
    ["bottom-left corner", (f) => [f.x + 3, f.y + 10], [-20, -10], 5, (f) => ({ x: f.x - 20, y: f.y - 10, w: f.w + 20, h: f.h + 10 })],
    ["top-left corner", (f) => [f.x + 2, f.y + f.h - 2], [-15, 25], 9, (f) => ({ x: f.x - 15, y: f.y, w: f.w + 15, h: f.h + 25 })],
    ["top-right corner", (f) => [f.x + f.w - 2, f.y + f.h - 10], [-50, -40], 10, (f) => ({ x: f.x, y: f.y, w: f.w - 50, h: f.h - 40 })],
    ["top edge", (f) => [f.x + f.w / 2, f.y + f.h - 2], [7, 30], 8, (f) => ({ ...f, h: f.h + 30 })],
    ["left edge", (f) => [f.x - 3, f.y + f.h / 2], [10, 9], 1, (f) => ({ ...f, x: f.x + 10, w: f.w - 10 })],
    ["right edge", (f) => [f.x + f.w + 2, f.y + f.h / 2], [-5, 9], 2, (f) => ({ ...f, w: f.w - 5 })],
    ["bottom edge", (f) => [f.x + f.w / 2, f.y - 4], [9, 12], 4, (f) => ({ ...f, y: f.y + 12, h: f.h - 12 })],
  ];
  for (const [name, at, [dx, dy], edges, want] of cases) {
    const before = frame(), [px, py] = at(before);
    s.ng_test_mouse(5, px, py); s.ng_pump();
    if (frame().hover !== edges) throw new Error(`${name}: hover edges ${frame().hover}, not ${edges}`);
    s.ng_test_mouse(2, px, py); s.ng_pump();
    if (frame().drag !== edges) throw new Error(`${name}: drag edges ${frame().drag}, not ${edges}`);
    s.ng_test_mouse(3, px + dx / 2, py + dy / 2); s.ng_test_mouse(3, px + dx, py + dy); s.ng_test_mouse(4, px + dx, py + dy); s.ng_pump();
    const got = frame(), w = want(before);
    if (got.drag || [got.x - w.x, got.y - w.y, got.w - w.w, got.h - w.h].some((d) => Math.abs(d) > 0.5))
      throw new Error(`${name}: frame ${JSON.stringify(got)}, not ${JSON.stringify(w)}`);
  }
  // The minimum content size holds when a corner is dragged far inwards.
  let f = frame();
  s.ng_test_mouse(2, f.x + f.w - 2, f.y + 2); s.ng_test_mouse(3, f.x + f.w + -2000, f.y + 2000); s.ng_test_mouse(4, f.x - 2000, f.y + 2000); s.ng_pump();
  const small = frame();
  if (small.w < 192 || small.w > 200 || small.h < 128 || small.h > 170 || Math.abs(small.y + small.h - (f.y + f.h)) > 0.5 || small.x !== f.x)
    throw new Error(`minimum size not kept: ${JSON.stringify(small)}`);
  // In the title bar beside its buttons, and in the page: no resize zone, and a
  // press is left to AppKit and the page. (A window that is never shown gets no clicks
  // from AppKit, so here the press only must not start a resize.)
  f = frame();
  s.ng_test_mouse(5, f.x + 7 + 6, f.y + f.h - 14); s.ng_pump();
  const titleBar = frame().hover;
  s.ng_test_mouse(5, f.x + f.w / 2, f.y + f.h / 3); s.ng_pump();
  if (titleBar !== 0 || frame().hover !== 0) throw new Error(`resize zone in the title bar or the page: ${titleBar}, ${frame().hover}`);
  s.ng_test_mouse(2, f.x + f.w / 2, f.y + f.h / 3); s.ng_pump();
  const pressed = frame();
  s.ng_test_mouse(3, f.x + f.w / 2 + 30, f.y + f.h / 3 + 30); s.ng_test_mouse(4, f.x + f.w / 2 + 30, f.y + f.h / 3 + 30); s.ng_pump();
  const after = frame();
  if (pressed.drag || after.w !== f.w || after.h !== f.h || after.x !== f.x || after.y !== f.y)
    throw new Error(`a press in the page moved the window: ${JSON.stringify(after)}`);
}
if (import.meta.main) Deno.args[0] === "resize" ? resize() : Deno.args[0] === "offscreen" ? offscreen() : Deno.args[0] === "cancel" ? cancel() : flood();
else for (const [name, mode] of [["native input queue keeps every click, cancel and key", "flood"],
  ["native cancel stays distinct and ordered between clicks", "cancel"], ["off-screen window uses the same queue", "offscreen"], ["window edges and corners resize like a Mac window", "resize"]]) Deno.test(name, async () => {
  if (Deno.build.os !== "darwin") return;
  const run = await new Deno.Command(Deno.execPath(), {
    args: ["run", "--no-check", "--no-config", "--allow-read", "--allow-ffi", "--unstable-ffi", new URL(import.meta.url).pathname, mode],
    stdout: "piped", stderr: "piped",
  }).output();
  if (!run.success) throw new Error(new TextDecoder().decode(run.stderr));
});
