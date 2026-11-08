// The window library keeps every discrete input event, in order, under a flood.
// Moves keep only the newest position; scroll steps add up.
import { libraryPath } from "./native_window.ts";

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
      s.ng_test_event(5, i, 0); s.ng_test_event(4, i, 0); s.ng_test_event(11, 1, 0); s.ng_test_event(11, 2, 0);
    }
    const bytes = new Uint8Array(16), view = new DataView(bytes.buffer), seen: Record<number, number> = {};
    let downs = 0, keys = 0, scroll = 0, newestMove = true;
    while (s.ng_next_event(bytes)) {
      const kind = view.getUint32(0, true), a = view.getInt32(4, true);
      seen[kind] = (seen[kind] ?? 0) + 1;
      if (kind === 2 && a !== downs++) throw new Error(`click ${a} out of order`);
      if (kind === 5 && a !== keys++) throw new Error(`key ${a} out of order`);
      if (kind === 3 && view.getInt32(8, true) !== 2) newestMove = false;
      if (kind === 11) scroll += a;
    }
    if (downs !== N || keys !== N || seen[4] !== N) throw new Error(`lost events: ${JSON.stringify(seen)}`);
    if (!newestMove || scroll !== 3 * N || s.ng_events_dropped() !== 0) throw new Error("coalescing changed input");
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
if (import.meta.main) Deno.args[0] === "offscreen" ? offscreen() : flood();
else for (const [name, mode] of [["native input queue keeps every click and key", "flood"], ["off-screen window uses the same queue", "offscreen"]]) Deno.test(name, async () => {
  if (Deno.build.os !== "darwin") return;
  const run = await new Deno.Command(Deno.execPath(), {
    args: ["run", "--no-check", "--no-config", "--allow-read", "--allow-ffi", "--unstable-ffi", new URL(import.meta.url).pathname, mode],
    stdout: "piped", stderr: "piped",
  }).output();
  if (!run.success) throw new Error(new TextDecoder().decode(run.stderr));
});
