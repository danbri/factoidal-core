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
if (import.meta.main) flood();
else Deno.test("native input queue keeps every click and key", async () => {
  if (Deno.build.os !== "darwin") return;
  const run = await new Deno.Command(Deno.execPath(), {
    args: ["run", "--no-check", "--no-config", "--allow-read", "--allow-ffi", "--unstable-ffi", new URL(import.meta.url).pathname],
    stdout: "piped", stderr: "piped",
  }).output();
  if (!run.success) throw new Error(new TextDecoder().decode(run.stderr));
});
