// Deno tests of the Tor worker path (no network needed).
// deno test --unstable-worker-options --allow-read --allow-net labs/demos/foafnaut/tor-wasm/deno/tor.test.ts
// Expected failures (CLAUDE.md, "A stated shortfall is a failing test plus an open issue"): each
// FAILS today; when one passes the suite fails with "unexpected pass".
import { keySource } from "./tor-state.ts";

function xfail(issue: string, passed: boolean) {
  if (passed) throw new Error(`unexpected pass: make this a real test and close ${issue}`);
}

Deno.test("the module runs in a dedicated worker, apart from page scripts", async () => {
  const w = new Worker(new URL("tor-worker.ts", import.meta.url), {
    type: "module",
    deno: { permissions: { net: true, read: [new URL("../.build/web/", import.meta.url)], write: false, env: false, run: false, ffi: false, sys: false, import: false } },
  } as WorkerOptions);
  const reply = await new Promise<unknown>((resolve) => {
    w.onmessage = (e) => {
      if (e.data.ready) w.postMessage({ id: 1, op: "isolated" });
      else resolve(e.data.result);
    };
  });
  w.terminate();
  if (reply !== true) throw new Error(`isolated_context() in the worker: ${reply}`);
});

Deno.test("xfail: the state key comes from the macOS Keychain (https://github.com/danbri/factoidal-core/issues/1058)", () => {
  xfail("https://github.com/danbri/factoidal-core/issues/1058", keySource() === "macos-keychain");
});

Deno.test("xfail: Foafnaut sends page requests through Tor with --tor (https://github.com/danbri/factoidal-core/issues/1060)", async () => {
  const src = await Deno.readTextFile(new URL("../../run_html.ts", import.meta.url));
  xfail("https://github.com/danbri/factoidal-core/issues/1060", src.includes('"--tor"'));
});

Deno.test("xfail: a top-level navigation's wires carry the browser's cookies (https://github.com/danbri/factoidal-core/issues/1060)", async () => {
  // Net.Navigation makes every navigation wire with omitCredentials: no Cookie field is sent and no
  // Set-Cookie is stored. The case passes when Net/Navigation.lean takes a cookie jar.
  const src = await Deno.readTextFile(new URL("../../../../../formal/lean4/L4Factoidal/Net/Navigation.lean", import.meta.url));
  xfail("https://github.com/danbri/factoidal-core/issues/1060", !src.includes("omitCredentials := true"));
});
