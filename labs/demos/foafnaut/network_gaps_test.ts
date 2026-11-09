// Expected failure of https://github.com/danbri/factoidal-core/issues/374: page scripts have no
// network access. The acceptance page is pages/search.html. When this test fails, make it assert
// the correct behaviour and update the issue in the same landing.
// Run with --allow-read.
import {strict as assert} from "node:assert";

Deno.test("expected failure, factoidal-core issue 374: page scripts have no fetch or XMLHttpRequest",()=>{
  const prelude=Deno.readTextFileSync(new URL("../../../tools/wasmvm/quickjs/prelude.js",import.meta.url));
  assert.ok(!/\bXMLHttpRequest\b/.test(prelude)&&!/\bfetch\s*[=(]/.test(prelude),
    "expected failure of https://github.com/danbri/factoidal-core/issues/374 no longer fails: make this test assert the correct result and update the issue");
});
