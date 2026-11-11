// https://github.com/danbri/factoidal-core/issues/374: page scripts have XMLHttpRequest and
// fetch, and only when the embedder turns the network on (web_api op 75, Net.Xhr.op: off
// answers -2, and then neither global is defined). The decisions are in
// formal/lean4/L4Factoidal/Net/PageFetch.lean and Net/Xhr.lean; the prelude holds the classes.
// Run with --allow-read.
import {strict as assert} from "node:assert";

Deno.test("issue 374: page scripts have fetch and XMLHttpRequest, off unless the embedder turns the network on",()=>{
  const prelude=Deno.readTextFileSync(new URL("../../../tools/wasmvm/quickjs/prelude.js",import.meta.url));
  assert.ok(/lazy\('XMLHttpRequest', makeXHR\)/.test(prelude),"XMLHttpRequest is not defined by the prelude");
  assert.ok(/lazy\('fetch',/.test(prelude),"fetch is not defined by the prelude");
  // Each network global asks the engine first, and is undefined when the network is off.
  for(const name of ["makeXHR = () => {","lazy('Headers', () => {","lazy('Response', () => {","lazy('fetch', () => {"]){
    const at=prelude.indexOf(name);
    assert.ok(at>=0,`missing ${name}`);
    assert.ok(/^\s*if \(apiCall\(75, \[\]\) !== '1'\) return undefined;/.test(prelude.slice(at+name.length,at+name.length+80)),
      `${name} does not ask the engine whether the network is on`);
  }
  const xhr=Deno.readTextFileSync(new URL("../../../formal/lean4/L4Factoidal/Net/Xhr.lean",import.meta.url));
  assert.ok(xhr.includes("if !s.enabled then (s, .error (-2)) else"),"Net.Xhr.op is not off by default");
});
