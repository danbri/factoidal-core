// about:foafnaut and --version (issue 416), as the engine writes them (WebAbout.lean): the
// engine's own build facts, the host's report in its own section, escaped, and a line when
// the host's record disagrees. Needs the built engine (test.sh runs it with native_html_test.ts).
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";

const engine=await loadHTML();
const facts=engine.engineBuild();

Deno.test("the engine knows its own release, commit and build time",()=>{
  assert.match(facts.version,/^\d+\.\d+\.\d+/);
  assert.match(facts.commit,/^[0-9a-f]{40}$/);
  assert.match(facts.builtAt,/^\d{4}-\d\d-\d\dT/);
  assert.match(facts.line,new RegExp(`^foafnaut ${facts.version.replaceAll(".","\\.")} \\((release|development) build\\), commit ${facts.commit}`));
  assert.equal(facts.mismatch,undefined,"no host record: nothing to disagree with");
  assert.equal(engine.engineBuild({commit:facts.commit.slice(0,9),version:facts.version}).mismatch,undefined);
  assert.match(engine.engineBuild({commit:"0000000",version:facts.version}).mismatch??"",/does not match this engine/);
});

Deno.test("about:foafnaut: the engine's facts, the host's report escaped and labelled, the specifications",()=>{
  const page=engine.aboutPage({rows:[["Runtime","<script>x</script>"]],commit:facts.commit.slice(0,9),version:facts.version});
  assert(page.includes(`<h1>Foafnaut ${facts.version}</h1>`));
  assert(page.includes(facts.commit));
  assert(page.includes("Reported by the desktop program"));
  assert(page.includes("&lt;script&gt;x&lt;/script&gt;")&&!page.includes("<script>x"),"host text is escaped");
  assert(!page.includes("does not match"));
  assert.match(engine.aboutPage({commit:"0000000"}),/does not match this engine/);
  assert.match(page,/Implemented in part/);
  const names=[...page.matchAll(/<li><a href="(https:[^"]+)">([^<]+)<\/a>/g)].map(m=>m[2]);
  for(const name of ["CSS","DOM","HTML","JSON-LD","OWL","RDF","SHACL","SPARQL","SVG","Turtle","URL","WebAssembly","WebGPU","WGSL","Encoding"])
    assert(names.includes(name),name);
  for(const name of ["DOM","HTML","URL","Encoding"])assert.match(page,new RegExp(`>${name}</a> <span class="body">\\(WHATWG\\)`));
  assert(!/honest|Lean/.test(page),"user-facing text says the built-in engine");
});
