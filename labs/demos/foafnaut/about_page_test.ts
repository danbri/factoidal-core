// about:foafnaut and --version (issue 416): the release number and commit of the build
// record, and the specifications list. No engine and no window.
import {strict as assert} from "node:assert";
import {aboutHTML,releaseURL,SPECS,sourceVersion,versionLine} from "./about_page.ts";

const record={commit:"abc123def",commitFull:"abc123def4567890abc123def4567890abc12345",dirty:false,builtAt:"2026-11-11T18:00:00Z",version:"0.36.0",release:true};

Deno.test("about:foafnaut shows the release number, the kind of build and the commit",()=>{
  const page=aboutHTML(record,[["Platform","darwin aarch64"]]);
  assert.match(page,/<h1>Foafnaut 0\.36\.0<\/h1>/);
  assert.match(page,/0\.36\.0 \(release build\)/);
  assert.match(page,/abc123def/);
  assert.match(page,/2026-11-11T18:00:00Z \(/,"build time in UTC and local time");
  assert(page.includes(releaseURL(record)!),"link to the release on factoidal-builds");
  assert.deepEqual(releaseURL(record),"https://github.com/danbri/factoidal-builds/releases/tag/build-abc123def456-foafnaut-darwin-arm64");
  assert.match(aboutHTML({...record,release:false,dirty:true},[]),/0\.36\.0 \(development build\).*with uncommitted changes/s);
});

Deno.test("about:foafnaut lists the specifications A to Z, implemented in part, each linked",()=>{
  const page=aboutHTML(record,[]);
  assert.match(page,/Implemented in part/);
  const names=[...page.matchAll(/<li><a href="(https:[^"]+)">([^<]+)<\/a>/g)].map(m=>m[2]);
  assert.deepEqual(names.length,SPECS.length);
  assert.deepEqual(names,[...names].sort((a,b)=>a.localeCompare(b,"en",{sensitivity:"base"})));
  for(const name of ["CSS","DOM","HTML","JSON-LD","OWL","RDF","SHACL","SPARQL","SVG","Turtle","URL","WebAssembly","WebGPU","WGSL","Encoding"])
    assert(names.includes(name),name);
  // WHATWG standards say so.
  for(const name of ["DOM","HTML","URL","Encoding"])assert.match(page,new RegExp(`>${name}</a> <span class="body">\\(WHATWG\\)`));
  assert.deepEqual(new Set(names).size,names.length,"no name twice");
  assert(!/honest|Lean/.test(page),"user-facing text says the built-in engine");
});

Deno.test("--version says the release, the kind of build and the commit",async()=>{
  assert.deepEqual(versionLine(record),"foafnaut 0.36.0 (release build), commit abc123def, built 2026-11-11T18:00:00Z");
  // The build check in build-executables.sh matches "foafnaut VERSION ...commit COMMIT".
  assert.match(versionLine({...record,release:false}),/^foafnaut 0\.36\.0 .*commit abc123def/);
  const version=await sourceVersion();
  assert.match(version??"",/^\d+\.\d+\.\d+/,"run from source: the package's version");
  assert.deepEqual(versionLine({},version),`foafnaut ${version} (run from source, no build record)`);
});
