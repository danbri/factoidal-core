// One source for Textnaut's cell mapping: labs/demos/foafnaut/textnaut/grid.ts. The terminal
// program imports the TypeScript file; the Hub's Textnaut page and notebook import the same file
// with its types removed, made here at build time (grid.11ty.js) and by the local server
// (tests/hub/hub-dev-server.mjs). Nothing is changed but the types: Node's type stripping replaces
// each type annotation with spaces, so every line and column of the program is where it is in
// grid.ts. tests/hub/textnaut_grid_shared_test.mjs checks that both hosts use this file.
const fs = require("fs");
const path = require("path");

const GRID_SOURCE = path.join(__dirname, "..", "..", "..", "..", "labs", "demos", "foafnaut", "textnaut", "grid.ts");
const HEADER = "// Generated from labs/demos/foafnaut/textnaut/grid.ts by docs/web/hub/textnaut/emit-grid.cjs: do not edit.\n";

function emitGrid(source = fs.readFileSync(GRID_SOURCE, "utf8")) {
  const { stripTypeScriptTypes } = require("node:module");
  if (typeof stripTypeScriptTypes !== "function") {
    throw new Error("emit-grid: this Node has no module.stripTypeScriptTypes (Node 22.13 or later is needed to build the Hub's Textnaut pages)");
  }
  return HEADER + stripTypeScriptTypes(source, { mode: "strip" });
}

module.exports = { emitGrid, GRID_SOURCE, HEADER };
