// The Hub's copy of Textnaut's cell mapping, made from labs/demos/foafnaut/textnaut/grid.ts at
// build time (emit-grid.cjs). Not committed: grid.ts is the only source.
const { emitGrid } = require("./emit-grid.cjs");

module.exports = class {
  data() {
    return { permalink: "/web/hub/textnaut/grid.mjs", layout: false, eleventyExcludeFromCollections: true };
  }
  render() {
    return emitGrid();
  }
};
