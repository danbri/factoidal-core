# foafnaut2525 demo pages

Test pages for the Lean engine, and the start page of `foafnaut`. `manifest.json`
lists each page and what the engine must do with it.

- `tools/build-demo-pages.py` writes the `.html` files from `source/`, the status note
  and `../svg-fixtures`. Do not edit them by hand.
- `tools/check-demo-pages.py WEB_RENDER_NATIVE` renders every page. `test.sh` runs both.
- A `.xml` page is its own source. It names a stylesheet with `<?xml-stylesheet?>`, and
  Lean runs it: `version` 1.x uses `XSLT/`, and 2.0, 3.0 and 4.0 use `XSLT4/`.
- A page marked `refused` is an expected failure with an open issue; the check fails
  when it starts to render.
- `source/foaf-graph.svg` comes from `native-webgpu-ui-darwin-arm64 --demo foafnaut
  --emit-svg`, and `source/solving-showcase.svg` from the macOS package. The interactive
  demos (spring network, vector playground, responsive layout) are Lean UI programs with
  their own event loop; they are not pages yet.
