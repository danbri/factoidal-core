# Selected Shiki syntax highlighting

Shiki **3.13.0**, bundled with esbuild **0.25.11**. `package-lock.json`
pins all build inputs and npm integrity hashes. `entry.mjs` selects the
GitHub light/dark themes, JavaScript regex engine (no WASM sidecar), and
JavaScript, TypeScript, JSON, XML, HTML, CSS, SQL, Turtle, SPARQL, Lean,
Bash, Markdown and YAML grammars. Unsupported languages display as text.
The forgiving regex engine may omit unsupported syntax distinctions;
highlighting is presentation only, never a parser or validator.

The upstream packages come from https://github.com/shikijs/shiki and the
npm registry tarballs recorded in the lockfile. `manifest.json` records
bundled packages, their declared MIT licenses, and the bundle SHA-256.
`licenses/` preserves upstream license/notice files, including the grammar
package's license. The theme is scoped to code; no Primer CSS is loaded.

Run `bash third_party/shiki/build.sh` to reproduce (requires npm network
access). The checked-in bundle follows the existing vendored Observable
bundle precedent. Normal Eleventy/Pages builds import it directly and
remain compatible with `third_party/eleventy/install.sh docs`: no new npm
runtime dependencies or online build step were added. Node 20 is supported.

The browser and static Markdown renderer use these same bytes. Live output
keeps an exact plain-text fallback. Copy always copies original input;
Wrap changes only CSS. A Formatted/Raw switch appears only when the caller
supplies a second representation; this code does no semantic formatting.

## Shared live output API

Load `docs/web/hub/assets/code-output.mjs` and its sibling CSS (the site
copies these paths unchanged). The module registers `<factoidal-code-output>`:

```js
const output = document.createElement('factoidal-code-output');
await output.setValue(originalText, { language: 'xml', formattedText: engineFormattedText });
```

`formattedText` is optional. `setValue` installs plain text immediately and
returns a promise for highlighting. It refuses non-string input. Original
text remains the Copy payload even while viewing the separate formatted
representation. Highlighting is installed only if browser `textContent`
exactly equals the input, including trailing blank lines; otherwise the
plain-text fallback remains. Code output uses bounded scrolling; Wrap only
changes whitespace presentation. Hub `pretty(text, { language: 'xml' })`
uses the same component, while existing tables and non-string values keep
their existing presentation.

`enhanceCodeBlocks(root)` adds controls to existing `pre > code` elements
without replacing their language classes, cell flags or executable source.
The hub calls it after mounting new cells and after source edits. Controls
are inside the same folded source section and hide during source editing.

Validation: `node --test tests/hub/code_highlighting_test.mjs`; browser:
`node tests/web-demos/code_output_check.mjs /path/to/playwright-core/index.mjs`.
The browser check uses installed Chrome and an ephemeral localhost server;
it checks the actual hub `pretty()` source as well as the shared component.
