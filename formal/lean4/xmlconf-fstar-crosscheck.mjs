// Cross-check harness: run the F*-extracted XML parser (via the npm
// bundle's xmlWellformed) over the same file list the Lean
// `xmlconf-probe` reads, so the two ports can be compared file by file
// rather than only by totals.
//
// Usage:  ls <dir>/*.xml | node xmlconf-fstar-crosscheck.mjs
//         (FACTOIDAL_FSTAR_ENTRY names the F* npm-entry bundle; default
//         docs/fstar-extracted/factoidal-npm-entry.js, which
//         tools/fetch-builds.sh --set web installs)
// Output: one `WF <path>` / `NWF <path>` line per file, matching the
// Lean probe's verdict column.
//
// Since @factoidal/core 0.9.0 the package's main entry is the Lean engine,
// so the F* bundle is loaded by path and driven through the package's
// typed layer (npm/factoidal/lib/api.mjs), as tests/engine-compare/ does.
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { buildApi } from "../../npm/factoidal/lib/api.mjs";

const require = createRequire(import.meta.url);
const entryPath = process.env.FACTOIDAL_FSTAR_ENTRY ??
  fileURLToPath(new URL("../../docs/fstar-extracted/factoidal-npm-entry.js", import.meta.url));
const entryModule = require(entryPath);
const abi = entryModule.factoidalNpmEntry ?? globalThis.factoidalNpmEntry;
const { xmlWellformed } = buildApi({ engineName: "fstar-npm-entry", loadEntry: () => abi });

const paths = readFileSync(0, "utf8")
  .split("\n")
  .map((p) => p.trim())
  .filter((p) => p.length > 0);

let wf = 0;
for (const p of paths) {
  let ok = false;
  try {
    // Read as UTF-8, exactly as the Lean probe does, so an encoding
    // difference cannot masquerade as a parser difference.
    ok = await xmlWellformed(readFileSync(p, "utf8"));
  } catch {
    ok = false;
  }
  if (ok) wf++;
  console.log(`${ok ? "WF " : "NWF"} ${p}`);
}
console.error(
  `summary: ${wf} accepted as well-formed, ${paths.length - wf} rejected as malformed (out of ${paths.length} files)`,
);
