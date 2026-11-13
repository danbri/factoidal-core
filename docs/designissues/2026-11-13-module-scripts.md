# Module scripts in the built-in engine (2026-11-13)

Status: stage 1 (static modules) on branch `wip/esm-scripts`. Engine: BubblePopJS. QuickJS-NG in
WasmVM does not run module scripts yet (see "Open").

## What a page gets

- `<script type="module">`, inline and with `src`: run after the classic scripts, in document
  order, before `DOMContentLoaded` (deferred). `async` module scripts run in the same pass.
  `document.currentScript` is null while they run.
- Static `import` and `export` in all their forms (named, default, namespace, renames, string
  export names, `export * from`, `export * as ns from`, re-exports of imports).
- Live bindings, the temporal dead zone across cycles, function declarations hoisted across
  cycles, a module evaluated once per document, an evaluation error kept and given again to
  later importers.
- `import.meta.url`.
- A classic script with `nomodule` is not run.
- External module scripts fire `load` after they run; a failed fetch anywhere in the graph
  fires `error` at the element; a parse error or a bare specifier is reported at the window
  (SyntaxError, TypeError).

## Where each decision is

| Decision | Where |
|---|---|
| Module grammar, early errors (duplicate exports, undeclared local exports, imports clashing with declarations) | `JS/Parser.lean`, `parseModule` |
| ResolveExport, GetExportedNames, namespace names, link errors, evaluation order | `JS/Modules.lean` (pure functions of the graph) |
| Instantiation, linking, evaluation on the heap | `JS/Modules.lean`, `runModuleGraph` |
| Which elements are module scripts; document base URL | `WasmVM/Hosts/LeanJSModules.lean`, `scriptsOf`, `baseOf` |
| Fetch mode (CORS), credentials, redirects, address policy | `Net.PageFetch.Transfer` (shared with `fetch` and XHR) through `LeanJSModules.fetchModule` |
| Status and MIME type check, UTF-8 decode | `LeanJSModules.moduleText` |
| Specifier resolution, module map (per document, keyed by request URL) | `LeanJSModules.resolveSpecifier`, `visit` |
| What a script does: run, `error`, report | `LeanJSModules.outcome`, `LeanJS.Session.runModule` |

The hosts are not changed: a module fetch is a `netSync` request, the same wire a sync
XMLHttpRequest uses, and every host answers it already.

## How a module runs

A module is a generator function whose closure environment is an Object Environment Record
over the module's imports object, with the global environment above:

```
function* () { %L = { get x() { return x }, ... }; yield; ...module statements... }
```

Calling it is FunctionDeclarationInstantiation (functions hoisted, `let`/`const`/classes in
their TDZ). Running it to the `yield` stores the getters of its exported bindings. Linking puts
on each imports object one accessor per imported name, the exporter's getter, or the namespace
object for `import * as`. Evaluation resumes the generators in post-order. Module code is
resolved by `Resolve.script` as a function at the top level: its own names get slots; free
names are looked up through the imports object, then the global object. The register machine's
global reads check the environment chain first (`vmGlobalHit` calls `findEnv`), so compiled
loops in module code see imports.

`%L` and `%meta` are not identifiers: module code cannot name the imports object's own entries,
and the imports object is never given to page code.

## Fetching

No script runs until every graph is there. The loader walks the graphs in a fixed order; each
request the host has not answered yet ends the start with `netSync`, and the start is made again
with the answer appended. A redo parses the HTML and the modules already fetched again, so a
graph of N modules costs N round trips and about N²/2 module parses (see "Open"). The answers
the module fetches used come first in the sync cache; the ones after are the page's sync
XMLHttpRequests.

A page with no module script makes no request and does no module work: `scriptSources` already
walks the script records, and `load` is called only when one is a module
(`LeanJSModules.load_none`).

## Proved, tested, assumed

Proved (Lean theorems, no `sorry`):

- `JS.resolveExport_local`, `resolveExport_seen` (a cycle of indirect exports ends),
  `resolveExport_default` (`default` is never found through `export *`).
- `LeanJSModules.moduleText_ok`: a response is run as a module only with an ok status and a
  JavaScript MIME type.
- `LeanJSModules.load_none`: a page with no module script asks for nothing.
- The CORS rules are `Net.PageFetch`'s, with its theorems (`deliver_cross_origin_needs_cors`,
  `plan_send_allowed`, `onAnswer_reach`, ...): a module fetch is a `Transfer` driven by `plan`
  and `onAnswer` only.

Tested: `JS/ModuleTests.lean` (`#guard`s: imports, live bindings, defaults, namespaces, star
exports and their ambiguity, cycles, TDZ, strictness, `this`, read-only imports, evaluate-once,
kept errors, `import.meta`, loops over imports, early errors). WPT: see the branch's hand-back.

Assumed: the host makes the request it is told and reports the response faithfully (as for
`fetch`).

## Differences from the standards (open)

- Top-level `await` is not supported (a SyntaxError).
- Dynamic `import()` parses (in classic and module code) but is not implemented: calling it is
  a ReferenceError.
- Import maps are not supported: a bare specifier is a TypeError.
- JSON and CSS modules (`with { type: ... }`) are a SyntaxError.
- Module workers, module scripts in frames, `modulepreload`: not supported.
- Namespace object properties are accessors, where ECMA-262 has data properties; namespace keys
  are sorted by code point, not by UTF-16 code unit.
- `async` module scripts run in document order with the deferred ones.
- `integrity`, `referrerpolicy`, `fetchpriority` and CSP are not checked for module scripts.
- Fetch: one request per redo; the module parses are redone on each redo. A cache of parsed
  modules in the script session would remove the N² parses.
- QuickJS-NG in WasmVM (the Hub's default engine) reports each module script as not run.
