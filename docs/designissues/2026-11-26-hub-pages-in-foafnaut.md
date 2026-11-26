# Hub conformance page and its neighbours in Foafnaut

Tracking: https://github.com/danbri/factoidal-core/issues/1161 (Hub conformance page and
neighbours in Foafnaut).

Owner, 2026-11-26, verbatim: "A cute milestone would be when we can actually see this page and
its neighbours in our own browser."

Pages: https://danbri.github.io/factoidal/web/hub/conformance/ (Conformance),
https://danbri.github.io/factoidal/web/hub/render-scores/ (Rendering scores),
https://danbri.github.io/factoidal/web/hub/specs/ (Data and documents),
https://danbri.github.io/factoidal/web/hub/ (Hub home).

## 1. Defects found, in the order the pages meet them

1. A page whose only scripts are module scripts got no script session at load.
   `WebDocument.inspect` lists the classic scripts only (the session fetches modules itself,
   `LeanJSModules`), and the host (`native_html_document.ts`) started a session only when that
   list had a script. In the window, `startScripts` then started one at the first press or key,
   so the module ran late; in Textnaut it never ran. Repair: `inspect` gives `modules`, the
   number of module scripts (0 with scripting off), and the host starts a session when it is
   more than 0. Conformance and Data and documents are module-only pages.
2. `[D, H] = await Promise.all(...)` in `mount()` (`docs/web/hub/conformance/conformance.mjs`)
   gave "SyntaxError: yield in this position is not supported". The page's `catch` printed that
   message in place of the data. Section 2.
3. `/[\240-\377]/` (Observable Plot, `plot.esm.js`) gave "range out of order in character
   class": the end of a class range had no Annex B legacy octal branch (B.1.2), only its start.
   Every page that imports Plot stopped at the parse of that module (Rendering scores, the Hub
   home).

## 2. How the generator machine handles `yield` and `await` inside an expression

An async function runs on the same machine as a generator: the parser reads `await e` as
`yield %await(e)`. The machine (`genEnter`, `genRun`, `genUnwind` in
`formal/lean4/L4Factoidal/JS/Interp.lean`) suspends only at statement level: a statement
whose whole value is a `yield` (`x = yield v`, `let x = yield v`, `return yield v`). Any
other statement with a `yield` goes to `genLift`, which asks `liftStmt` to move each `yield`
into a statement of its own before the statement (`liftE`): `f(await p)` becomes
`let %y0 = await p; f(%y0)`. Operands evaluated before the `yield` move into temporaries too,
so they are still evaluated first. A `yield` on one branch of `&&`, `||`, `??`, `?:` or of
`&&=`, `||=`, `??=` is put inside an `if`. When nothing can be lifted, `genUnsupported`
throws the SyntaxError above.

Added 2026-11-26: the value of a destructuring assignment, the substitutions of a tagged
template, the operand of `++` and `--`, `super[...]` keys, `super(...)` arguments, and the
logical assignments.

### Destructuring with a `yield` in its pattern

`[x = yield] = v`, `({a: o[yield]} = v)`, `let {b = await f()} = o`: the pattern's own steps
must stop at the `yield`, so `dstrLower` writes them as statements, in the order of §13.15.5.5
(IteratorDestructuringAssignmentEvaluation) and §13.15.5.6
(KeyedDestructuringAssignmentEvaluation):

- the value into a temporary (`%d` names, which source text cannot write);
- array pattern: GetIterator, then for each element the target's operands, IteratorStep (the
  record is marked done before the call, so a throw of `next`, `done` or `value` does not
  close it), the default when the value is `undefined`, PutValue; the rest element collects
  the remaining values. All inside `try`: the `catch` closes the iterator and ignores the
  errors of `return` (a throw completion), the `finally` closes it and checks the result (a
  normal or `return` completion: this is how `it.return()` on a suspended generator closes
  the pattern's iterator);
- object pattern: RequireObjectCoercible, then for each property the computed key, the
  target's operands, GetV, the default, PutValue; the rest property is CopyDataProperties
  without the keys already taken;
- a nested pattern with a `yield` is lowered in the same pass (its temporaries then cannot
  collide with the outer ones); one without a `yield` is evaluated as before.

The internal calls `%dstr(op, ...)` in `evalExpr` do the steps that have no source syntax:
`iter`, `next`, `close`, `closeQuiet`, `push`, `req`, `rest`, and `init`. A declaration
(`let`, `const`) initialises each name at its step with `init`, which sets the binding that
the declaration's scope made (in its TDZ until then), so a later default can read an earlier
name (`const {a = yield, b = a} = o`) and a `const` name stays read-only. A `var` name is
assigned. Each declarator of a declaration with several runs as a statement of its own.

Known differences: the callee and operands to the left of a lifted `yield` are evaluated after
the suspension when they are not moved to a temporary (a difference from §13.3.6 only when
they have side effects); a computed key is converted to a property key at GetV, not at once.
A `yield` inside an optional chain is still refused:
https://github.com/danbri/factoidal-core/issues/1167 (expected failure in
`JS/RegressionTests.lean`).

### Measured

Test262 at `4db99ac4dc89` (2026-11-24, tc39/test262 main; not the pinned commit of the
cloud runs), `leanjs test262 . test/language/*`, one mode (sloppy unless the file says
otherwise), 23,832 files: 22,751 pass before (`994dd4ad`), 22,800 after (`1afce5e8`). No
file went from pass to fail. The 24 files of
`expressions/assignment/dstr/*-yield-expr.js` and `*-rtrn-close*.js` that failed before
pass.

## 3. How to see a Hub page as Foafnaut sees it, on Linux

From `labs/demos/foafnaut`, with a native engine (`TEXTNAUT_NATIVE`, a `libweb-render.so`
from this checkout's `build-web-render.sh --native`, or the release set
`foafnaut-browser-linux-x86_64` of `danbri/factoidal-builds`):

```sh
deno run --no-prompt --allow-read --allow-ffi --allow-net --allow-env --allow-write \
  --import-map=textnaut/import_map.json textnaut/textnaut.ts --dump --verbose --width 100 URL
```

`--verbose` prints the page's console lines (`page:`) and one `settle:` line per script turn
(its network requests, its script fetches, its next timer). No `settle:` line means that no
script session started. Chrome's text for the same page: Playwright, `document.body.innerText`
after `networkidle`.
