# Lean hygiene ratchet for the browser engine

2026-11-11. Issue: https://github.com/danbri/factoidal-core/issues/390.

## Why

`tools/lean-hygiene-audit.py` reads source text in the directories it lists. The engine's
lab modules (`labs/demos/foafnaut/`) were not listed, and 29 `unsafe` definitions and 29
`@[implemented_by]` attributes went in without anyone seeing them. `#print axioms` does not
show them either: an `opaque` with `@[implemented_by]` is not an axiom. A text scan also
misses what it was not told to look at, and it can be skipped by not running it.

## What is checked, by what

`labs/demos/foafnaut/LabHygiene.lean` imports every module of the engine build
(`LAB_MODULES` in `build-web-render.sh`). Its command `#hygiene_counts` (meta code in
`CommandElabM`, no `unsafe`) walks each imported module's constants as Lean recorded them
(`env.header.moduleData`) and counts, for the lab modules and, separately, for the
`L4Factoidal.*` modules they import:

| count | what Lean records |
| --- | --- |
| `unsafe` | `ConstantInfo.isUnsafe`, except compiler-made names (`_unsafe_rec`, internal names) |
| `implemented_by` | the `implemented_by` attribute, except the one a `partial def` gets |
| `partial_def` | an `opaque` constant with a `_unsafe_rec` copy (what `partial def` makes; well-founded recursion also gets a `_unsafe_rec` but its constant is a definition, so it is not counted). Includes `partial def`s that `deriving` writes for nested inductives |
| `extern` | the `extern` attribute |
| `opaque` | `opaque` constants that are not `partial def` or `extern` (in the lab: `initialize` cells and `opaque` fronts of `implemented_by`) |
| `modules` | how many modules were read: a floor, so an empty walk fails |

It defines `counts` as a value. The theorem `lab_ratchet` states, by `decide`, that every
count is at most `baseline` (and `modules` at least). If a count rises, `LabHygiene.lean`
does not compile.

Baseline, measured on main 4078eafa2 (2026-11-10):

| part | modules | unsafe | implemented_by | partial def | extern | opaque |
| --- | --- | --- | --- | --- | --- | --- |
| lab | 50 | 29 | 29 | 1 | 0 | 37 |
| formal (engine closure) | 369 | 0 | 0 | 153 | 22 | 1 |

The lab's 37 opaque constants are its 18 `initialize` cells and 19 `opaque` declarations
that carry `@[implemented_by]`; its 1 `partial def` is `deriving Repr` on
`NativeSVG.DisplayNode`. The formal 153 is the engine's import closure, counted by Lean
(including derived ones); the Python audit's 163 is all of `formal/lean4`, counted by text.

## Wiring

- `build-web-render.sh` (native, Wasm and `--source-only`) compiles `LabHygiene.lean` right
  after the lab modules. It refuses to continue when the file is missing or does not import
  some `LAB_MODULES` entry, when Lean fails, or when no `HYGIENE_JSON` line comes out.
- The counts go to `.build/web-render/hygiene.json` (removed at the start of each run), and
  `web-render/write-witness.py` writes them into `source-witness.json` as
  `hygiene: {counts, commit, theorem: "lab_ratchet", module}`. It refuses to write a record
  without them.
- factoidal-builds (PR on branch `wip/hygiene-field`): the `foafnaut-engines` job copies the
  `hygiene` field to `meta/hygiene.json`; `publish.sh` does not publish a `foafnaut-web` set
  without it and puts it into that release's `build-info.json`.
- The module is checked, not linked: it adds no runtime code. It adds about 12 s to each
  engine build (loading the ~420 imported modules; 11.8 s measured on the development Mac, 2026-11-10).

## What is trusted

- The counting command (about 60 lines in `LabHygiene.lean`): that it reads the right
  modules and classifies declarations correctly. Its `modules` floor catches an empty walk.
- Lean's environment data: the `unsafe` flag, the `implemented_by` and `extern`
  attributes, and the shape `partial def` compiles to (Lean 4.33.1). A Lean upgrade that
  changes how `partial def` is compiled can change the counts; the build then fails or
  the numbers move, and either is visible.
- CI running the build: factoidal-builds runs `build-web-render.sh --wasm`, and publish
  refuses a `foafnaut-web` set whose record has no `hygiene` field.
- Lab files outside `LAB_MODULES` (tests, demos not in the engine) are not counted.

## How to lower a baseline

Remove the declarations, then lower the matching number in `baseline` in
`LabHygiene.lean` in the same commit. A lower count with an unchanged baseline still
passes; the `HYGIENE_JSON` line in the build log shows the new numbers. Raising a number
needs the owner.

## How failure shows

The build log shows the counts, then the theorem error, and the build stops:

```
HYGIENE_JSON {"lab":{"modules":50,"unsafe":30,"implemented_by":30,"partial_def":2,...},...}
labs/demos/foafnaut/LabHygiene.lean:180:2: error: Tactic `decide` proved that the proposition
  counts.lab.modules ≥ baseline.lab.modules ∧
    counts.lab.unsafeDecls ≤ baseline.lab.unsafeDecls ∧ ...
is false
```

Compare the `HYGIENE_JSON` line with `baseline` to see which count rose. A module missing
from the imports shows as
`LabHygiene.lean does not import WebConsole: the hygiene ratchet would not see it; build refused`.

## The Python audit

`tools/lean-hygiene-audit.py` still checks `formal/lean4` (`sorry`, user `axiom`,
`native_decide`, `unsafe`, `implemented_by`, the `partial def` baseline, `#print axioms`).
Its lab section is removed: the lab counts have one baseline, in `LabHygiene.lean`.
