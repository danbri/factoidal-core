# XProc 3.1 implementation progress — 2026-10-28

Scope: CODEX-BRIEF.md. No commits or pushes. Changes restricted to XProc31,
lakefile, this file and docs/designissues.

## First implementation milestone

Added document/property model, XPath option/AVT helpers, input bindings,
compound step runtime, standard atomic step dispatch, isolated upstream test
runner, static cycle detection and Dataflow lowering/theorems.

The runner path in the brief is `formal/lean4/Harness/Qt4Run.lean` (without
`L4Factoidal`). All named engine dependencies are present in this checkout.

Build: `ulimit -s 65520; export PATH=$HOME/.elan/bin:$PATH; lake build L4Factoidal.XProc31.Core`
with working directory `formal/lean4` passed. Atomic/runtime/runner integration
is in progress. No suite score yet.

Open: complete runtime integration, measure all 3363 upstream test documents,
fix failures, extend unsupported steps and static checks. Bridge distinguishes
graph evaluator equality from an unproved XML-reader interpretation; the
pure for-each law does not yet prove the runtime IO loop.

Tracking: https://github.com/danbri/factoidal/issues/1129 (checked pipelines and XProc).

## Full suite measurements

All commands run from `formal/lean4` after `lake build l4xproc`:

`.lake/build/bin/l4xproc --list-fails --list-unsupported`

- First run: 129 pass, 1821 fail, 1413 unsupported, total 3363.
- Second run: 466 pass, 1439 fail, 1458 unsupported, total 3363.
- Third run: 750 pass, 782 fail, 1831 unsupported, total 3363.

Each test runs in a child process with a five-second deadline. Logs are
`/tmp/xproc-suite-1.log`, `/tmp/xproc-suite-2.log`, `/tmp/xproc-suite-3.log`.
Runner corrections: Schematron XML default namespaces do not define the
XPath default element namespace; fixture paths are absolute file URIs.
The first score therefore included oracle defects as well as runtime defects.

Current unmeasured additions: nested/quoted/comment-aware AVTs, imports,
forward-reference scheduling, use-when pruning, XSLT/XQuery error mappings,
more atomic steps and JSON values. Unsupported step admission now precedes
input loading, so an absent archive step cannot fail while trying to parse
its binary input as XML. General document properties, binary content and
several compound/static checks remain incomplete.

### Shared module fix: XSLT host function fallback

`formal/lean4/L4Factoidal/XSLT4/Transform.lean`: `mkHost` now delegates an
unknown host function to `base.host q k`. The previous fallback returned
`none` and dropped the XProc default collection hook. XSLT functions still
have precedence. With the default empty host the result is unchanged.
`XProc31/Atomic.lean` has a regression that calls a named XSLT template and
checks `count(collection()) = 2` for two source documents. Build result is
recorded with the next Atomic milestone.

Atomic validation (2026-10-28): from `formal/lean4/`,
`ulimit -s 65520; export PATH=$HOME/.elan/bin:$PATH; lake build L4Factoidal.XProc31.Atomic`
completed with exit 0 (112 jobs). The subsequent QName-prefix preservation
change passed `lake env lean L4Factoidal/XProc31/Atomic.lean`, exit 0.
The guards cover count, delete, rename, add-attribute, collection through
XSLT, and rejection of an empty-matching text replacement pattern. These
local guards are not included in the upstream suite score.

### XPath host functions (2026-10-28)

`XProc31/Functions.lean` supplies POSIX `p:urify`, `p:system-property` and
`p:step-available`. Availability comes from a caller-supplied predicate;
lexical QNames and EQNames resolve in the XPath static namespace context.
The episode identifier is a caller parameter. Windows-specific `urify`
fixtures are platform requirements and must be reported unsupported on POSIX.

Validation from `formal/lean4/`: `lake build L4Factoidal.XProc31.Functions`
exited 0. A temporary Lean harness, `/tmp/XProcUrifyCheck.lean`, reads the
actual upstream `nw-urify-non-windows*`, `nw-urify-any*`, and `nw-urify-path*`
files, evaluates their expressions through the host function, checks their
assertions and expected errors: `lake env lean --run /tmp/XProcUrifyCheck.lean`
reported 133 pass / 0 fail. This is a function-only check; the full runner
score is recorded separately after runtime integration.

## Runtime and proof integration milestone

Fourth full run: 910 pass, 683 fail, 1770 unsupported, total 3363.
Fifth full run: 1145 pass, 532 fail, 1686 unsupported, total 3363.
Command for both, from `formal/lean4` after successful `lake build l4xproc`:
`.lake/build/bin/l4xproc --list-fails --list-unsupported`.
Logs: `/tmp/xproc-suite-4.log`, `/tmp/xproc-suite-5.log`.

Viewport subset after binding and fragment fixes:
`.lake/build/bin/l4xproc --filter viewport --list-fails --list-unsupported`
reports 46 pass, 0 fail, 2 unsupported, total 48.

Runtime now calls `Sequence.forEachIO`; the actual IO action has mapM,
ordered concatenation and short-circuit theorems imported by Bridge.
The earlier pure-only for-each boundary is resolved. XML reader correctness
and full runtime-to-graph equivalence remain unproved.

Added standalone pipeline CLI and `Regression.lean` end-to-end checks
(the new regression file is pending its first run while document-property
migration is in progress). Design/status record:
`docs/designissues/2026-10-28-xproc31-processor.md`.
