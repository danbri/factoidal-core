# QT4 harness recursion audit classification

Date: 2026-10-30. Base: `108139c94a2fa69bd9c082e0acc6e6c1aba90eb9`.
Tracking: https://github.com/danbri/factoidal/issues/1101 (QT4 integration).

## Failure and classification

The [core corpus job](https://github.com/danbri/factoidal-core/actions/runs/40968839816/job/123780141051)
built the library, proofs, guards and QT4 runner, and passed hygiene and
resource-base regressions. It failed the compiled recursion gate on five
previously unlisted `Harness.Qt4Run` declarations. This is a deterministic
audit inventory failure, not a failed XML assertion or infrastructure flake.
The workflow now builds `l4qt4` before that gate, so the harness C is audited
alongside library C. Package-build success does not establish coverage of
the same compiled-file inventory.

The five declarations qualify for the existing policy marker `(b)`:
recursion follows document or query/assertion nesting. The audit labels them
`length` from the signature text; source and generated C show tree-depth
recursion through child-map callbacks. Sibling iteration uses the core
map/mapM loops. Each recursive traversal uses predecessor fuel.

| Declaration | Recursion follows | Entry fuel and call site |
| --- | --- | --- |
| `checkAssert` | Nested any-of/all-of/not assertions | 100 in `runSet` |
| `fixXml` | Catalog XML child elements | 100000 in `runSet` |
| `innerXml` | Nested expected-XML elements | 1000 in `fixXml` |
| `resolveXmlFiles` | Result/assertion XML children | 100 in `runSet` |
| `serNode` | Result document/element children | 100000 in `serSeq` |

These are semantic-depth fuel limits, **not proofs that the C stack is safe
at arbitrary depth or at the maximum budgets**. The native recursive call
cycles remain visible. `fixXml` can start a separately bounded `innerXml`
traversal; its own entry budget does not describe every helper stack frame.
No stack-safety or tail-recursion claim is made for these declarations.

Exactly five entries were added to `tools/lean-tail-recursion-allow.txt`,
with individual reasons, budgets and links to this note and the issue.
No wildcard, runtime implementation, budget, fixture, exclusion, gate
logic, gate order or workflow changed. Existing nested assertion/XML
controls were reused; no tests that mirror unchanged implementation were
added.

## Verification

The named build ran with `formal/lean4` as its explicit working directory,
under the shared build lock:

- `lake build l4qt4`: passed, 373 jobs.
- `tests/qt4-resource-base/run.sh`: 12 pass, 0 fail, 0 unsupported (out of 12).
- Existing XQuery `fn-transform`: 132 pass, 4 fail, 1 unsupported (out of 137).
  Its nested assertion groups and XML output assertions remain visible.
- Existing XQuery `fn-parse-xml`: 49 pass, 5 fail, 3 unsupported (out of 57).
  The complete result log is byte-identical to the supplied frozen PR270
  runner, SHA256 `61afcea1287811c2ab5fa800de96c9c3195cd56f20cb08c76cb732b2f9b9eef4`.
  Existing failures and unsupported cases were not recategorized.

The compiled gate used a correctly rooted view containing only the freshly
built `Harness/Qt4Run.c`, symlinked to this checkout's generated C:

```sh
python3 tools/lean-tail-recursion-audit.py --gate \
  --ir-dir /private/tmp/qt4-harness-audit-ir \
  --json /private/tmp/qt4-harness-audit.json
```

With the original allowlist, this same C reproduces exactly the five CI
findings and exits 1. With the five classifications, the recursion gate and
its chained csimp-reach gate both pass, exit 0. The recursion scan reads one
C module and 432 function definitions; no declaration is hidden from it.
This is targeted generated-C validation, not a full local library build or
a substitute for the next clean core workflow.

Evidence logs are `/private/tmp/qt4-harness-audit-build.log`,
`/private/tmp/qt4-harness-audit-red.log`,
`/private/tmp/qt4-harness-audit-green.log`,
`/private/tmp/qt4-harness-resource-controls.log`,
`/private/tmp/qt4-harness-transform-controls.log`,
`/private/tmp/qt4-harness-xml-controls.log`, and
`/private/tmp/qt4-harness-xml-frozen-controls.log`.
