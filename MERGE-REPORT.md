# Merge report — 2026-10-29

All eight conflicts are resolved and staged. No commit, push or network
command was run.

## Resolution

- `Harness/Qt4Run.lean`: combined imports, features, resource loading,
  file sandpits and XQuery Update query chains. Kept the inherited default
  namespace during serialization. Removed six stale Update namespace
  exclusions after they passed the merged XML assertion comparison.
- `XPath4/Eval.lean`: kept the branch's context diagnostic and closure
  behavior, plus updating-function checks and pending update lists.
- `XPath4/Parser.lean`: retained the type checks; accepts Update annotations.
- `XQuery4/Grammar.lean`: kept the branch's enclosing-namespace tracking
  through parser context, which supplies main's enclosing declarations;
  added revalidation and Update annotations.
- `XQuery4/Module.lean`: combined rich annotations, visibility, module
  context and lazy defaults with updating functions and revalidation.
- `XQuery4/Runtime.lean`: combined lazy function references with `fn:put`;
  preserved updating metadata through closure reconstruction.
- `third_party/testing/qt4tests/PROVENANCE.md`: retained both provenance entries.
- `tools/lean-tail-recursion-allow.txt`: retained the union of entries.

Lean paths above are relative to `formal/lean4/`. Also repaired the Update
entry point in `XQueryUpdate/{Grammar,Query,Static}.lean`: imported types,
function lookup, context type checks and resolved annotation QNames.
Five added regression guards pass during the build.
`docs/dataflow-inventory.md` merged without conflict; it was not regenerated.

## Build and checks

From `formal/lean4/`:

```sh
ulimit -s 65520
export PATH=$HOME/.elan/bin:$PATH
lake build l4qt4
```

Build passed (335 jobs). Log: `/private/tmp/m214-build-final.log`.
Only `l4qt4` was built. The module reachability gate and Lean hygiene audit
passed. Hygiene: 0 sorry, 0 user axioms, 0 native_decide, 0 unsafe;
163 partial definitions, unchanged from baseline. The hygiene audit did not
check imported axioms. Diff whitespace checks pass for the resolution files.
Vendored incoming fixtures have existing whitespace findings and are unchanged.

## Measurements

Commands run from `formal/lean4/`, with stack limit 65520:

```sh
TMPDIR=/private/tmp/m214-qt4-final .lake/build/bin/l4qt4 --isolate 60 --lang xquery
TMPDIR=/private/tmp/m214-qt4-extra .lake/build/bin/l4qt4 --isolate 60 --lang xquery --family bin --family file --family xs --family ser
```

Raw TOTAL lines from the final full selection and supplemental run, respectively:

```text
TOTAL: 44366 pass, 1329 fail, 1096 unsupported (out of 46791); 1 excluded (defective test data)
TOTAL: 1563 pass, 17 fail, 78 unsupported (out of 1658); 24 excluded (defective test data)
```

The full selection was interrupted in `prod-ForClause` and
`misc-HtmlTestSuite`. Follow-up commands:

```sh
TMPDIR=/private/tmp/m214-qt4-final .lake/build/bin/l4qt4 --isolate 60 --lang xquery --family prod --family misc --list-fails
.lake/build/bin/l4qt4 --lang xquery --family prod --list-fails
```

```text
TOTAL: 17906 pass, 741 fail, 533 unsupported (out of 19180)
TOTAL: 14099 pass, 408 fail, 441 unsupported (out of 14948)
```

The first follow-up completed `misc` at 4120 pass, 16 fail, 96 unsupported,
but stopped in `prod-InstanceofExpr`. The direct `prod` run completed.
Combining those completed families with the final full run's other families
and the supplemental run gives the comparison below. This is a combined
family measurement, not one uninterrupted full run.

- PR's 12 families: **45858 pass, 618 fail, 1148 unsupported (out of 47624)**;
  25 excluded. Baseline: 45855 pass, 619 fail, 1150 unsupported.
- `fn`: 17316 pass, 138 fail, 408 unsupported; three more passes than baseline.
  All other original families have exactly the PR's scores.
- Incoming `upd`: **798 pass, 0 fail, 27 unsupported (out of 825)**.
- All 13 families combined: **46656 pass, 618 fail, 1175 unsupported
  (out of 48449)**; 25 excluded.

No original family loses passes in the completed measurements. Remaining
limitation: intermittent isolated-process interruptions are unresolved.
The pre-existing `op-same-key` and `app-Demos` interruptions remain counted
as failures, as in the baseline; no interrupted test is counted as a pass.

Logs: `/private/tmp/m214-xquery-final.log`,
`/private/tmp/m214-xquery-extra-final.log`, `/private/tmp/m214-prod-misc.log`,
`/private/tmp/m214-prod-direct.log`.

The default selection includes `upd` but omits `bin`, `file`, `xs`, and `ser`.
The second command supplies those four PR baseline families. Full Text was
not part of this PR.

Initial runs reported interrupted sets and an apparent loss of passes.
`--family fn --list-fails` and a direct `fn-path` repeat did not reproduce
that loss consistently. The runner uses shared progress-file names under
`TMPDIR`; final measurements use separate directories to avoid collisions.
Interruptions also occurred with separate directories, so shared progress
files do not explain all observed interruptions. Their cause remains unconfirmed.

Worknote: [XQuery 4.0 merge validation](docs/20261029-xquery4-merge.md).
