# fn:transform assertion option

Tracking: https://github.com/danbri/factoidal/issues/1161 (remaining
fn:transform conformance work).

## Contract and change

The [F&O fn:transform option table](https://www.w3.org/TR/xpath-functions-31/#func-transform)
defines `enable-assertions` as `xs:boolean`, defaults it to false, and
uses it to control whether `xsl:assert` instructions are evaluated.
QT4 cases `fn-transform-91` and `fn-transform-92` check the default and
explicitly enabled cases respectively.

Previously both transform adapters ignored the option, and the XSLT
interpreter always evaluated assertions. A failing assertion therefore
raised `XTMM9001` even when the option was absent or false.

`XSLT4.Sheet.assertionsEnabled` now carries the invocation setting through
all uses of the stylesheet. Its default is true, which retains the
existing behavior of direct XSLT invocations. `Interp.run1` checks it
before evaluating the assertion test, message body, select expression,
or error-code AVT. Both `QtFnTransform` and the separate `FnTransform`
adapter set it from the option, with default false. The nested adapter
uses the normal boolean coercion before storing the setting.

The existing `QtFnTransformTests` module remains reachable from
`L4Factoidal.lean`; no root-import change was needed. Eleven new executable
guards cover absent, false and true settings, disabled test/body
non-evaluation, enabled test errors, the separate nested adapter, and
the retained direct-XSLT assertion default.
These are executable regressions, not a new correctness theorem.

## Validation

All Lake commands ran from `formal/lean4` under the shared build lock.

- Red: `lake build L4Factoidal.XSLT4.QtFnTransformTests` failed six new
  disabled/default assertion guards; the three enabled controls passed.
  Log: `/private/tmp/qt4-assertions-red.log`.
- Green: `lake build L4Factoidal.XSLT4.QtFnTransformTests l4qt4` passed
  (373 jobs). The initial nine new guards and the existing QName guards pass.
  Log: `/private/tmp/qt4-assertions-green.log`.
- Final regression validation by the Unicode worker:
  `lake build L4Factoidal.XSLT4.QtFnTransformTests` passed (134 jobs),
  including both added direct-XSLT default guards and all eleven new
  assertion guards. Log: `/private/tmp/qt4-transform-final-direct-tests.log`.
- Fresh corpus: `.lake/build/bin/l4qt4 --lang xquery --set fn-transform
  --list-fails --isolate 60` reported 130 pass, 6 fail, 1 unsupported
  (out of 137), previously 129 pass, 7 fail, 1 unsupported.
  `fn-transform-91` now passes; `fn-transform-92` still passes.
  Log: `/private/tmp/qt4-assertions-corpus.log`.
- `tools/obsolescence-sweep.sh enable-assertions xsl:assert` found no
  stale-claim candidates. A direct source search found the ignored-option
  statement in `QtFnTransform`'s header; it was corrected.

Remaining corpus failures are `fn-transform-27`, `fn-transform-67`,
`fn-transform-70`, `fn-transform-82e`, `fn-transform-94` and
`fn-transform-err-9a`. The unsupported `fn-transform-48` requires the
older selectable language mode; it remains work to do. No dependency
filters, exclusions or expected results changed.


## Generated-C recursion gate

The [exact-head package run](https://github.com/danbri/factoidal-builds/actions/runs/40965768109)
compiled the library but failed the tail-recursion audit on the previously
unlisted `XSLT4.fnTransform` and `XSLT4.fnTransformHost` callback cycle.
The assertion regression module imports this separate nested-transform
adapter, making its pre-existing recursion reachable in the library build.

The cycle is real C call/closure recursion, but its depth is transformation
nesting, bounded by the explicit fuel. It is not a recursive traversal of
the `List` arguments named in the audit's signature-based classification.
`fnTransformHost (f + 1)` installs a callback calling `fnTransform f`;
`fnTransform (f + 1)` installs `fnTransformHost f`. Zero fuel gives no host
callback or raises `FOXT0001`. The production `Harness/Xslt4Run.lean`
caller supplies host fuel 3. Arbitrary callers can supply larger budgets;
there is no claim that all API calls have a constant stack bound.

The body is factored as nonrecursive `fnTransformWithHost`, leaving lazy
host setup with constant work independent of unused fuel. The four
zero/successor equations retain the original mutual definitions for every
fuel. The two successor theorem axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`. No axioms or partial definitions were
added. An eager `Nat.repeat` callback-chain construction was rejected
because it would add work proportional to unused fuel.

Two exact allowlist entries classify the existing semantic nesting under
marker `(b)`, each with the bound, code/test location and tracking issue.
No wildcard, audit logic, class threshold or runtime budget changed. The
C cycle remains visible to the audit.

Additional executable regressions run a stylesheet that calls
`fn:transform` on a second stylesheet: host fuel 3 produces `FOXT0001`;
host fuel 4 returns `7`. These test actual nested execution at adjacent
budget boundaries, rather than only host construction.

Validation:

- Named `lake build L4Factoidal.XSLT4.QtFnTransformTests l4qt4` passes.
  Log: `/private/tmp/qt4-transform-fuel-build.log`.
- The generated-C audit over a correctly rooted view of the named
  `FnTransform.c` module fails with the previous allowlist on exactly the
  two declarations, then passes with the two documented entries, including
  the chained csimp reach gate. Logs:
  `/private/tmp/qt4-transform-fuel-module-red.log` and
  `/private/tmp/qt4-transform-fuel-module-audit.log`.
- The full local cached-C audit reports 47 unrelated Harness/XProc entries;
  it is not a clean full-library build. This targeted validation does not
  replace the next clean exact-head package gate.
- The fresh official XQuery fn-transform set remains 132 pass, 4 fail,
  1 unsupported (out of 137). Log:
  `/private/tmp/qt4-transform-fuel-corpus.log`.
