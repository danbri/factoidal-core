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
