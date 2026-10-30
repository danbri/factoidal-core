# parse-ietf-date zero-seconds panic

A valid date with omitted seconds, explicit zero seconds or fractional seconds
below one returned the correct value but also printed a Lean panic/backtrace.
The panic fallback supplied zero, so value-only assertions missed the problem.
This was present before HTML integration: `XPath4/Format.lean` was unchanged
between main baseline `5de7afc8` and HTML integration `11e9d4c8`.

## Cause and bounded change

`Format.decDigits` removes leading integer zeroes. Its integer part is therefore
empty for zero and a fraction below one. `parseIetf` serialized this part with
`numOf`, which calls `String.toNat!`; an empty list triggers `Nat expected`.

The change emits `"00"` for that valid empty seconds integer part. All nonempty
parts still use the original numeric parser and padding. General `numOf`, date
admission, timezone handling and error behavior are unchanged.

[F&O 3.1 section 9.9.1](https://www.w3.org/TR/xpath-functions-31/#func-parse-ietf-date)
permits omitted seconds/fractions and specifies zero when absent. Explicit zero
seconds and fractions such as `00.25` also satisfy the grammar.

## Regressions and reproducible commands

`L4Factoidal/XPath4/FormatIetfTests.lean` checks the empty integer part and five
returned values. The normal aggregate test module imports it.
`tests/xpath4/parse-ietf-date-native.test.mjs` invokes the real native dispatch
ABI and checks process success, JSON success/cardinality/value, and **empty
stderr** for the same five examples. A driver path may be supplied in
`FACTOIDAL_QT4_NATIVE`; otherwise it uses the normal local `l4wasm-cli` target.
The test never downloads or builds an engine and does not silently skip a
missing/stale driver.

From `formal/lean4/`, under the shared build lock:

```sh
lake build L4Factoidal.XPath4.FormatIetfTests l4qt4 l4wasm-cli
.lake/build/bin/l4qt4 --root ../../third_party/testing/qt4tests \
  --family fn --set fn-parse-ietf-date --lang xpath --trace --list-fails
```

From the repository root:

```sh
node --test tests/xpath4/parse-ietf-date-native.test.mjs
```

The probes use omitted seconds (`19:36 GMT`), explicit zero (`19:36:00 GMT`),
zero integer fraction (`19:36:00.25 GMT`), a nonzero control (`19:36:01 GMT`),
and next-day rollover (`Aug 20 24:00 2014`). They require the unchanged values
`2014-08-20T19:36:00Z`, `2014-08-20T19:36:00Z`,
`2014-08-20T19:36:00.25Z`, `2014-08-20T19:36:01Z` and
`2014-08-21T00:00:00Z` respectively.

## Measurements

Before the fix, the five native probes returned correct JSON and exit status
zero, but four failed the clean-stderr assertion; only the nonzero control
passed. The targeted official set reported 105 pass, 0 fail, 0 unsupported,
while emitting 11 panic backtraces: `parse-ietf-date-9`, `-11`, `-13`, `-19`,
`-20`, `-21`, `-22`, `-23`, `-60`, `-63` and `-64`.

The named warm build of `L4Factoidal.XPath4.FormatIetfTests`, `l4qt4` and
`l4wasm-cli` passed. All six Lean guards passed. The official targeted set still
reports **105 pass, 0 fail, 0 unsupported**, now with **zero panic diagnostics**.
The same five native probes report **5 pass, 0 fail**, with empty stderr and
unchanged values. The regression was run red before applying the fix, so its
stderr assertion is known to detect the original defect.

The existing build cache measured 3,025,196 KiB before and 3,025,256 KiB after
the warm build (0.06 MiB net change); no cold dependency or
WASM build was used. The shared lock was released after the named build.
No full corpus, fixture/exclusion/harness policy change or CI dispatch was
made during local validation. Local diagnostic logs are under
`/private/tmp/parse-ietf-date-diagnosis/`; no generated artifacts are committed.
The core Lean workflow now builds the native dispatch driver alongside the
existing QT4 runner and runs the five Node stderr/value probes. A missing
driver is an error. This makes the regression a CI gate instead of relying
on value-only Lean guards, which did not detect the original panic.
