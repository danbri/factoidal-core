# XML parsing: invalid XSD validation option

Official QT4 case `fn-parse-xml/parse-xml-437` supplies the string `sporadic`
as the `xsd-validation` option. It requires `FODC0008`; the shared
`XPath4.XmlParse.parseOpts` returned `XPTY0004`. The recently added option
tests also incorrectly pinned `XPTY0004` for an invalid string mode.

The producer now applies the existing XPath coercion operation to obtain one
`xs:string` before checking its permitted values. An invalid string mode
raises `FODC0008`. Non-coercible values and wrong cardinality retain type
errors. `xs:anyURI` and `xs:untypedAtomic` values use the shared coercion
rules rather than a new conversion implementation. The default remains `skip`.
The correction applies to the shared options used by XML parsing and `fn:doc`.

## Normative evidence

[F&O 4.0 option parameter conventions](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#option-parameter-conventions)
require each function to coerce option values to their declared type before
checking permitted values.
[fn:parse-xml](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-parse-xml)
declares `xsd-validation` as `xs:string` and specifies `FODC0008` for invalid
modes or invalid/unknown type names.

The existing specification snapshot `/private/tmp/qt4-fo4-unicode-policy.html`
was inspected at lines 4345–4365, 71232–71278 and 71350–71353; its SHA-256 is
`60cbc78c30be60ad2b7c2bd34153891c1527d554863d57e3110c1c9e96a21bba`.
No new download was needed.

The untouched fixture is
`source/factoidal-qt4/third_party/testing/qt4tests/fn/parse-xml.xml`, case 437,
in test-suite commit `18728a6943589f8341d67f94af154e3c68917bbb`.

## Validation

The corrected expected-error guards for `invalid` and `sporadic` failed
against the old producer before the implementation edit. After the edit,
all 24 focused checks in `XmlParseOptionTests.lean` pass: 13 kernel examples
and 11 executable guards. The additional guards exercise invalid modes,
boolean/integer values, empty/multiple values, valid modes and permitted
URI/untyped coercions. They do not prove the full XPath coercion rules.

The current `XmlParse.lean` was compiled to C and one native object. That
object replaced the old XmlParse object in the existing October 30 native
QT4 runner's link response file. All other runner objects were reused.
This is a targeted native replay, not a complete current-head build or a
published npm/WASM artifact. No engine binary was copied into the repository.
The fresh test executable is `/private/tmp/l4qt4-xsd-option`.
Its SHA-256 is
`ce4c247dc12ddfef5720097f13c69873a66758a21b8cf14c6d1fe463b5719c1f`.
The C generation used Lean's module setup with package `l4factoidal` to retain
the existing object symbol namespace; no generated C was edited by hand.

Run from `formal/lean4/`:

```sh
/private/tmp/l4qt4-xsd-option \
  --root ../../../factoidal-qt4/third_party/testing/qt4tests \
  --family fn --set fn-parse-xml --lang xquery --list-fails
```

The official parse-xml set changed from **49 pass, 5 fail, 3 unsupported** to
**50 pass, 4 fail, 3 unsupported**, out of 57 cases. Case 437 is repaired.
Remaining failures are 434 (schema-invalid error code), 436 (schema-aware
whitespace preservation), and 438/439 (type-name validation errors in the
schema hook). They remain failures, with no changed expectations or skips.

The same replay gives **40 pass, 0 fail, 1 unsupported**, out of 41 fragment
cases; the old runner gives 38 pass, 2 fail, 1 unsupported. This also exercises
the earlier retain-location repair, which is present in the fresh module.
The `fn-doc` set remains **75 pass, 1 fail, 3 unsupported**, out of 79 cases.
Its failure is `fn-doc-40-065`; two unsupported cases have missing source
fixtures and one requests a different language version. The native runner
returns exit zero even with reported failures, so the counts were inspected.

The routing checkout's all-suite fixture check reports missing fixtures and
native binaries. These narrow runs explicitly use the populated sibling QT4
suite; they are not an all-suite conformance result. A rebuilt npm/WASM package
and a clean current-head native runner remain release validation obligations.

## Deliberately separate repairs

Cases 438 and 439 require rejecting malformed or unknown names after `type`.
That resolution is currently in the schema hook, not this mode-admission
branch. The patch does not remap all schema failures to `FODC0008`, which would
hide the separate `FODC0014` contract for content that fails XSD validation.
