# Selectable XPath and XQuery language versions

Date: 2026-10-29. Workstream: CONFIG-BRIEF S1.

## Configuration and reuse

`XPath4.FeatureSettings.version` selects 1.0, 2.0, 3.0, 3.1, or 4.0.
The default is 4.0. XPath 2.0 and XQuery 1.0 share the original F&O
library. `xpath10Compatibility` separately selects compatibility conversion.
`Env.restrictFeatures` carries both settings into the engine. Qt4Run selects
the newest version allowed by each test's spec dependency for its language.
The test-case dependency replaces the set dependency. Other feature and
schema dependencies still apply; unsupported is never a pass.

The implementation reuses the XPath4 AST, parser, evaluator, signatures,
atomic values, decimal arithmetic, regex engine, serializer, and schema hooks.
XQuery extension parsing receives the same feature settings. Older grammar
and operator domains are checks around these shared definitions. Numeric
comparison uses the existing `Num.promote`. Older regex profiles use the
existing Regex profiles. Legacy anchored patterns use the existing ordered
matcher because sentinel consumption cannot represent repeated zero-width
anchors such as `^{2}`. The v40 compilation branch is unchanged. Typed variable bindings use `Env.bindTyped`:
4.0 applies the shared coercion; older versions check the supplied sequence
against the declared type. Function parameters still use function conversion.

Old function argument types must be checked before the 4.0 defaults and
coercions erase the supplied arity and type. Static normal calls check supplied
values before defaults are passed to the function implementation. Builtin
function-item calls check the original arguments before appending defaults.
The full-argument implementation must not recheck the supplied arity.

Binary map keys in older versions keep hexBinary and base64Binary distinct.
Version 4.0 retains its map builder. The older map constructor uses the shared
version-sensitive equality helper. Adaptive serialization uses the existing
writer with version-dependent lexical forms; it does not duplicate the writer.

## Assurance

`CompatibilityTheorems.lean` is imported by the Qt4Run build root. The common
AST fragment contains string literals and boolean constants. Kernel theorems
cover value string conversion and XPath4 literal evaluation. The older XPath
engine is partial, so its actual evaluator agreement is an executable guard,
not a kernel theorem. General AST agreement remains open.

Default settings are definitionally an identity through `Env.restrictFeatures`.
Explicit v40 and default evaluation agree definitionally. Version wrappers
for operators, maps, regex compilation, argument checks and typed bindings
have v40 identity theorems. These do not prove full conformance or historical
identity with a separate old executable. The qt4tests measurements check the
selected configurations against the supplied expected results.

## Integration and evidence

The resumed worktree had an unfinished merge. The Regex4 conflict contained
version/empty-pattern checks on one side and schema annotation on the other.
Both are retained. Incoming validation and regex bridge theorems needed the
new feature precondition and version-aware statements.

The source inventory and grouping are `../20261029-version-targets.tsv` and
`../../REPORT.md`. Baseline logs are in `../20261029-version-before/`.
The report records final commands, measurements, and every remaining target.
Network commands are prohibited by the brief, so comparison with the 4.0
change-log appendices could not be completed from locally available material.
