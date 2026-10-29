# XPath and XQuery processor feature settings

`XPath4.FeatureSettings` is part of the parser context and the evaluator
`Env`. The default enables all ten features named in the switch brief.
`Env.restrictFeatures` combines restrictions. An all-enabled restriction
leaves the environment unchanged. Disabling typed data also disables schema
import and validation. Node access then removes type annotations and typed
values; element construction uses the untyped form.

The XSLT30 restriction rejects XSLT3-only options and principal stylesheet
versions of 3.0 or later. The compiler still uses its full XSLT4 grammar.
A version 2.0 transformation is included in the focused checks.

The parser and module checks reject calls to absent functions even in a
branch that will not run. Runtime checks also protect calls through function
items and host callbacks. Binary, file, and invisible-XML functions become
absent. Dynamic XQuery and XSLT calls retain error functions with `FOQM0006`
and `FOXT0004`. Serialization retains `fn:serialize` with `FODC0010`; output
declarations are ignored. These choices follow the error alternatives in
the supplied qt4tests and the function specifications.

References: [XQuery 4.0 optional features](https://qt4cg.org/specifications/xquery-40/xquery-40.html),
[F&O 4.0](https://qt4cg.org/specifications/xpath-functions-40/Overview.html).

`Harness.Qt4Run.featureSettings` reads negative feature dependencies from
the test set and case, and positive dependencies for the opt-in
[static typing configuration](2026-10-29-static-typing.md).
The selected settings apply to the query and its
assertions. Other tests use the default. The runner does not infer a pass
from a dependency; the query must produce the expected result or error.

`Env.restrictFeatures_allEnabled` and `eval_allFeaturesEnabled` prove the
identity of applying an all-enabled restriction by `rfl`. They do not prove
that every modified evaluator branch is equivalent to the earlier source.
The before/after family measurements check that separate requirement.

Measurements, commands, and limitations: [SWITCH-REPORT.md](../../SWITCH-REPORT.md).
Worknote: [2026-10-29](../20261029-processor-feature-settings.md).
