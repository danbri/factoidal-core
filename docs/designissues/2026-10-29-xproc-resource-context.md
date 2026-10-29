# XProc XPath resource context — 2026-10-29

ResourceContext provides `preloadXPathResources : XPath4.Env → XML.Node → IO XPath4.Env`.
The XPath evaluator remains pure: the pipeline runtime reads resources before
evaluation and passes byte/text tables through Env. Recognized calls include
doc/doc-available, json-doc, unparsed-text/lines/available. URI expressions are
evaluated from parsed AST arguments, not guessed by searching string literals.

Traversal preserves lexical variable and mapped focus contexts where evaluated,
uses only the selected branch of an evaluable conditional, and traverses nested
calls before outer resource arguments. XML nodes contribute raw select/test
expressions and AVT/TVT expressions scanned with the shared parser. Namespace,
base URI and expansion settings are inherited while only resource state leaks
back to the caller.

Every resolved file URI is refreshed. Failed reads invalidate the previous
resource entry and leave the evaluator to produce its own error; decoder failures
retain the actual bytes without substituting text. Reads do not authorize writes.

The module builds. `resourceContextRegression` uses a real temporary file and
passes dynamic URI resolution, overwrite refresh, let binding, no literal-only
or inactive-branch read, and missing-resource behavior after deletion. Runtime
integration and full-suite measurement are owned by the root agent.
