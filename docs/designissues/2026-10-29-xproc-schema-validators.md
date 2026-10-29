# XProc schema validator bridges — 2026-10-29

SchematronSteps reuses the Schematron XML reader and assertion/report semantics, with XProc XPath environments and XSLT pattern matching. Rules claim matching nodes in order within each active pattern. Schema, pattern and rule lets are bound lexically; current() refers to the matched rule node even inside a predicate. Source documents and properties pass through unchanged. SVRL and XVRL reports record actual findings. An enabled assert-valid rejects either a failed assertion or a successful report. Includes, abstract rule expansion and diagnostic references are outside this bridge's implemented slice.

JsonSchemaSteps uses the existing three-valued JSONSchema validator, converting native XDM JSON values through the JSON serializer. Invalid instances yield XC0165; unknown validator capabilities remain unsupported. Keyword shapes are checked before evaluation so malformed unvisited subschemas are rejected. Only draft-07 dialect declarations are accepted because the shared validator has draft-07 reference-sibling semantics. Arbitrary report formats produce XC0117. XVRL contains a detection for a failed validation and no detection for a successful one; fine-grained keyword paths are not available from the shared verdict API.

Regression guards cover Schematron assertion/report inversion and strict/permissive behavior, JSON keyword structure, and required properties without a corresponding properties declaration. The upstream JSON-schema008 fixture calls such a schema invalid, but JSON Schema permits it: the instance fails validation instead. This remains visible as a test discrepancy.

Verification pending the coordinated module build; no compile or fixture pass claim is made yet.
