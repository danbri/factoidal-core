# Hub Data Compositor and shared code output

The full-width [Data Compositor](web/hub/data-compositor/) uses the published `@factoidal/core@0.27.0` browser engine in a worker. Studio roster inputs pass through Turtle/CSVW import, dataset merge, RDFS closure, named graph adapters, SPARQL selection, SPARQL XML and XSLT HTML. Source text remains editable. The default result is three contributors from five source people.

Registered public nodes execute where available. Named graph tagging, closure delta selection, query-template substitution and display transport are explicitly unproved API adapters. The filtered SPARQL query executes once: a fixed engine XQuery projects table rows from that same XML, and XSLT consumes the identical XML. This avoids divergent results for volatile queries. CSVW conversion is not a strict CSV validator: invalid typed numeric cells may become plain literals and fail the query filter.

The Evidence switch shows actual registry/runtime statuses, checked/proved flags, contracts and assumptions. Only datasetMerge's small registered graph uses its actual composition checker. Display wires are manually specified dependencies, including query-to-filter sequencing rather than a Table input. Neither the whole recipe nor all adapters are proved. HTML is displayed in a sandboxed, CSP-restricted iframe.

Shared code-output controls preserve exact source text, highlight using the vendored Shiki bundle, and provide Copy, Wrap and Raw/Formatted views. Formatting is supplied by the engine; the control does not invent a formatter. Existing hub code cells use the same controls, including executable fence flags and source visibility.

## Verification

Ten focused compositor Node tests pass, including actual core execution, input edits and errors, volatile query single-execution consistency, evidence boundaries and a real resource-bounded Eleventy build with the `/factoidal/` Pages prefix. The integrated Chrome interaction probe passes actual WASM results, slider and CSV edits, metadata/evidence, wire inspection, table/HTML export, shared output controls, drag/zoom, errors and reset with no browser errors. Shared controls have two passing static tests and a passing Chrome test covering exact text, highlighting, Copy/Wrap/Raw/Formatted, executable flags, dark mode, CRLF and actual hub cells.

The initial full hub run measured 392 pass, 66 fail and 9 skip. All 66 failing test labels reproduce on unchanged HEAD using baseline subsets; no new failing labels were found. A complete aggregate baseline run was interrupted by disk exhaustion, so no full baseline pass count is claimed. Focused existing hub baseline/current comparisons match: fn parity 9/0, fence flags 9/0, post32 12/0, and post17 6 pass/7 fail on both. No full historical-site build, new engine build or whole-pipeline proof is claimed.

## Future proof targets

A useful future theorem should bind the exact typed Lean recipe, adapter contracts, query settings, source snapshot and stylesheet identity. Candidate obligations are sound and complete query results for the supported fragment; exact provenance of the derived-triple delta; faithful row presentation by a fixed XSLT stylesheet; and snapshot consistency between displayed rows, XML and HTML. First state conditional contracts for the currently unproved adapters, then discharge them individually. These are proposed proof targets, not existing guarantees. Component theorems alone do not establish the end-to-end claim.
