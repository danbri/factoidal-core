# XProc 3.1 implementation progress — 2026-10-28

Scope: CODEX-BRIEF.md. No commits or pushes. Changes restricted to XProc31,
lakefile, this file and docs/designissues.

## First implementation milestone

Added document/property model, XPath option/AVT helpers, input bindings,
compound step runtime, standard atomic step dispatch, isolated upstream test
runner, static cycle detection and Dataflow lowering/theorems.

The runner path in the brief is `formal/lean4/Harness/Qt4Run.lean` (without
`L4Factoidal`). All named engine dependencies are present in this checkout.

Build: `ulimit -s 65520; export PATH=$HOME/.elan/bin:$PATH; lake build L4Factoidal.XProc31.Core`
with working directory `formal/lean4` passed. Atomic/runtime/runner integration
is in progress. No suite score yet.

Open: complete runtime integration, measure all 3363 upstream test documents,
fix failures, extend unsupported steps and static checks. Bridge distinguishes
graph evaluator equality from an unproved XML-reader interpretation; the
pure for-each law does not yet prove the runtime IO loop.

Tracking: https://github.com/danbri/factoidal/issues/1129 (checked pipelines and XProc).

## Full suite measurements

All commands run from `formal/lean4` after `lake build l4xproc`:

`.lake/build/bin/l4xproc --list-fails --list-unsupported`

- First run: 129 pass, 1821 fail, 1413 unsupported, total 3363.
- Second run: 466 pass, 1439 fail, 1458 unsupported, total 3363.
- Third run: 750 pass, 782 fail, 1831 unsupported, total 3363.

Each test runs in a child process with a five-second deadline. Logs are
`/tmp/xproc-suite-1.log`, `/tmp/xproc-suite-2.log`, `/tmp/xproc-suite-3.log`.
Runner corrections: Schematron XML default namespaces do not define the
XPath default element namespace; fixture paths are absolute file URIs.
The first score therefore included oracle defects as well as runtime defects.

Current unmeasured additions: nested/quoted/comment-aware AVTs, imports,
forward-reference scheduling, use-when pruning, XSLT/XQuery error mappings,
more atomic steps and JSON values. Unsupported step admission now precedes
input loading, so an absent archive step cannot fail while trying to parse
its binary input as XML. General document properties, binary content and
several compound/static checks remain incomplete.

### Shared module fix: XSLT host function fallback

`formal/lean4/L4Factoidal/XSLT4/Transform.lean`: `mkHost` now delegates an
unknown host function to `base.host q k`. The previous fallback returned
`none` and dropped the XProc default collection hook. XSLT functions still
have precedence. With the default empty host the result is unchanged.
`XProc31/Atomic.lean` has a regression that calls a named XSLT template and
checks `count(collection()) = 2` for two source documents. Build result is
recorded with the next Atomic milestone.

Atomic validation (2026-10-28): from `formal/lean4/`,
`ulimit -s 65520; export PATH=$HOME/.elan/bin:$PATH; lake build L4Factoidal.XProc31.Atomic`
completed with exit 0 (112 jobs). The subsequent QName-prefix preservation
change passed `lake env lean L4Factoidal/XProc31/Atomic.lean`, exit 0.
The guards cover count, delete, rename, add-attribute, collection through
XSLT, and rejection of an empty-matching text replacement pattern. These
local guards are not included in the upstream suite score.

### XPath host functions (2026-10-28)

`XProc31/Functions.lean` supplies POSIX `p:urify`, `p:system-property` and
`p:step-available`. Availability comes from a caller-supplied predicate;
lexical QNames and EQNames resolve in the XPath static namespace context.
The episode identifier is a caller parameter. Windows-specific `urify`
fixtures are platform requirements and must be reported unsupported on POSIX.

Validation from `formal/lean4/`: `lake build L4Factoidal.XProc31.Functions`
exited 0. A temporary Lean harness, `/tmp/XProcUrifyCheck.lean`, reads the
actual upstream `nw-urify-non-windows*`, `nw-urify-any*`, and `nw-urify-path*`
files, evaluates their expressions through the host function, checks their
assertions and expected errors: `lake env lean --run /tmp/XProcUrifyCheck.lean`
reported 133 pass / 0 fail. This is a function-only check; the full runner
score is recorded separately after runtime integration.

## Runtime and proof integration milestone

Fourth full run: 910 pass, 683 fail, 1770 unsupported, total 3363.
Fifth full run: 1145 pass, 532 fail, 1686 unsupported, total 3363.
Command for both, from `formal/lean4` after successful `lake build l4xproc`:
`.lake/build/bin/l4xproc --list-fails --list-unsupported`.
Logs: `/tmp/xproc-suite-4.log`, `/tmp/xproc-suite-5.log`.

Viewport subset after binding and fragment fixes:
`.lake/build/bin/l4xproc --filter viewport --list-fails --list-unsupported`
reports 46 pass, 0 fail, 2 unsupported, total 48.

Runtime now calls `Sequence.forEachIO`; the actual IO action has mapM,
ordered concatenation and short-circuit theorems imported by Bridge.
The earlier pure-only for-each boundary is resolved. XML reader correctness
and full runtime-to-graph equivalence remain unproved.

Added standalone pipeline CLI and `Regression.lean` end-to-end checks
(the new regression file is pending its first run while document-property
migration is in progress). Design/status record:
`docs/designissues/2026-10-28-xproc31-processor.md`.

### 2026-10-28 — typed document properties milestone

Document now stores additional properties as QName-keyed XPath sequences; nested maps, arrays, and node references retain their types (node references capture their document). Core fields remain authoritative for content-type/base-uri. New `XProc31/Properties.lean` normalizes lexical QName keys, validates absolute base URIs/media types/serialization maps, and merges or resets properties. Atomic `p:set-properties` uses this model. Runtime property functions return the full typed map and inline bindings apply properties for XML, JSON, and text. Constructor migration touches Core, Atomic, Runtime and Sequence. Runner serialization merges a stored serialization property with explicit declaration options and translates parameter QName keys for the existing XPath serializer.

Validation: `lake build L4Factoidal.XProc31.Runtime` succeeded (120 jobs). Five meaningful Properties guards cover reset/base removal with nested map retention, malformed base URI, preservation of namespaced arbitrary property plus QName serialization keys, non-map serialization rejection, and prohibited content-type changes; `lake env lean L4Factoidal/XProc31/Properties.lean` passed. Runner changes await its owner's module build. Remaining work handed to root: document/load binding properties, preservation through binding select, choosing the passed document rather than first document for property functions, bare pipe semantics and port media validation. These are not claimed complete.

### 2026-10-28 — cast-content-type semantic fixes

Atomic casts now classify media types before conversion: text/xml remains a tree, XML/HTML retagging preserves content, cross-kind casts remove serialization while retaining arbitrary document properties. JSON→XML retains those properties; text→JSON/XML report XProc parse error codes; text→HTML delegates to existing parse-html. c:data decodes standard base64 using the existing XSD decoder with UTF-8 or Latin-1, and reports missing/mismatched content-type and unsupported encoding/charset. Generated XML edits also remove serialization when their result changes to text.

Validation: Atomic module built; three new guards typechecked for XML retagging, non-ASCII Latin-1 c:data, and property retention/removal. Full fixture gains await next executable measurement; did not rebuild executable during suite6.

### 2026-10-28 — namespace rename and XInclude checks

Build 14 targeted commands, from `formal/lean4/`:
`.lake/build/bin/l4xproc --filter namespace-rename --list-fails --list-unsupported`
reported 23 pass, 0 fail, 0 unsupported (23).
The same command with `--filter xinclude` reported 21 pass, 1 fail, 0 unsupported (22).
With `--filter viewport`, it reported 47 pass, 1 fail, 0 unsupported (48).
Logs: `/tmp/xproc-namespace-rename-latest.log`, `/tmp/xproc-xinclude-latest.log`,
`/tmp/xproc-viewport-latest.log`.

The viewport failure exposed a text-result content-type defect; the source
now changes it to text/plain, removes obsolete serialization properties, and
preserves arbitrary source properties. Module typecheck and new guards pass.
The XInclude failure exposed unavailable per-node base URI preservation when
XML inclusion disables xml:base fixup. That specific missing capability now
returns unsupported instead of silently discarding the base URIs. The next
full executable run must measure both changes. Details and remaining XInclude
limits are in `docs/designissues/2026-10-28-xproc31-processor.md`.

## Seventh full suite and independent regressions

Sixth full run: 1583 pass, 508 fail, 1272 unsupported, total 3363.
Seventh full run: 1776 pass, 412 fail, 1175 unsupported, total 3363.
Exact command from `formal/lean4`: `.lake/build/bin/l4xproc --list-fails --list-unsupported`.
Logs `/tmp/xproc-suite-6.log`, `/tmp/xproc-suite-7.log`.

Build 17 passed `lake build l4xproc`; `.lake/build/bin/l4xproc --self-test`
passed 22 end-to-end checks. Runtime now supports named compound outputs,
expanded-name catch matching, direct try subpipelines, finally output merging,
split-sequence matched/unmatched ports, and initial dynamic p:run support.
Regression coverage includes literal use-when preservation, foreign-step
refusal, callee option isolation, collection branches and dynamic pipelines.

`.lake/build/bin/l4xproc --scale-test`: 65/129/257-step identity pipelines
passed at 1/3/7 ms. The same command with `ulimit -s 512` passed at 2/3/6 ms.
These measurements cover this native chain workload only.

`python3 tools/lean-unbuilt-modules.py --gate` exits 0: all 1273 modules
reachable from 183 roots. `python3 tools/lean-tail-recursion-audit.py --gate`
exits 1: 146 recursive declarations lack allow-list entries, including new
XProc declarations and pre-existing XPath/XSLT dependencies. Log:
`/tmp/xproc-tail-gate.log`. The narrow stack canary does not discharge this
gate. The brief excludes edits to the tools allow-list; no blanket exceptions
were added. This remains open verification work.

### 2026-10-28 — native map and array document content

Core Document now has an optional native XPath sequence payload. `seqDocuments` retains map/array entries without eager JSON serialization, including multiple-item values, QName keys and embedded XML nodes with captured document references. `xpathEnv` uses the payload and recognizes +json media types. Atomic c:param-set conversion creates QName-keyed maps; casts clear native payloads when changing bodies and serialize JSON only when text/XML conversion requires it. Runner CLI and serialized test output serialize native content at the boundary. Constructor migration updated Core, Atomic, Sequence (Runtime migration coordinated with root). Also fixed invalid base64 error XC0072 and recursive wrapping of nested matches.

Validation: Core/Atomic/Sequence built (117 jobs). New Core guard checks both multi-item map retention and navigation into embedded nodes after a document table change; Atomic guard checks QName map access after c:param-set conversion. Both source typechecks passed. Full suite gains pending next measurement.

### 2026-10-29 — local document loading

`XProc31/Loading.lean` supplies `loadDocument uri contentType`. It reuses the
existing UTF-8, UTF-16, ASCII, Latin-1, XML, JSON, and HTML implementations.
MIME charset controls decoding; a compatible BOM is removed. An explicit
incompatible charset remains authoritative. XML/text/JSON/HTML produce typed
documents; network retrieval and binary documents remain unsupported.
Local DTD and entity resources are read before XML parsing and supplied through
`XML.Resolver`. Ambiguous lexical system IDs with different base URI contexts
are unsupported. External-entity per-node base URIs remain outside the current
XML tree representation; entity content expansion does not establish that
missing metadata property.

Validation, from `formal/lean4/`: `lake env lean L4Factoidal/XProc31/Loading.lean`
passed, with eight decoding/declaration guards. A temporary probe reads the
upstream BOM fixtures and evaluates their result AVTs after loading:
`lake env lean --run /tmp/LoadingProbe.lean` reported 14 pass, 0 fail,
3 network unsupported. It also checked external DTD loading and expansion of
both chapters in `doc-with-entities.xml`. This is a loader check, not a full
processor score. `lake env lean --run /tmp/LoadingHtmlProbe.lean` passed its
HTML parser integration check with an omitted paragraph end tag.

### 2026-10-29 — recursive wrapping and adjacent groups

Atomic p:wrap now transforms descendants recursively and groups adjacent matching siblings using atomized XPath deep equality. Comments, processing instructions, and whitespace between equal-key members stay inside the group; separators between differing groups remain outside. p:wrap-sequence evaluates keys with sequence position/size and supports sequence-valued keys. Both steps support the attributes map with QName resolution; wrapper xml:base sets wrap-sequence result base URI.

Validation: all 14 ab-wrap and all 17 ab-wrap-sequence upstream fixtures passed via Runner.runTest under `lake env lean /tmp/XProcWrapCheck.lean` (31/31, no executable rebuild). Atomic module builds; added a regression guard for comment placement across equal and unequal adjacent keys. Locale text-sort failures remain visible, not reclassified.

### 2026-10-29 — remaining implemented-step validation

Fixed p:set-attributes to consume its XProc 3 map option rather than the old attributes input port; QName-resolved generated attributes override prior values. Namespace-declaration keys raise XC0059 and non-XML/HTML input raises XD0038. p:compare rejects unknown comparison methods with XC0076 and incompatible document types with XC0077. Empty XML edit and XSLT document results retain application/xml instead of treating the empty child list as text.

Validation: Atomic module built and final source typechecked; added guards for map-driven attribute creation and empty XML document content type. Broader Runner fixture verification deferred because Runtime.olean was being rebuilt concurrently (first interpreter batch exited139; followup reported missing Runtime.olean). Existing failures remain counted until the next suite measurement.

## 2026-10-29 — ninth full measurement and scope corrections

`cd formal/lean4` is expressed as the tool workdir; command `.lake/build/bin/l4xproc --list-fails --list-unsupported > /tmp/xproc-suite-9.log 2>&1` measured **1884 pass / 309 fail / 1170 unsupported**, total3363, with the runner's five-second per-test timeout. Previous eighth run measured1832/356/1175. Build19 includes the local BOM/DTD/HTML loader, function-conversion option typing and pipeline-boundary XPath error mapping. No unsupported case is counted as passing.

Next changes awaiting measurement: externally supplied dynamic options excluded from nested-step static scope; EQName step declarations resolve correctly; recursive use-when availability detects cycles (XS0115); imported private steps are scoped inside exported declarations; absent caller input permits a declared default input; import loading errors map to XS0052. Atomic grouping, static structural validation, and inline decoding continue in parallel. Existing unsupported functionality and recursion audit remain open; this is not a complete XProc implementation.

### 2026-10-29 — inline decoding and text value templates

Inline base64 uses the existing XSD decoder and document character codecs. Inline XML/HTML encoding, unknown encoding, invalid base64, unencoded charset, encoded markup, and unknown charset return the specified XProc errors. JSON inline content retains its native value and reports XD0057 for malformed JSON. Binary inline documents remain explicitly unsupported.

Text value templates now copy XML nodes and attributes into XML content, preserve atomic sequence spacing, and reject attributes in text-only documents (XD0084). Inline expansion controls use `p:inline-expand-text` on non-XProc elements and unprefixed `inline-expand-text` on XProc elements; controls are removed from output.

Targeted built-binary validation: ab-inline 19 pass/0 fail; nw-tvt 8 pass/0 fail; p-inline 7 pass/0 fail/1 unsupported. Inline-expand-text 4 pass/3 fail and ab-contenttypes 29 pass/2 fail/1 unsupported exposed remaining static control validation and retained variable-node context issues outside inline construction. These counts do not replace the full-suite measurement.

### 2026-10-29 — explicit error details

ProcError carries `details : List XML.Node`; p:error preserves all input document children in this field while retaining the expanded error QName. Positional error constructors migrated in Core, Atomic, Loading, Viewport, ExtraSteps, Sequence; Runtime catch consumes this separately (root-owned). Atomic removes empty text nodes before classifying generated XML edit results, fixing empty-string replacement content type.

Validation: Core/Atomic/ExtraSteps/Viewport/Sequence module build passed (119 jobs), and a guard confirms both expanded QName and nested input detail tree survive p:error. Fresh Runner probes also confirmed all 15 set-attributes and seven nw-compare fixtures pass. Requested native document probes: doc-prop011/012/002, json-join010 and json-merge018 pass; doc-prop005 argument handling and json-merge019 unused inherited namespaces diagnosed as Runtime construction issues and handed to root.

### 2026-10-29 — dynamic pipeline binding checks

The p:run branch now checks primary port names as well as primary flags (XC0206/XC0207), permits declared input defaults when a run-input supplies no documents, validates required options and declared option types before execution (XC0200), and converts string keys for QName-keyed option maps. Dynamic use-when receives only declared static option values. Runtime source typechecking passed; executable fixture validation awaits the coordinated rebuild after suite10. Inline namespace exclusion and outer static use-when handling are separate remaining issues.

## 2026-10-29 — tenth full measurement

Build24: `ulimit -s 65520`, `export PATH=$HOME/.elan/bin:$PATH`, `lake build l4xproc` (explicit workdir `formal/lean4`), succeeded391 jobs. `.lake/build/bin/l4xproc --self-test` passed25/25. Full command `.lake/build/bin/l4xproc --list-fails --list-unsupported > /tmp/xproc-suite-10.log 2>&1` measured **1976 pass / 212 fail / 1175 unsupported**, total3363, five-second test timeout.

Subsequent improvements awaiting full measurement: variable node retention/property registry, catch/finally error context with retained p:error XML details and QName, DTD validation via existing XML.Validity, imported-source scope/cache/conditional pruning, p:run port/default/option validation, inline namespace exclusions, and atomic text/pack/query corrections. Imports no longer expose private steps globally. All new implementation stays in XProc31; no additional shared-module edits.

### 2026-10-29 — line counts, pack attributes, XML query input, lexical errors

p:text-head and p:text-tail now treat zero as all lines; negative head skips initial lines, negative tail removes final lines. p:pack supports typed wrapper attributes and xml:base. XQuery query documents use c:query text content for that standard wrapper, and serialize other XML query documents so direct element constructors are retained. p:error always carries an expanded QName (including no namespace) and ProcError.errorName separately preserves the lexical prefix for catch error documents; constructor migration covered the same helper files as details.

Validation: migration module build119 jobs succeeded. Final Atomic typecheck passed guards for zero/negative head/tail, no-namespace p:error name, and an XML direct-constructor query that returns a nested title. Target Runner batch temporarily blocked by root Runtime rebuild; no executable rebuilt here. pack007 remains a Runtime inline whitespace preservation issue, and xquery003 is document loading/media classification.

## 2026-10-29 — eleventh full measurement

Build28 passed391 jobs and25/25 independent regressions. `.lake/build/bin/l4xproc --list-fails --list-unsupported > /tmp/xproc-suite-11.log 2>&1` (explicit `formal/lean4` workdir; five-second per-test timeout) measured **2057 pass / 138 fail / 1168 unsupported**, total3363. Catch details/context, imports, DTD validation, namespace exclusions, text operations and p:run corrections account for substantial gains. Follow-up work is preserving static use-when semantics inside inline content, context-independent multi-document variables, and isolated filesystem fixtures with IO step support. No completion claim; remaining errors and unsupported categories remain visible in runner output.

### 2026-10-29 — isolated filesystem fixtures

Runner now mirrors support documents, pipelines, libraries, schemas and the current test into a temporary suite directory for filesystem tests. Copies contain actual bytes; symlinks and special files are refused. `t:file` text and nested `t:folder` instructions populate the temporary `testfolder`. Path guards reject absolute paths, schemes and traversal. The parent test process owns temporary cleanup, including after child timeout. Direct `--one` also cleans up. Runtime receives the canonical temporary root for write confinement; normal pipeline execution needs explicit `--write-root DIR` for filesystem writes.

188 of217 file environments use supported setup instructions. The other29 require false permissions, hidden flags or timestamps and remain explicitly unsupported. Missing runtime file operations remain unsupported independently. FileEnvironment module built (83 jobs); Runner source typechecked. A real ab-file-copy012 setup probe checked the copied test and exact nested file text, then removed its directory. Full runner measurement awaits filesystem-step integration.
