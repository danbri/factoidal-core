# Browser foundation work after the first WPT baseline

3 November 2026. Local implementation authorized in the side conversation,
after the [initial baseline](20261103-browser-wpt-baseline.md). Source is in
`source/factoidal-web-render-overnight`; measurements below preceded the
4 November source checkpoint. This is not a published release. This work does not build `foafnaut2525.app`.
The [measurement manifest](../tests/browser-wpt/foundations-20261103.json)
records all denominators, final artifact hashes and report/log hashes.

## Parser diagnostics and tokenizer

The [diagnostic audit](20261103-html-parser-error-count-audit.md) is the
main follow-up requested by the owner. All 446 differing document-error
counts now have durable, reproducible case records. The count remains
446; categories do not turn failures into passes. There are 280 cases
with legacy/new error sections, 141 with empty expectations and 25 for
closer algorithm review. Within the mismatches, 436 have the correct tree.

Fresh unchanged upstream fixtures, without an exclusion mask:

| Measurement | Pass | Fail | Not run | Total |
| --- | ---: | ---: | ---: | ---: |
| HTML tree construction | 1,963 | 10 | 0 | 1,973 |
| Tree construction through DOM arena | 1,963 | 10 | 0 | 1,973 |
| Tokenizer tokens and error codes together | 7,047 | 6 | 0 | 7,053 |

Tokenizer token output alone has 7,050 passes and three failures; error
codes alone have 7,049 passes and four failures. One case fails both.
The four formerly skipped surrogate cases now execute and pass through
`L4Factoidal.HTML.CodePointTokenizer`. It decodes UTF-16 units and retains
lone surrogates as numeric character tokens. Ordinary scalar inputs still
use the existing tokenizer state machine, and the entire scalar fixture
set runs through this adapter too. No fixture is rewritten as U+FFFD.

This is limited code-point support, not full DOMString support. Raw
surrogates entering String-valued tag, attribute or comment buffers are
explicitly refused. The production HTML document String entry remains
scalar-valued. The small UTF-16 singleton theorem uses no axioms; the
broader tokenizer is tested code, not a proved complete HTML tokenizer.
Review replaced compiled UTF-16 decoding with a tail loop and checked its
equality to the reference decoder. This does not extend tokenizer coverage.

Authoritative run:
`/private/tmp/factoidal-browser-foundations-20261103/parser-verified/`.
The runner validates fixture blobs, module-cache hashes and harness source
stability. An earlier run preceded a usage-message edit; use the
`parser-verified` report for that recorded run. Review subsequently made the
code-point test module reachable from the harness by an import; that changed
the harness source hash. The historical parser measurement was not rerun.

## Synchronous JS/DOM integration

`quickjs.mjs` can now expose a bounded synchronous string capability to
the isolated QuickJS WASM heap. A worker-private Lean WASM instance
parses and applies each supported DOM command before the QuickJS call
returns. The guest refreshes its connected-node records from Lean.
The raw capability is removed from the guest global object before page
scripts run. Production worker, document client, server whitelist and
package file list are wired to `script-engine/lean-dom.mjs`.

Actual QuickJS/Lean tests now cover child text mutation observed through
the parent in the same script turn, immediate ID rename lookup, removal
from connected ID lookup after parent text replacement, `isConnected`,
listener removal, unchanged unrelated nodes, exceptions and heap isolation.
The original foundation run passed 12 scripting tests. Review added three
actual-engine regression tests; all **15 now pass**. Absent attribute reads
check own properties, before and after snapshot refresh. Bootstrap parses its
data as JSON, preserving real `__proto__` attributes. Invalid attribute names
throw an ordinary guest Error named `InvalidCharacterError` synchronously;
this does not install a `DOMException` class or claim full WebIDL behavior.
Oversized Lean responses are refused before committing command history, so a
caught response-budget error cannot retain that rejected command.

The adapter currently reparses the source and replays a bounded command
history for every mutation. This establishes ordering for the supported
operations but has poor scaling. Persistent Lean DOM handles are the next
implementation step. Disconnected-subtree ancestor updates remain
incomplete; so do Node creation, general selectors, layout queries,
promise jobs and the browser event loop. This does not close
[issue 1232](https://github.com/danbri/factoidal/issues/1232)
(scripts observing their mutations and defined layout queries).

The original updated probe used this actual synchronous capability. Its
historical 13:54 run is preserved at `quickjs-final/`, with guest SHA256
`01d7d1f13c3e9acf82de152ea213be36bc7a3faba7360eeaf96a54e90fc739b2`.
A fresh run of the reviewed binding finished at 16:34 UTC against the same
native/WASM engine bytes. Its full 784-document result is unchanged:
**zero complete PASS documents**;
367 ERROR, 27 INCOMPLETE, 229 UNAVAILABLE, 136 FAIL, 23 HARNESS_ERROR and
two UNSUPPORTED. Individual assertions have 103 passes and 1,342 failures.
Local integration tests and broad WPT conformance are separate evidence.
Fresh report:
`/private/tmp/factoidal-browser-foundations-reviewed-20261103/quickjs/`.
Its guest SHA256 is
`929a12d479668f234c25b8c00f8f4c7ff0cda2ebbde9594e1ec86e93811c00e8`.
The measurement manifest keeps both reports separately and records the new
bridge/adapter hashes, runner hashes and exact engine identities. No historical
report or original fixture was overwritten.

## Reader text size and builds

The HTML development host has A−, A+ and reset controls, from 50% to 250%.
The requested percentage reaches Lean CSS computation, shaping requests
and layout. Scaling occurs once after inheritance; it changes glyph size,
line heights and wrapping at the same viewport/CSS widths. It does not
resize a finished screenshot. Font sizes are rounded to the integer-pixel
font-provider contract.

Targeted Lean rendering/document guards pass. Two additional native/WASM
tests pass: a line fits at 100% and wraps at 200%, with identical complete
scene JSON from both backends; invalid scales are refused consistently in
layout and shaping requests. Run:

```sh
node --test labs/demos/foafnaut/web-render/document-text-scale.test.mjs
node --test labs/demos/foafnaut/web-render/script-engine/*.test.mjs
python3 -m unittest discover -s tests -p test_package_web_render.py
```

The ten package structure/control tests pass. This is not a new live
Chrome/GPU interaction or screenshot validation. Frozen development
bundles on previously reported ports are not automatically updated.
The native CLI and web WASM assets were rebuilt locally using the targeted
build script. They remain development artifacts, not a macOS app bundle.
The final native rebuild produced the same binary bytes as the tested
native/WASM pair. A fresh provenance check matched 125 source/generated-C
files and rendered 480,000 pixels in a native process with no browser-library
markers in its linked/loaded library logs. This is source/build and runtime
evidence, not a formal binary correctness proof.

The old runtime-cache path had disappeared. `/private/tmp/l4wasm-build`
contained a Lean 4.33.1 runtime whose patched `object.cpp` and `object.o`
exactly matched the previously recorded witness. An isolated directory of
read-only references was made under the work directory; all 889 runtime
input objects were hashed and confirmed unchanged after the WASM build.
The linker reports signature warnings for `lean_io_create_tempfile` and
`lean_io_create_tempdir`; rendering tests pass, but these unrelated I/O
entry points are not exercised or qualified by this work.

## SVG Tiny: complete original inventory, no passing claim

The official
[2008 SVG Tiny 1.2 archive](https://www.w3.org/Graphics/SVG/Test/20080912/W3C_SVG_12_TinyTestSuite.tar.gz)
is pinned by SHA256
`2203d6f44178cbb3853bdc7abe865f4e7e42506727ecc9e34b408b6f33e2e718`.
Its `svg/` directory contains 496 original tests, all marked approved and
accepted, including one UTF-16 file. The runner uses that actual inventory
rather than the overview's 495 summary.

The [saved admission report](../tests/browser-wpt/svg-tiny-admission-20261103.json)
records all 496 cases: **zero admitted, 495 unsupported, one unavailable**.
First failures are `baseProfile` (486), DOCTYPE/DTD (four), `nav-next`
(three), `focusable` (one), namespace well-formedness (one), and the UTF-16
byte-decoding boundary (one). These are first blockers, not complete
feature diagnoses. Visual conformance remains NOT_RUN for every case.
The source bytes, labels and metadata are unchanged; no derived `svggen/`
file or browser renderer is substituted.

This exposes a basic profile-admission gap before drawing features can be
meaningfully measured. The next SVG work is to implement the relevant
root/profile and foreign-metadata rules, preserve all remaining failures,
then add SVG text/font support and qualified reference comparisons. A
scene being accepted must never be counted as a visual pass.

All temporary logs and reports are under
`/private/tmp/factoidal-browser-foundations-20261103/`. Durable test runners,
diagnostic evidence and this note remain in the checkout for main-thread
review. The earlier WPT baseline was not overwritten.
