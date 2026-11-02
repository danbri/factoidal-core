# SVG standards implementation, overnight 2026-11-02

The SVG lane starts from `9c67291515833dd8b76f0da3f605a7d452943844` on
`codex/svg-standards-overnight`, in the isolated `factoidal-svg-overnight`
worktree. The existing viewer worktree remains unchanged.

## Environment and public DOM interface checkpoint

`tools/ensure-test-env.sh --check` exited 1: unrelated test submodules and
native release binaries are absent in the new worktree. No whole-suite or
zero-test score is inferred. The SVG fixture checker separately verified all
75 original pinned files and the unchanged 38-pair inventory. The broader SVG
corpus is being inventoried by the corpus lane.

The cold targeted source build exposed a real closure omission:
`FoafPresentationProofs` imports `FoafGeometryProofs`, and the presentation
tests import the first module. The script had checked these proof files
without emitting their `.olean` files, so a warm cache hid the missing outputs.
The script now emits both in dependency order. Their proofs and presentation
regressions passed in the fresh worktree.

`NativeSVG.parseRoot` now accepts a namespace-expanded SVG DOM root, explicit
embedding viewport and inherited paint style. The standalone string reader
retains XML/namespace/DTD validation and delegates to this same SVG root
reader. Public `Scene.artifact`, `Scene.samplePixel` and `Scene.samplePixels`
let HTML adapters use the actual SVG packed-data/WGSL producer and CPU sampler
without serializing/reparsing XML. The batch API constructs packed data once;
its equality with individual samples is proved by `rfl`.

Native regressions construct a namespace DOM directly, check inherited
`currentColor`, compare the complete artifact with the equivalent standalone
SVG, test embedding viewBox geometry, compare batch/single samples, and retain
foreign-root and malformed/DTD input checks. This interface checkpoint adds no
new SVG feature or rendering-conformance claim. It unblocks the shared
HTML/SVG renderer lane while substantive instancing work proceeds.

Evidence: `/tmp/factoidal-overnight-svg-{step0,fixtures,source-baseline,api-checkpoint}.log`.
The focused API/proof checkpoint exited 0. Builds use only the targeted Lean
closure and local outputs; no full library/native build is run. Before heavy
phases the lane requires at least 3 GiB free. Last precompile free space was
4.190 GiB. The stable runtime cache's patched source/object witness is verified
read-only; no shared runtime or engine output is changed.

## Next implementation

Implement same-document `defs`/`use`/`symbol` instances, reference identity and
cycle handling, style/transform order and real viewport clipping. The design
follows [SVG 2 structure](https://www.w3.org/TR/SVG2/struct.html#UseElement)
and [URL processing](https://www.w3.org/TR/SVG2/linking.html#processingIRI).
The corpus lane supplies original upstream relations; original fixtures,
denominators and tolerances remain unchanged. Acceptance alone is not a
rendering pass.

## Viewport clip foundation

SVG symbols need actual viewport clipping before they can be admitted. A new
`ClipRect` records local bounds and a Float affine transform. `DisplayNode.clipped`
keeps the content CTM independent from the viewport CTM: a symbol viewBox moves
and scales its contents, while its viewport rectangle stays in the containing
coordinate frame. Lowering transforms both frames through each parent and
retains nested intersections on each primitive. Existing reference traversals
remain declarative, with the same proved tail-recursive replacements extended
for the new constructor.

The packed storage adds three rows per clip after existing geometry, dash and
affine rows. Unclipped records retain their old bytes. Header mode bits preserve
line-cap and affine flags and encode clip count above those bits. Lean theorems
bind clip counts, payload lengths, record cursors and bounded clip-row access;
shader and host validate remaining storage and exact integer counts. The host
validation interprets only the ABI, with no SVG geometry or layout semantics.
CPU sampling, picking and WGSL apply inverse clip-local half planes rather than
world-space bounding boxes. Singular or empty clip frames paint and pick nothing.

Native tests independently describe a rotated square by half-plane equations,
including partial quarter-grid coverage, translated parent, distinct content
transform and nested intersection. Five generated artifacts include independent
full 64×64 RGBA expectations. These are backend diagnostics, not WPT cases or
proof that an SVG source document was interpreted correctly. Source/model/CPU
checks pass in `/tmp/factoidal-overnight-svg-clip-{model,wire,renderer,native,controls}.log`;
All five actual WebGPU controls passed every RGBA pixel exactly (4096 pixels
each, zero differing channels/max delta zero) on Apple Metal, using the frozen
raw bridge. Evidence: `/tmp/factoidal-overnight-corpus-clip-math/report.json`,
with full native-size PNGs and readback hashes matching independent expected
bytes. Standard small-engine build exited 0 (`...-clip-engines.log`), using the
verified runtime cache read-only and our own EM_CACHE/outputs. The rebuilt
SVG WASM passed 23 Deno tests; the remaining lab files passed 52 tests (75 total,
zero failures), including ABI rejection for fractional counts, truncated clips,
forged cursors, inactive flags and zero active bounds. Logs:
`/tmp/factoidal-overnight-svg-clip-deno-{isolated,other}.log`. Tests type-check
with `--no-config --no-lock` because the unrelated root Deno configuration
requires missing node_modules types; the original failed environment attempt
is retained as `...-clip-deno.log`. No type checking was skipped.

The selected original upstream symbol cases include CSS dimensions. The
[SVGWG February 2026 resolution and merged PR1059](https://github.com/w3c/svgwg/pull/1059)
clarify that width/height CSS properties apply to outer SVG (and rect/image/
foreignObject), but are ignored on nested svg/use/symbol; their XML dimensions
still apply. This supersedes conflicting older prose. Instancing tests must
check this rule alongside specified target style overriding inherited use style.

## Definition and instance reader (in validation)

The reader now collects original document IDs in a persistent `Std.TreeMap`,
keeping the first matching element in tree order, including a foreign element
that makes that target invalid for SVG use. Each entry retains an original
source path independently from its ID string. An active source-path stack
suppresses an ancestor or recursive use instance; duplicate ID strings alone
do not manufacture a cycle, and sibling instances do not share active state.
Expansion is total and fuel-bounded within the existing group-depth budget.

Definitions and uninstantiated symbols do not paint. Instances inherit the
host's paint style, then apply the target's own specified attributes/style;
target parents are not cloned into the instance. `use` appends x/y translation
on the right of its transform. Symbol and nested-svg dimensions establish the
percentage context and viewBox transform, while their actual rectangular
viewport clip retains its separate CTM. Explicit visible overflow is supported;
zero viewport/viewBox disables that instance. Partial container opacity still
requires a real compositing surface and is explicitly refused.

References prefer `href` to `xlink:href`, even for an empty href; fragments
percent-decode UTF-8 exactly once and do not decode plus as form whitespace.
Missing, malformed and cyclic references draw no instance without dropping
unrelated graphics. A host document URL can now be supplied to `parseRoot`,
`parse` or the transported `compileWithURL` export. The existing RFC3986 resolver
checks the resolved nonfragment document identity before choosing a local ID.
Original source xml:base context is retained across cloning; it is not replaced
by a use host's different base. External-document references remain explicitly
unsupported without fetching. URL equivalence follows this resolver's component
serialization; a complete WHATWG URL canonicalizer is not claimed.

Foreign qualified metadata attributes and xml:lang/xml:space are inert here;
xml:base affects URL resolution. SVG-qualified lookalike paint attributes still
fail namespace validation. Empty XHTML meta annotations used by original WPT
files are inert; active http-equiv metadata remains unsupported.

Native tests passed full rendering-field comparisons (only retained `tree`
inspection removed), plus independent raster rectangles for symbol viewBox,
use dimension override, nested hidden/visible viewport overflow, CSS dimension
ignore rules, duplicate/source identity, direct/indirect cycles, href precedence,
UTF-8/plus/single percent decoding, relative/absolute self URLs and original
xml:base across a differently based host. Logs:
`/tmp/factoidal-overnight-svg-use-{compile,native,url-compile,url-native}.log`.
The first version of a painter-order test encoded a translated rectangle in
world geometry rather than the instance's equivalent local geometry+CTM. The
reference fixture was corrected to the explicit equivalent translated group;
all rendering fields continue to be compared, without weakening the helper.
Standard small-engine build exited 0 (`...-use-engines.log`). The fresh
WASM passed 27 SVG Deno tests and 52 other lab tests (79 total, zero failures),
with type checking enabled under the isolated configuration. The original
negative list contained empty use/defs/nested-svg cases; those three were
replaced by explicit zero-paint checks while all other negatives and all pixel
tolerances remain unchanged. The first 26-pass/1-failure run is retained, along
with the final green logs `...-use-deno-final.log` and `...-use-deno-other.log`.

All TEN nominated original pinned upstream relations matched independent
browser test/reference renders exactly through the fresh Lean WASM/WGSL path:
zero differing pixels/max delta zero in every case, with ten controls passing.
The selection includes the four symbol display/CSS cases, two symbol dimension
override cases, two svg dimension override cases, use-svg-inline-css, and zero
symbol viewBox. The original HTTP document URL is a host input to Lean URL
resolution; no browser bbox/layout is fed to the candidate. Evidence:
`/tmp/factoidal-overnight-corpus-use-symbol/capture/{report,capture}.json` and
its `diagnostics/use-symbol.json` selection. All 601 inventory rows remain;
591 unselected rows are explicitly unavailable in this diagnostic. This is
10/10 selected rendering evidence, not a full-601 or full-SVG conformance claim.

Frozen engine SHA256: WASM
`6e1de3a3fbf8bb2b215fcd53e272a35978c2def46223c90848f5069db816c58d`,
glue `4716f7b83cb27c462d3223f2761e00e3177bfa5b017204699fc281665d6f3607`.
The capture records exact matching source/TS/runtime witness identities.
The broader baseline reason inventory contains no root-sizing unavailable
cases yet, so the next implementation priority is actual curved path geometry.

## Proved formatter cache checkpoint

The root lane's narrow `Rendering/FloatFormat.lean` patch is ported without its
HTML-specific modules. The bit-keyed cache stores the existing formatter's
`javaDoubleString(bits)` result. Its invariant, single-step theorem and general
accumulator theorem prove `formatList xs = xs.map format` for **every Float
list**, preserving order and every decimal byte without assuming Float equality
implies bit equality. The csimp wrapper keeps the original reference visible.
A central `L4Factoidal.lean` import registers the module; the small lab's targeted
core closure, source inventory and SVG link explicitly include it. No full
library/native build was run.

The actual generated C `Scene_json` caller invokes
`l_L4Factoidal_Rendering_FloatFormat_formatList`; its excerpt and source/runtime
hashes are in `/tmp/factoidal-overnight-svg-format-caller.txt`. A theorem that
was not selected at this caller would not establish the optimization executed.
The proof prints only the standard propext/Classical.choice/Quot.sound axioms.

The standard small build and all 79 type-checked Deno tests pass. Full raw UTF-8
artifacts are byte-identical before/after for the ten original use/symbol cases
and a 512-rectangle fractional scene, including every data, shader, probe and
inspection byte. Before/after manifests and exact outputs are under
`/tmp/factoidal-overnight-svg-format-{before,after}`. Five warm repetitions of
the fractional case measured median 585.50 ms before and 355.38 ms after
(approximately 1.65×); these are diagnostic timings under concurrent test
activity, while the general proof and exact raw bytes are the correctness gates.

The fresh formatter engine also matched all ten upstream GPU cases exactly,
with all three sensitivity controls passing for every case. Evidence:
`/tmp/factoidal-overnight-corpus-formatter-symbol/run.json`. New WASM SHA256 is
`1829bdb48f3cf6620ee583349033ad6484321c6f684450249258dcd0622e0a08`;
MJS glue remains `4716f7b83cb27c462d3223f2761e00e3177bfa5b017204699fc281665d6f3607`,
and TS source remains `38511f26402f218874db4090d090314f582dd720fd92bec44473df4e46b6f370`.
The broader 601-case run has separately frozen this exact runtime and source
witness. It remains pending; this checkpoint claims no complete-corpus score.
