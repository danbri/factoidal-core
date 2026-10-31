# Shared affine algebra and actual raw WebGPU SVG comparisons

Tracking: <https://github.com/danbri/factoidal/issues/1209>.
The earlier live-policy work remains separate from these SVG feature/evidence
commits. No release/build dispatch or native executable packaging occurred.

## Reuse audit and shared implementation

`Math/Matrix.lean` already provides exact-rational TOAN/MathML operations, but
its entries are `Option (Int × Int)` and its matrices are runtime-checked lists.
Contrary to its former header, that module contains no matrix correctness or
shape-preservation theorems; the comment is corrected. `MathML/Rat.lean` uses
raw pairs and normalized arithmetic, with zero denominator normalization to
0/1. It is not a refinement type guaranteeing valid rational inputs. No matrix
inverse routine was found. These are useful exact finite test oracles, not a
Float GPU matrix representation or a library of inherited inverse proofs.

The [TOAN design record](designissues/2026-09-07-lean-toan-parity.md) describes
an independent symbolic computer-algebra layer, conceptually closer to SymPy
than a NumPy array backend. `formal/fstar/Math.Expr.fst` explicitly says no code,
API or algorithm was ported from SymPy or another CAS. NumPy and SymPy are not
runtime dependencies of this renderer.

`Math/Affine.lean` now supplies one typed six-field `Affine2 α`, parameterized
by explicit scalar operations. It provides identity, column-vector composition,
determinant, optional inverse, point versus direction mapping, inverse-transpose
unnormalized normals, four box corners and a homogeneous 3×3 embedding. SVG uses
its Float specialization. Exact regression checks instantiate the existing
MathML rational operations and compare with existing TOAN matrix multiplication.
There is no second general SVG matrix library.

Three small kernel-checked properties state that direction mapping ignores
translation, the homogeneous embedding is exactly 3×3, and the actual Float
backend refuses a determinant accepted by its zero test. They do not prove
algebraic correctness, numerical stability, rational-to-Float refinement or GPU
pixel equality. No new axioms, sorry or native_decide are used. The printed dependencies are
none for direction mapping, propext for shape, and the standard propext /
Classical.choice / Quot.sound for the Float guard theorem; runtime/extern
implementation equivalence is not proved by these statements.

## SVG transform behavior and numerical boundary

Group/primitive transform lists implement matrix, translate, scale, rotate with
optional center, skewX and skewY in SVG order. CPU hit predicates and generated
WGSL use the inverse composed CTM before the same typed local-shape conditions,
so stroke geometry follows nonuniform scale/shear rather than a guessed scalar
stroke-width adjustment. Singular CTMs have effective opacity zero in both CPU
sampling and packed GPU rows; an identity coordinate fallback cannot paint.
The local affine fixture's final singular red full-canvas rectangle does not
cover its other shapes on the actual GPU.

Each transformed record appends eight inverse floats; identity records retain
the existing size. Primitive/input/storage budgets remain unchanged. Numeric
input magnitude still caps at 1e6, transform lists at 32 functions, and finite
composed/inverse coefficients at 1e9. Near-singular matrices can be refused.
These are resource/numerical profile limits, not a condition-number or stability
guarantee. GPU arithmetic is f32; Lean CPU arithmetic is Float/f64. Extreme
coordinate cancellation and raster edges still need a general error analysis.

An actual transport defect was caught before GPU use: Lean's ordinary Float
string formatter prints six decimals, turning a 1e-9 inverse coefficient into
zero. SVG data now reuses standalone `Tdb2.javaDoubleString(bits)` with an integer
fast path. Regressions retain tiny inverse and geometry coefficients. This
repairs decimal transport loss; it does not remove f32 rounding on the device.

Root transforms, nested viewports and CSS transform-origin/transform-box remain
explicitly unsupported. Existing FOAF integer drawing/hit/policy records are
unchanged. Arbitrary SVG has no interactive policy/picking controller yet;
this change does not extend the FOAF policy theorem to arbitrary Float SVG.
The normal/corner APIs do not establish real-number extrema or normal-length
preservation for arbitrary scalar operations.

## Validation and actual GPU results

Named Lean shared-affine, prerequisite and transform tests pass. Exact checks
cover 16 matrix products, four determinants/two-sided inverses/point/direction
mappings, normal/tangent orthogonality, four-corner shape and singular refusal.
NumPy 2.5.2 independently checks 16 actual Lean-emitted IEEE64-bit fixtures at
rtol/atol 1e-12; the explicitly measured small-fixture f32 round-trip error is
0, within stated 1e-5. This is a finite numerical check, not a bound for all
accepted inputs. SymPy is unavailable and was not installed.

The warm SVG C/WASM target was relinked with cached runtime objects; the full
suite passes **66 Deno tests, 12 C checks**, with entrypoint/test typechecks.
Four native SceneSVG groups and three full-FOAF capacity groups also pass:
default8 has 1,880 primitives/37,608 floats; dense16 has 6,748/134,968. These counts
remain unchanged for identity transforms. The two pre-existing runtime tempfile/
tempdir linker warnings are unchanged.

Default installed Chrome exposes a real Apple `metal-3` adapter with fallback
false. No GPU bypass flags were supplied. The new browser test host transpiles
the existing TypeScript bridge, uses the exact Lean SVG/WGSL and render-plan
WASM modules, renders to an offscreen WebGPU texture, and reads pixels back.
It does not invoke browser SVG rendering for the candidate. The independent
reference images use the browser's SVG implementation separately.

Actual 38-case full-image comparison: **2 matches, 23 unsupported, 13 unavailable,
0 mismatch and 0 rejection**. Both unchanged WPT fallback cases match all 800×600
pixels of their independently captured references exactly (maximum channel
difference 0, differing pixels 0). The 13 unavailable cases remain nine original
runtime/resource requirements and four independent-browser disagreements. No
denominator changed or tolerance was added. All source/WASM/browser/image
hashes, actual adapter facts and metrics are in generated reports.

The local 11-primitive affine gallery and actual 1,880-primitive generated FOAF
SVG also pass GPU readback references; they are not extra WPT passes. Cold
measurements were about 54 ms compile +242 ms GPU setup/render/readback for the
local gallery, and 703 ms +356 ms for default8. These include pipeline/device
setup and readback; they do not measure resident-frame throughput or support a
CPU/GPU speed ratio. Resident-resource/batch benchmarks are the next performance
step. Native Deno adapter lookup remains unavailable in this session; no native
window presentation claim follows from the browser-host GPU result.

Generated evidence lives outside source:
`/private/tmp/foafnaut-svg-browser-comparison/report.json`,
`foafnaut-svg-browser-gpu/candidate.json`, `foafnaut-affine-browser-gpu/affine.png`,
and `foafnaut-default8-browser-gpu/candidate.json` (all under `/private/tmp`).
The independent harness retains upstream fuzzy ranges and full-image diffs.
See the [declared feature target](designissues/2026-10-31-svg2-static-feature-target.md)
for the next paths/viewports/strokes/style/reuse/paint/text work.
