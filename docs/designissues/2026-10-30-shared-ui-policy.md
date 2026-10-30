# Shared geometry and renderer-independent layout admission

Owner request: express the layout policy once in Lean, derive drawing and
hit-testing from shared geometry, and apply the policy to both generated SVG
in a Web Platform application and native graphics. Applications must be able
to tune parameters without silently weakening their chosen assurances.
Graphics work: <https://github.com/danbri/factoidal/issues/1209>.

## One policy, bounded configurations

`L4Factoidal.UI.LayoutPolicy` owns the checker and theorem. The named profile
`experimental-graph-browser-v1` allows overlap budgets of 300–700 basis points
(3–7%) and target check rates of 12–24 Hz. Its default is 500 basis points and
12 Hz. These ranges are an **experimental human design**, not a theorem that
these values are optimal, practical on every device, or sufficient for usability.

An `ApplicationPolicy` chooses a closed subinterval of each profile range.
A `Config` contains proofs that its values lie within those application ranges.
Validation refuses invalid values; it does not clamp them. An application with
a 5% ceiling cannot obtain a 7% configuration through `validateFor`.
`certify_application_bound` connects accepted scenes to that application ceiling.
The portable adapter's `retune` retains the same application bounds.

The metric for each visible node is the sum of pairwise intersection areas of
its viewport-clipped bounding box with other node boxes. The checker requires
positive node area and `10000 * overlapSum ≤ overlapBps * nodeArea`. Summing
pairwise intersections can overcount regions where several nodes meet. This is
a conservative bounding-box metric, **not a percentage of painted pixels**.
Missing/zero-area footprints fail. An empty list passes vacuously and establishes
no non-empty-display property. Nodes with the same box remain distinct.

## Geometry source and actual runtime connections

FOAFNaut constructs `PaintedPart` records containing a graphics shape, visibility
and an interaction target. Drawing uses their shape list. Picking searches the
same records in reverse paint order and applies `NativeGeometry.hit`. Chrome
can therefore block underlying graph interaction; painted control disks have
their actual drawn radius. Hidden fixed GPU slots cannot be hit.

`FoafGeometryProofs.lean` connects a successful pick to a visible part, a true
shape hit and membership of that shape in the rendered scene. It also connects
runtime layout reports to the shared checker. Tests cover non-square viewports,
control edges, blank card corners, chrome occlusion and overlapping nodes.
The integer hit predicates do not establish equality with floating-point GPU
rasterization, antialiasing or pixel-center conventions.

Visible node footprints are derived from those same painted pieces. Edges and
browser chrome are outside the node-overlap metric. Labels contribute their
bitmap glyph bounds; this is still the temporary font, not general text layout.

## Scene admission and rendering options

`L4Factoidal.UI.Presentation` is generic over a scene type and its authoritative
footprint function. `Approved` retains a scene and its `LayoutAccepted` proof.
`inspect` admits or refuses a candidate. `submit` can retain the last approved
scene when a later candidate fails. A changed context clears the old scene;
this prevents retaining a scene whose viewport or other geometry context changed.
The operational theorem `submit_accepted_candidate` connects an accepted result
to the actual candidate and its layout property.

There are two checked FOAFNaut exports:

- `foafnaut_export_svg` serializes the admitted scene to static SVG.
- `foafnaut_picture_checked` emits its native graphics artifact.

Both call the same `Presentation.inspect`, with `Model.footprints`. The legacy
interactive frame/snapshot APIs still provide diagnostic reports and explicitly
mark `enforced:false`. They are not silently promoted to checked presentation.

Checked exports also require a separately supplied expected configuration.
Lean refuses a model whose typed configuration differs. The portable FOAFNaut
adapter retains the normalized configuration privately at initialization;
editing the serialized model cannot widen its budget or application ceiling.
Reinitialization with a different configuration invalidates older models for
checked export. The browser passes its bound configuration separately too.
This is application-context binding, not authentication: raw callers must
supply their trusted application configuration, not copy it from untrusted
model JSON. Configuration parsing and model parsing reject nesting above eight
before entering the recursive JSON parser.

The browser component `policy-demo.html` displays generated SVG and offers that
exact SVG for download. `run_foaf_svg.ts` can send the same generated SVG through
Factoidal's XML parser and Lean SVG compiler to WebGPU. Portable JavaScript and
TypeScript code transport strings, input and device operations; it contains no
copy of the overlap checker, RDF layout algorithm or SVG serializer.

Other renderers can use the generic Lean admission API. `UI.PolicyProtocol`
also exposes strict JSON `defaults`, `configure` and `check` operations through
the lab's small WASM bridge. Supplying boxes to that generic API does not prove
that an arbitrary renderer uses those boxes. The FOAFNaut exports provide the
stronger connection by deriving them from their own drawing records.

## Timing and remaining assurance boundaries

The native FOAFNaut window now uses `NativeFoafPresentation.Session` and the
opaque `FoafLiveBridge` WASM API. Candidate geometry, fixed policy and approved
offers stay in Lean. After a successful surface submission the host acknowledges
that offer's token; pointer-down uses the acknowledged scene. This does not
claim GPU completion. Stale acknowledgments cannot advance the displayed scene.
Changing viewport clears approval and pointer targets until the new geometry
passes the same checker. Preparation of draw buffers and diagnostics is cached
in Lean per render offer. Each WASM instance permits one session initialization,
so tokens cannot be reused by restarting that holder.

The [live presentation worknote](../20261030-foafnaut-live-presentation.md)
records the controller, bridge, proofs and tests. The older raw/model APIs and
browser component retain their previously stated static/diagnostic semantics.

`Presentation.submit` refuses a backwards clock and prevents checks occurring
closer than the configured interval. This is a **frequency ceiling**, not a
proof that an operating system will schedule a check at least 12 times a second.
`PolicyProtocol.targetIntervalMs` is the rounded-up scheduling target. The static
browser and export demos check on request, and say so. Native admission retries
continue while physics is paused. Browser live integration, deadline/expiry
behavior and host callback-liveness guarantees remain unfinished.

The theorem is conditional on supplied geometry, configuration and time. It does
not prove GPU execution, browser layout, DOM mutation safety, font behavior,
device limits reported by a driver, or pixel equivalence across renderers. A
consumer must not alter an admitted scene and reuse its admission result.
No npm public API shipment is claimed by this source prototype.

## Validation record

Named Lean compilation passed for the policy, JSON protocol, presentation and
their tests. All ten native FOAFNaut state-test groups passed after the shared
geometry refactor. The SVG capacity tests accepted a complete 8-person scene
(1,880 primitives / 37,608 floats) and a dense 16-person scene (6,748 primitives /
134,968 floats), with selected CPU sample comparisons and explicit size refusals.
These are local regression tests, not SVG conformance scores.

The fresh warm WASM build and macOS packaging passed 58 Deno tests and 12 C
coordinate checks. Tests exercise actual WASM refusal of modified application
bounds, modified chosen configuration and excessive JSON nesting. The relocated
Mac package passed checksums, all four compiled CPU modes, native-library loading,
checked SVG export and compilation of that SVG by the packaged SVG executable.
The browser assets and both WASM engines are present in the package.

Browser automation currently fails before connection because its
tool transport lacks sandbox metadata; no visual-browser pass is inferred.
The native GPU probe returned no adapter in this execution environment. Checked
SVG and its policy JSON were exported, but that probe produced no raster image.
