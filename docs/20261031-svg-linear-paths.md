# Retained SVG linear paths and compound glyphs

Tracking: https://github.com/danbri/factoidal/issues/1209.
Source branch: https://github.com/danbri/factoidal-core/pull/271.

Lean now parses bounded filled M/L/H/V/Z paths, including relative commands,
implicit lineto after moveto, multiple subpaths, closepath current-point
restoration and implicit fill closure. Contours are retained as geometry;
CPU and generated WGSL use the existing shared expression predicates for
winding tests. Nonzero/evenodd fills and inverse affine transforms apply.
The SVG 2 grammar is the target, including rejecting trailing decimal points:
https://www.w3.org/TR/SVG2/paths.html#PathDataBNF.
Curves, arcs, stroked paths, joins, pathLength and partial-prefix recovery after
invalid path data remain unsupported. This is not complete SVG path support.

Limits: 65536 raw path characters before whitespace trimming, 4096 tokens,
128 subpaths and 512 points/edges. The numeric scanner examines at most 49
characters and refuses tokens above 48. Relative coordinates retain the 1e6
magnitude limit. Existing global scene/storage budgets are unchanged.

Each temporary bitmap glyph serializes as a compound path containing exactly
its cell squares. This is vector geometry, not text shaping or SVG font support.
Local bounding boxes avoid unnecessary winding tests. Runtime storage arrays
make the generated shader independent of scene count and primitive kinds.
The Lean scene and shader still own drawing semantics; the host transports data.

## Fresh validation

The complete engine build passed native scene, geometry, policy, affine,
path and capacity controls. Rebuilt WASM passed 69 Deno tests and 12 native C
coordinate checks. The previously failing whitespace-budget regression passes.

Actual Chrome 156.0.8078.76 / Apple metal-3 non-fallback WebGPU rendered the
new eight-person scene in 20 resident frames, with one pipeline, one upload,
two buffers and one texture. Median frame plus readback was 21.25 ms; the earlier
same-host old representation measured 131.4 ms and the initial path run 22.0 ms.
These are finite host round-trip measurements, not GPU-only or interactive
frame-rate guarantees. The new 800x600 RGB image is byte-identical to the old
representation, SHA256:
`c8dba3ad854d8d585b882609a02d0eb3bd29ee46688be93344fec3b7cebbdacc`.
Primitive count falls 1880 to 292, storage floats 37608 to 32792, and SVG characters
128347 to47845. The dense 16 scene falls 6748 to 716 primitives.

All 38 original WPT cases remain in the measured inventory. This feature alone
does not add official passes: percentage lengths, markers, definitions and
other features still block those cases. The independent oracle comparison is
recorded separately from local glyph-image equivalence. Generated images and
WASM remain external artifacts, not committed files; older executables do not
automatically gain this change.

Fresh independent comparison: 2 matches, 23 unsupported, 13 unavailable,
zero mismatches or rejections. The two matches have zero channel/pixel
difference. The linear-path gallery also rendered with Lean readback checks.
Independent source review found no blocker; f64/f32 boundary agreement remains
empirical, and no complete SVG or GPU refinement theorem is claimed.
