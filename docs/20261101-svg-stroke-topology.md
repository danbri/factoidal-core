# Stroke topology contracts — 2026-11-01

`labs/demos/foafnaut/SVGStrokeProofs.lean` proves four contracts over the actual `SVGStroke.edges` implementation. Open contours contain exactly the consecutive vertex pairs after its numeric zero-edge filter. A nonempty explicitly closed contour contains exactly those consecutive pairs plus the last-to-first seam, filtered identically. The two membership equivalences retain both allowed-edge provenance and the actual Float comparison predicate. Thus these are exact structural descriptions, not only subset bounds that could also allow every edge to disappear.

The generic zipper lemma is proved by induction on the list. The rendering code is unchanged. These theorems concern edge construction; they do not prove correct antialiasing, geometric distances, dash arithmetic, cap placement or Float/GPU equivalence. They describe the implementation's Float inequality test rather than assuming it equals mathematical real inequality for every representable input.

The proof file checks with Lean 4.33.1 and is included in build-engines.sh source checks. No new runtime module or heavy WASM build is required.

Mutation check: an isolated copy of SVGStroke changed `if c.closed then c.points.take 1 else []` to unconditional `c.points.take 1`. The mutated runtime module compiled successfully. Checking the unchanged proof file against it failed at `edges_open_exact`: Lean could not establish equality between the list with a forced closing seam and the consecutive-pair list. The normal implementation passes without warnings. Temporary mutation files live under `/private/tmp/svg-stroke-topology-mutation`; tracked rendering source was not mutated.
