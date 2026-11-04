# Reuse GPU resources for compatible scene edits

The local HTML renderer created a device, shader module, pipeline, storage
buffer and readback texture after each edit. The Hub worker did the same.
`createOffscreenSession` can now update an existing session when dimensions,
shader source and packed-data length agree. It requests a new plan from Lean
and requires the complete descriptors and command sequence to match before
uploading the full replacement buffer. A different shape still requires a
new session.

The update also copies the new pixel expectations. Every draw continues to
check the returned image. A failed upload or readback makes the session
unusable. Updates and draws cannot overlap; the editor and worker serialize
GPU work. The worker skips queued requests superseded by a newer render.

This change concerns host resource lifetime. It does not claim a new Lean
equivalence theorem. Scene construction and render-plan validation continue
to run in Lean; the separately proved CPU sampling optimization is recorded
in [the path preparation note](20261103-lean-path-sampling-preparation.md).

## Validation

Four Deno transport tests pass, including changed expectations, incompatible
dimensions/shaders/buffer lengths, concurrent access, invalid numeric input,
failed sessions and cleanup. Tests use the existing Lean render-plan WASM
with a mocked GPU; they do not count as real GPU rendering.

`web-render/check-gpu-updates.mjs` also runs Chrome WebGPU. Three complete
32 by 24 images from a reused session exactly match separately created fresh
sessions (2,304 pixels total). An intentionally wrong pixel expectation still
fails. An actual editor color edit retains one device/pipeline and performs
a second upload and draw. The proposed Hub worker retains one pipeline across
two changed images and drops the earlier queued request.

The worker test intercepts the proposed worker and transport source against
the existing frozen Hub engines. It does not qualify a newly published bundle
or deploy the Hub. The report records source hashes, browser version and both
runtime provenance records. Initial local evidence is under
`/tmp/factoidal-gpu-updates-combined-check-final`.

Sample timings for the two updates were about 1.0--1.1 ms for update plus draw,
versus 3.0--3.1 ms for fresh setup plus draw. This is a small functional test, not a
throughput benchmark or an estimate of full-page speed. Lean compilation and
GPU work proportional to page size remain separate costs.
