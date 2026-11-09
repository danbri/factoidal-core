# Frame cost: where the time of a frame goes, and partial compile

Date: 2026-11-09. Author: partialframe, a subagent of session depmap-0e, branch
`wip/partialframe`. Related: https://github.com/danbri/factoidal/issues/1268 (responsiveness),
`docs/designissues/2026-11-09-web-fonts-and-paint-only.md` section 5, `docs/designissues/2026-11-07-foafnaut-frame-pipeline.md`.

## 1. What was measured and how

Tool: `labs/demos/foafnaut/frame_split_bench.ts`. It loads a page in the engine (`loadHTML`,
`prepareHTML`), takes `compileLayers` answers as the window does, and on this machine's GPU
(Apple silicon, `navigator.gpu` of Deno 2.9 / wgpu, off screen; no window, no present) splits
a frame: engine compile (`engineMs`, `compileLayers` of the same request again, so the kept
page layer when nothing changed), the host's draw call, and the GPU pass. `device.queue.onSubmittedWorkDone`
is polled in steps of about 13 ms in Deno, so one pass cannot be timed: passes are timed by
putting N of them in one submission and taking the difference (`--variants`). `--export` writes
a scene (`.json`, `.floats`, `.tiles`); Chrome's Dawn runs the same scene with the same pass
timing (`chrome_scene_bench` in the agent's scratch, not committed), which is the Hub's GPU.

Pages: `pages/spinal-tap-sparql.html`, `pages/status.html` (text-only and large), and a live
Wikipedia article (a snapshot in scratch, not committed). Sizes: 1600 by 1000 at pixel ratio 1,
2880 by 1800 at ratio 2 (`zoomUnit` 200). The page layer is the view plus margins:
1600 by 1959 and 2880 by 2694 pixels.

## 2. Findings

The scene is one full-screen triangle (`NativeSVG.sceneShader`): each pixel takes 4 samples (16 at
an edge, only when the scene has at most 65,536 rows); each sample walks the primitives of its
32-pixel tile and, for a path, runs `windingContains` over all its edges. There is no CPU
compositing, no glyph atlas, no MSAA, and no buffer rewrite beyond `queue.writeBuffer` of the
storage floats.

Per-pass GPU time of the page layer (ms; Deno/wgpu native, then Chrome):

| page | 1x as shipped | 1x 4 samples | 1x 1 sample | Retina as shipped | Retina 4 samples | Retina 1 sample |
| --- | --- | --- | --- | --- | --- | --- |
| Spinal Tap (629 primitives, 18,001 edges) | 57 / 81 | 23 / 21 | 5 / 3.8 | 57 / 65 | 52 / 53 | 10 / 12 |
| status (1,823 primitives, 57,704 edges) | 17-20 / 23 | 16 / 19 | 3 / 3.3 | 45 / 55 | 43 / 46 | 8 / 11 |
| Wikipedia article (3,974 primitives, 56,443 edges) | 22 / 22 | 21 / 17 | 7 / 3.8 | 40 / 45 | 38 / 41 | 8 / 10 |

Readings:

- The per-pass cost scales with pixels × samples: 5 ms with 1 sample (3.1 MP) and about 4× with 4
  samples. Text scenes are not the problem they looked like: a status page of 1,823 primitives is
  17-20 ms at 1x.
- The 16-sample branch costs far more than its share of pixels: Spinal Tap at 1x, 1.9 % of pixels
  refine (readback count) and that branch is 34 of its 57 ms (Chrome: 60 of 81 ms). Both branches
  of the shader run on all lanes of a GPU thread, so a few refined pixels make many pixels pay.
  A scene with more than 65,536 rows does not refine at all (`pixelSampleRefineRowLimit`: issue
  https://github.com/danbri/factoidal/issues/1269): the status page and every Retina scene
  above, which is why Retina is not 4× the 1x cost in this table.
- Empty and solid tiles do not matter: skipping empty tiles in the fragment shader, and drawing
  only the non-empty tiles as instanced quads, gave no measurable gain (within 10 %).
- The path winding loop is not the main cost either: removing it changes Spinal Tap from 53 to
  44 ms; what remains is the per-sample walk (storage reads with bounds checks and the branchy
  primitive tests). Shrinking the fragment work needs fewer samples per pixel (per-tile coverage,
  an atlas) or fewer pixels drawn: the second is the partial redraw below.
- The composite pass costs little (a full-screen `textureLoad`; the 13 ms it shows in the bench is
  the completion polling above).
- Pipeline creation is the outlier that is not per frame: 25 to 270 ms in wgpu and 200 to 510 ms
  in Dawn for the scene shader when the module is new: the first frame, and a Metal compile.
  A cold start also pays a 100+ ms `createRenderPipelineAsync`. The earlier Hub figures of 1.3 to
  1.7 s of GPU draw at ratio 2 came from `gpuMs` with `waitForGpu`, which includes the first
  frame's pipeline; not reproduced here: a pass measured the way above is 45 to 65 ms at
  2880 by 2694 (Chrome). The native frames of 128 to 143 ms and the 1,002 ms outliers were not
  reproduced either: in the run below the frame time was the engine's 110 ms, and a window present
  adds the drawable wait (a separate bench of a window was not run).

## 3. Design: partial frames

Two parts, both from one source of truth (the engine knows what changed):

Engine side, `WebPaint.retainedAnswer` and `NativeSVG.compileRetained`: for a band whose answer
is sections with no probes and no inspector tree (every interactive frame), the page layer's
primitives are kept per leaf of the layout's scene: the leaf's address (the object of the kept
layout), and its context (the transforms down to it, the cull box and the clips around it). A
frame compiles again only the leaves whose key differs; the others' records (bytes) are copied.
The tile words are made from the kept compiled primitives. `Scene.artifactWith` stays the
reference; `partial_frame_test.ts` compares the bytes of a retained answer with the plain path
frame by frame.

GPU side: the answer carries `damage: {id,base,rects}`. The rects are tiles (32 pixels)
touched by the old and new boxes of the changed primitives (`Primitive.screenBox`, the
conservative boxes the tile lists use), merged. A host whose layer texture holds answer `base`
draws only those rectangles (`layer_compositor.ts`, `layers.mjs`: `loadOp: "load"`, one
`setScissorRect` and `draw` per rectangle). The scene shader's pixels do not read what was
there, so a rectangle has exactly the pixels of a full draw. An answer that repeats `id` (the
engine's kept band) is not drawn at all. More than half the tiles damaged, a primitive added
or removed, a band change, a probe (`checks`), the inspector or `retained:false` give no rects
and a full draw.

Costs now of a paint-only frame: the walk over the leaves, the key comparisons (no hashing and
no re-flattening of unchanged glyphs), byte concatenation, tile words, the JSON, and the GPU
draw of the damaged tiles only.

Not done, and why: per-tile edge lists or a glyph atlas (the path winding is not the main cost
measured above and these change the coverage model and all pixel hashes); dropping or
reducing the 16-sample refinement (a quality decision on hashes the tests compare).

## 4. Results

See the hand-back of this branch for numbers on the exact tree.
