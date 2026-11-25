# Typed word maps from Lean source to a WGSL dispatch

19 November 2026. Paralliverse can lower a typed map of `UInt32` addition or multiplication to a fixed WGSL shader, or lower two such maps to sequential passes. Lean checked that the two parsed affine shaders return the same words as the fused CPU task interpreter for every factor, offset and worker count. The shader is selected from the original syntax. Fusing the affine tree first creates a scalar composition that this selector refuses. [Word-map target](../formal/lean4/L4Factoidal/Paralliverse/WordMapGPU.lean) · [Work item 646](https://github.com/danbri/factoidal-core/issues/646)

For example, multiplying `[0xffffffff, 3, 3]` by two then adding one yields `[0xffffffff, 7, 7]`. The multiplication writes its output payload to an intermediate buffer whose header already names the addition operand. The addition reads that same returned buffer, including its spare tail. The formal run exposes both individual dispatches, their complete output frames and their chronological lane traces. [Two-pass proof and CPU correspondence](../formal/lean4/L4Factoidal/Paralliverse/WordMapGPUChain.lean)

## Buffers and launch

The immutable source at group 0, binding 0 starts with the payload length and coefficient, followed by up to 1,024 logical words and any spare tail. The distinct writable destination is at group 0, binding 2 and has room for its two-word header plus the payload. The coefficient comes from the source buffer. The parser checks the entire UTF-8 source of each exported shader. At invocation `i < length`, the shader reads source word `2+i` and stores the modular result at destination word `2+i`. Padded invocations record zero stores. [Exact byte and single-invocation proofs](../formal/lean4/L4Factoidal/Paralliverse/WordMapGPUSurface.lean)

The workgroup size is 64. The bounded dispatcher receives the actual rounded lane count as fuel, including zero for empty input. Each pass admits every permutation of its own physical grid. The complete destination is its original first two words, followed by the original program’s result and then its original words beyond the payload. The second pass receives the first pass’s entire returned array without reconstruction. The existing packing pipeline and the new word-map target share the same dispatch declarations. [Grid semantics](../formal/lean4/L4Factoidal/Paralliverse/WordMapGPUGrid.lean) · [Shared dispatcher](../formal/lean4/L4Factoidal/Paralliverse/WGSL/Dispatch.lean)

## Checked evidence

All five GPU jobs compiled fresh source at `d499e3be2f158278adc544dc1089cebc8443c5be`. Every module in each dependency closure exited zero. New proof leaves and the guard harness used warnings as errors, a 2 GiB Lean limit, a 4 GiB process address-space limit and 180 seconds per module. Each job passed its proof-hygiene audit. The 15 public names below are in `L4Factoidal.Paralliverse.WordMapGPU`. Their axiom reports contain only subsets of `propext`, `Classical.choice` and `Quot.sound`. [Exact source](https://github.com/danbri/factoidal-core/commit/d499e3be2f158278adc544dc1089cebc8443c5be)

| CI job | Compiled modules | Public theorems |
| --- | ---: | --- |
| [Selection](https://github.com/danbri/factoidal-core/actions/runs/44603117138/job/135839543441) | 9 | `selectUnary?_eq_some_iff`, `select?_eq_some_iff`, `select_affine`, `select_fused_affine` |
| [Shader bytes and lane](https://github.com/danbri/factoidal-core/actions/runs/44603117138/job/135839543222) | 11 | `parse_shader`, `packet_layout`, `eval_pass`, `run_module_lane` |
| [Finite-buffer frame](https://github.com/danbri/factoidal-core/actions/runs/44603117138/job/135839543531) | 12 | `lane_size`, `foldLanes_frame` |
| [Physical grid model](https://github.com/danbri/factoidal-core/actions/runs/44603117138/job/135839543300) | 17 | `word_grid_bounds`, `word_canonical_valid`, `selected_grid` |
| [Direct two-pass chain](https://github.com/danbri/factoidal-core/actions/runs/44603117138/job/135839542782) | 19 | `selected_two_grid`, `affine_grid_eq_cpu` |

The chain job also evaluated 11 executable checks. They exercise empty and full inputs, 64, 65 and 129 words, repeated values, wraparound, independently ordered passes, short buffers, coefficient reads and fused-source refusal. The oracle uses ordinary word arithmetic and compares the entire intermediate and final buffers. [Model fixtures](../formal/lean4/Harness/ParalliverseWordMapGPUModel.lean)

The theorem covers the restricted Lean WGSL parser, its finite storage model and the existing CPU interpreter. Shader compilation by a driver, host uploads, distinct physical bindings, inter-pass visibility and device readback require their own observed execution evidence. [Device acceptance criteria](https://github.com/danbri/factoidal-core/issues/646)

