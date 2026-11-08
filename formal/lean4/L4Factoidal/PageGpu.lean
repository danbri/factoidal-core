/-
L4Factoidal.PageGpu: the GPU API of page scripts, validated by Lean
(record: docs/designissues/2026-11-08-page-gpu.md).

- `PageGpu.Wgsl`: the WGSL subset (tokens, AST, parser, validator, index hardening, printer).
- `PageGpu.Model`: page commands, host commands, the page's object table, quotas, `step`.
- `PageGpu.Wire`: the bytes of the `gpu_command` import and the JSON of host commands.
- `PageGpu.Theorems`: subset, bounds, zero initialisation, usage, ownership, quotas.
- `PageGpu.Tests`: `#guard` cases and the `#print axioms` audit.
-/
import L4Factoidal.PageGpu.Wgsl
import L4Factoidal.PageGpu.Model
import L4Factoidal.PageGpu.Theorems
import L4Factoidal.PageGpu.Wire
import L4Factoidal.PageGpu.Tests
