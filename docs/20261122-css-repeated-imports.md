# Repeated CSS imports

Each import occurrence now enters the cascade at its source position and under its own conditions. Cycle detection follows the active import chain. Fetch requests use the first occurrence of each URL. A shared occurrence budget and the existing depth bound limit traversal.

The standalone module compiles in Lean 4.33.1 with warnings treated as errors. The import traversal retains its no-import and zero-fuel equations and its public result bounds. Its guards cover ordering, repeated URLs with distinct wrappers, missing resources, cycles, depth and breadth. Native rendering was dispatched separately.

[CSS Cascade Level 5 §6.1](https://www.w3.org/TR/css-cascade-5/#at-import)
