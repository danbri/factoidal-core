# Commits of 49dd1eaab..41a1aaeab (169) that are in neither file, and why

Method for the npm entry: the import closure of `formal/lean4/Wasm/Dispatch.lean`, `Wasm/Exports.lean` and `Wasm/Main.lean` on `origin/main` (891 modules, computed from the `import` lines) was compared with the 74 Lean files that changed under `formal/lean4`. Two changed files are in the closure: `L4Factoidal/LWS/Client/Machine.lean` and `L4Factoidal/Net/ProxyProtocol.lean`. The closure has no module of `L4Factoidal/JS`, `WasmVM`, `Rendering`, `PageCanvas` or `FrameCost`. Under `npm/` only `npm/factoidal/bin/foafnaut.mjs` changed. `formal/lean4/Wasm/` did not change.

## Reachable from the npm package, but with no change a user can observe

- `0fee0a14f` `ProxyProtocol.groups16` is a loop. Same result; the input is at most 16 bytes, so stack use does not change in a way a user can see. It closes one line of the tail-recursion allow list (https://github.com/danbri/factoidal/issues/1291, tail-recursion gate).

## In the browser notes as a group, not as their own bullet

Every browser, engine, font, Hub and tool commit is named in `evidence.tsv` with the bullet that covers it.

## Left out of both files

- Merge commits and pull request merges with no content of their own: `a987008d6`, `94906aebc`, and the merge lines of `41a1aaeab` (#387), `9b18837a4` (#384), `a6f655490` (#382), `55dd7a66c` (#370; one status line of the canvas chart demo).
- Records and docs only: `5d0fe6c5f`, `e23a5a312`, `ed49cc141`, `97eda5b3b`, `43d4d85c6`, `bac4001d6`, `342a6d55d`, `3245341dc`, `0ca9153cf`, `d9efaa6c4`, `32adf8477`, `e1328353f`, `a384e0f4d` (theorems as contributions; https://github.com/danbri/factoidal-core/issues/388, theorem tasks), `a6b41fdce`, `9d2613de1` (used only for the last known limit).
- Skills: `9ecf33ae9`, `4a1c56b32`, `dc863db7c`, `7cb8cceb6`, `c1ddc1dd9`, `1c86bffc6`.
- Tests and fixtures only, with no behaviour change of their own: `386f8fb43`, `4fb2b87e1`, `dcbaacef0`, `ffefdacef`, `7d76c4ad1`, `7b0001720`, `730684b2a`, `c6e74a618`, `eba872bd9`.
- Gate lists only: `8a9f9bd70` (tail recursion allow list).
- Demo page content: `c74e1184b` (Spinal Tap page text and zoom stage).
- Source hygiene with the same behaviour: `f094a4a62` (`FormSubmission.decodeChars` is specification only).

## Not in the range

- The daily WPT job is in `danbri/factoidal-builds` (commits `5011198`, `32d004f`), not in `factoidal-core`. It is in the browser notes because the task names it.
