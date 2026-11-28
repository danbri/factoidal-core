# Foafnaut page-script engine reporting, 28 November 2026

The 0.38.0 and 0.38.1 macOS releases select BubblePopJS with a fresh setting. Both allow QuickJS-NG by explicit selection. The native executable's help in those releases still described QuickJS-NG as the page-script engine. A status explanation then described the older switch in terms that made it sound recent.

## Timeline

- 8 November at 22:30 UTC. The native host's default changed to BubblePopJS. QuickJS-NG remained available in Settings. The Hub initially kept its previous default. [Native default commit](https://github.com/danbri/factoidal-core/commit/98cc094f7)
- 9 November at 18:51 UTC. The Hub and Foafnaut Wasm host changed their defaults to BubblePopJS in source. The QuickJS guest became lazy. [Wasm host default commit](https://github.com/danbri/factoidal-core/commit/226c14a0a)
- 14 November. The shared policy was aligned across the host names. [Shared default commit](https://github.com/danbri/factoidal-core/commit/ff96d6a96)
- 28 November. The bundled native engine was queried in both published Mac packages. For `scriptPlan` with one script and an empty setting, both returned `engine: bubblepop` and `run: true`. Explicit QuickJS selected `engine: quickjs`. The 0.38.1 engine's `scriptChoices` rendered BubblePopJS checked and labelled it the default. Its native `--help` still described QuickJS-NG as the page-script engine. The npm launcher's `--dev-help` gave the current default. [0.38.0 bundle](https://github.com/danbri/factoidal-builds/releases/tag/build-2d9fb5f097b3-foafnaut-darwin-arm64) · [0.38.1 bundle](https://github.com/danbri/factoidal-builds/releases/tag/build-bd0d78dd12ff-foafnaut-darwin-arm64)

## Cause and correction

QuickJS-NG originally ran page scripts as a Wasm guest in WasmVM. BubblePopJS replaced that execution path as the default. Deno continued to run the desktop host. A separate help string in the native executable retained the pre-switch text after the policy and Settings changed. The status explanation also omitted the transition dates and failed to distinguish the host from the page engine.

Update the native help to name the default and describe the explicit QuickJS choice. When reporting release defaults, use the bundled engine's `scriptPlan` and `scriptChoices`. Saved settings and explicit flags can select a different engine.
