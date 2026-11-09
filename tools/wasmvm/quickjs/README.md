# QuickJS-NG in the Lean WasmVM engine

On the Hub, page scripts run in QuickJS-NG, compiled to WebAssembly and run by the Lean
WasmVM engine (`formal/lean4/L4Factoidal/WasmVM/`). In the desktop app the default engine is
BubblePopJS (`formal/lean4/L4Factoidal/JS/`), and QuickJS-NG in WasmVM is an option in
settings; `WebRenderScript.defaultEngine` decides. No host JavaScript engine runs a page
script. DOM effects go through typed host imports that Lean serves on its DOM arena.
Issue: https://github.com/danbri/factoidal/issues/1244 (WasmVM engine). Record:
`docs/designissues/2026-11-07-wasmvm-engine.md`, section "QuickJS in WasmVM".

## Files

- `qjs_wasmvm_entry.c`: the entry point. It has the exports `qjs_new`, `qjs_eval`,
  `qjs_call`, `qjs_release`, `qjs_alloc`, `qjs_free` and `qjs_test262`, and the
  `foafnaut_dom` imports. The comment at the top gives the ABI.
- `prelude.js`: the JavaScript prelude that makes `document`, elements, `console`, timers
  and `queueMicrotask` from those imports. BubblePopJS uses it too.
  `prelude_bytecode.c` compiles it to QuickJS bytecode for the guest at build time.
- `webassembly.js`: the WebAssembly JavaScript API for page scripts.
- `../build-quickjs.sh`: the build (pinned version, SHA-256 of the tarball, flags).
- `host-reference.mjs`: runs the same scripts with today's host-run QuickJS path
  (`labs/demos/foafnaut/web-render/script-engine/`), for comparison.
- `test262-sample.py`: prepares a random sample of Test262.
- Lean side: `WasmVM/Hosts/Dom.lean` (the host), `WasmVM/Bench/QuickJS.lean` and
  `WasmVM/Bench/Test262.lean` (the runs).

## Run

From the repository root:

    tools/wasmvm/build-quickjs.sh                  # ~/working/qjs-wasm/qjs-wasmvm.wasm
    curl -sSfLo ~/working/qjs-wasm/qjs-wasi-reactor.wasm \
      https://github.com/quickjs-ng/quickjs/releases/download/v0.18.0/qjs-wasi-reactor.wasm
    python3 tools/wasmvm/quickjs/test262-sample.py 500 1244
    cd formal/lean4
    lake exe wasmvm-bench qjs ~/working/qjs-wasm/qjs-wasmvm.wasm ~/working/qjs-wasm/qjs-wasi-reactor.wasm
    lake exe wasmvm-bench test262 ~/working/qjs-wasm/qjs-wasmvm.wasm ~/working/qjs-wasm/test262-sample ~/working/qjs-wasm/qjs-native

The native comparison runner (`qjs-native`) is the same entry point built with the
host C compiler and `-DQJS_NATIVE` (DOM imports answer "denied"):

    S=~/working/qjs-wasm/src/quickjs-0.18.0
    cc -O2 -D_GNU_SOURCE -funsigned-char -DQJS_NATIVE -w -I$S tools/wasmvm/quickjs/qjs_wasmvm_entry.c \
      $S/quickjs.c $S/libregexp.c $S/libunicode.c $S/dtoa.c -lm -o ~/working/qjs-wasm/qjs-native

The binaries are not committed.

## Licences

- QuickJS-NG v0.18.0 (https://github.com/quickjs-ng/quickjs): MIT. Copyright (c)
  2017-2026 Fabrice Bellard, 2017-2024 Charlie Gordon, 2023-2026 Ben Noordhuis,
  2023-2026 Saúl Ibarra Corretgé (LICENSE in the tarball). A distributed build must
  carry that notice.
- Test262 (https://github.com/tc39/test262), used only as test input and not committed:
  BSD-3-Clause.
- `qjs_wasmvm_entry.c` is this repository's own code.
