# Presenter JSON boundary

The `presenterStep` operation reads a caller-owned `State` and one `Input`, calls
`L4Factoidal.Presenter.step`, and returns the next state and ordered outputs.
`placement` reports the offset, whether it is exact, and whether the shown band keeps
the current scroll. These decisions remain in Lean.

The ordinary document operation is available for serial callers and parity tests.
The independent C entry `web_presenter_step_call` uses the same compiled function
without reading or writing the document engine's C `engine` variable. The main
thread must initialise this entry before it starts the worker. The existing
document ABI remains restricted to one engine thread. No non-blocking FFI or new
Lean escape hatch is used.

The pure text entry refuses requests above 4096 bytes before parsing. All numeric
fields must be natural integers at most 2147483647. Invalid input returns an
error. The host does not clamp invalid input or substitute its own arithmetic.

`Wire.exact_offset` states that an exact placement selects the requested top row.
It does not establish the CPU/GPU pixel equality or the host's thread behaviour.
The library build passed in cloud run 44144679468 on 4c6cd118e, including this
module, after repairing the state constructor syntax. Local Lean still cannot run:
the required lock exits 3 because this context cannot inspect the process table.
The exact-offset theorem now also has a `#print axioms` command for the next build;
that additional diagnostic has not yet run.

Checks completed for this section:

- `deno test --no-config --no-lock -A labs/demos/foafnaut/host_contract_source_test.ts`:
  3 passed, 0 failed.
- `deno check --no-config --no-lock --unstable-ffi` on `native_html_engine.ts` and
  `presenter_step_test.ts`: passed.
- `bash -n labs/demos/foafnaut/build-web-render.sh`: passed.
- `clang -fsyntax-only` with the pinned Lean include directory on
  `web_render_shim.c`: passed.

`presenter_step_test.ts` compares the serial document operation with the pure
entry on the same trace, checks coalescing, kept scrolls, offsets and malformed
numbers. Execution requires a new engine build and has not yet been done.
