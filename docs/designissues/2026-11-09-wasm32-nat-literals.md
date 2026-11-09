# Big Nat literals in the Foafnaut Wasm build: a use after free, and the fix

Date: 2026-11-09. Author: bpwasm, a subagent of session depmap-0e.
Records it joins: `2026-11-08-lean-js-engine.md` (section 12, "BubblePopJS does not run in
the Wasm engine yet"), `2026-11-08-page-scripts.md`, and `formal/lean4/Wasm/build-wasm.sh`
(steps 1b and 2, the earlier wasm32 runtime defects).

## 1. Result

BubblePopJS stopped in the Foafnaut Wasm build with "memory access out of bounds" in
`mi_malloc_small`, at stack sizes of 1 MB, 4 MB and 64 MB, so this was not a stack overflow.
An earlier local build at 64 MB had stopped with "remainder by zero". That message was not
reproduced: with today's tree 64 MB gives the same out of bounds, so it is likely, but not
shown, to be this fault too. The cause is a use after free that only a 32-bit target sees.
The sharing that frees a literal twice was found only on BubblePopJS paths (section 2):

- the Lean 4.33 compiler emits a `Nat` literal with no reference counting when it is a
  scalar on the 64-bit machine that compiles it (seen in the emitted C for 4,000,000,000 and
  2^40; that the bound is 2^63 is inferred, not tested);
- on wasm32 a `Nat` of 2^31 or more is a heap object (an mpz), but the emitted C still
  passes one such value to several owners with no `lean_inc`;
- the first owner that is done with it frees it, and the others keep a dangling pointer. The
  frees that follow break the allocator's free lists, so the program fails later, in an
  unrelated allocation.

The fix makes each such literal a persistent object in the C that is compiled for wasm32.
`build-web-render.sh --wasm` refuses to build if one is left. With the fix the Foafnaut Wasm build
runs BubblePopJS: the demo pages, a WPT testharness page, timers and clicks.

## 2. The two cases found

| Where | Literal | Owners in the emitted C |
|---|---|---|
| `JS.callMethod` (`JS/Interp.lean`) | `defaultFuel` = 2^40, emitted as `lean_cstr_to_nat("1099511627776")` | `getV`, then `callV`: both free their fuel argument |
| `WebScripts.startLean` | `Page.Limits.fuel` default 4,000,000,000, as `lean_unsigned_to_nat(4000000000u)` | a closure (`lean_closure_set`) and the `Limits` record (`lean_ctor_set`) |

A third site has the same shape: `JS.runScriptM` passes the fuel to `evalStmts` and `runJobs`.

Only these BubblePopJS paths were found to share a literal. The same 4,000,000,000 default is
built in `Hosts/Page.lean`, `Hosts/PageAot.lean`, `Hosts/PageWasm.lean` and `Hosts/LeanJS.lean`,
and in `WebScripts.loadModule` and `loadAot`, but there the emitted C stores it once, in one
record, so it has one owner and is not freed twice: the QuickJS-NG paths of the Hub do not have
this fault at those sites. The scan that says so counts owner lines in the emitted C of the
engine; it is a text scan, not a proof. The fix covers every site, so that a later change of
the emitted code can not turn a single owner into two.

In all, the C of the Foafnaut Wasm build has 254 literal sites (main of
2026-11-09): 207 in our modules and 47 in 13 of the runtime cache's `Init` and `Std` modules
(for example `Init.Prelude`, `Init.Data.UInt.BasicAux`, `Std.Time`). An `Int` made from such
a literal (`lean_nat_to_int`) has the same flaw above 2^30 - 1, the largest small `Int` on
wasm32; 38 of the 254 sites are such `Int`s.

## 3. How it was found

The work used small Wasm programs (`emcc` on the Lean C of the `LeanJS` import closure, a C
`main`, run in Node), then the engine itself relinked from its objects. No Lean build was
needed:

1. The stack was ruled out. `-sSTACK_OVERFLOW_CHECK=2` builds with 1 MB, 4 MB and 64 MB
   stacks all failed at the same place, and none reported an overflow.
2. Assertions and memory were ruled out. Without `-DNDEBUG`, lean.h's assertions passed. The
   heap was 45 MB at the fault.
3. Other allocators still failed. With mimalloc replaced by dlmalloc the fault became a
   dlmalloc abort, and with emmalloc a 2.2 GB request: heap corruption, not a mimalloc bug.
4. Freed blocks were filled with 0xEF and kept back from reuse. A read of the freed fuel
   number then trapped in `lean_nat_big_sub` called from `callV`, and the emitted
   `callMethod` showed the literal passed to `getV` and `callV`.
5. With the fuel patched, the engine still failed in other places. The runtime's
   `lean_del_core` was rebuilt to report a freed child: the parent was a `Page.Limits`
   record, and its field 0 was the freed mpz 4,000,000,000. The emitted
   `WebScripts.startLean` showed that literal shared with a closure.

## 4. The fix

- `tools/wasm32-nat-literals.py` rewrites each `lean_unsigned_to_nat(N)` and
  `lean_cstr_to_nat("N")` with N of 2^31 or more, and each `lean_nat_to_int` of a literal
  above 2^30 - 1, into `L4_PERSISTENT_LITERAL(...)`. That makes one object per call site
  on first use and marks it persistent (reference count 0), so every increment and
  decrement leaves it alone. This is the representation the compiler already assumes: it
  emits no reference counting for these literals. On a 64-bit target the macro returns
  the scalar unchanged. `--self-test` checks the rewrite, `--count` lists the sites, and
  `--check` fails on any site left.
- `build-web-render.sh --wasm` compiles our modules through the rewrite. It also compiles
  the runtime cache's `Init` and `Std` modules that have sites again, from the cache's own
  C, into `.build/web-render/obj-wasm/core`. The cache itself is left unchanged. The build
  runs `--check` on every file it compiles, so a new literal fails the build.
- `JS.defaultFuel` is now 2^31 - 1, a scalar on wasm32 (theorems `fuel_scalar_on_wasm32`
  and `fuel_covers_steps` in `JS/Tests.lean`). This was not needed for correctness once the
  literal was persistent, but every call and loop iteration subtracts one from the fuel,
  and a big number there allocated each time: the first fib(24) turn in the Foafnaut Wasm build went
  from about 580 ms to 265 ms (Deno, same position in the run).
- Native builds are unchanged.

`Page.Limits.fuel` (4,000,000,000) is still a big number on wasm32. Where WasmVM counts its
instructions against it, each step may do big-number arithmetic in the Foafnaut Wasm build. This
was not measured here. A smaller default, or a `UInt64` count, is a follow-up for the
owners of `Hosts/Page.lean`.

## 5. Limits of this record

- Which literals have two owners: `JS.callMethod`, `JS.runScriptM` and
  `WebScripts.startLean`. That comes from a text scan of the emitted C, not a proof.
- "Remainder by zero" was not reproduced (section 1).
- The call depth in the Foafnaut Wasm build, its stack use (about 55 % of a 984 KB stack) and
  tail calls are in `2026-11-08-lean-js-engine.md`, section 17. Safari's worker stack was not
  measured.
- The Hub's default stays QuickJS-NG until BubblePopJS has been measured there.

## 6. Owner decisions

- This is a defect of the compiler's output for 32-bit targets. Whether to tell anyone
  outside this project is the owner's decision. Nothing has been filed.
