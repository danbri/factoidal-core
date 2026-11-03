# Layout recursion audit, 2026-11-03

The full Lean CI recursion gate reported `Rendering.Layout.block` and
`Rendering.Layout.inlineItems` as unreviewed length-proportional cycles. The
cycles are real retained C calls, but their depth is the explicit nesting
fuel. Sibling width does not accumulate those calls. The production renderer
starts with fuel 64, and every descent shares and decreases that budget.
No layout algorithm, fixture, error result or limit was changed by this audit.

## Generated C evidence

The inspected file is
`formal/lean4/.lake/build/ir/L4Factoidal/Rendering/Layout.c`, SHA-256
`e410b98c3eec60d53e69d2fc797aa48002bf079f7d462dbfd699cc547f642e2d`.
The symbol prefix is `lp_l4factoidal_`; the helper suffix below is the emitted
`Array_forIn_x27Unsafe_loop___at___00…_spec__0` specialization.

| Edge or loop | Generated C evidence |
| --- | --- |
| `Layout.render` → `Layout.block` | Lines 11257–11262 construct `lean_unsigned_to_nat(64u)` and pass it as the fuel argument. |
| `Layout.inlineItems` → its Array helper | Line 4279 computes `v_n_1328_ = lean_nat_sub(v_x_1297_,1)` after the zero-fuel return; line 4306 passes that predecessor into the helper. |
| Inline helper → `Layout.inlineItems` | Line 4876 passes the helper's predecessor argument `v_n_1427_` to the child call. Lines 4889–4895 increment the sibling index and execute `goto _start;`. |
| `Layout.block` → its Array helper | Line 9049 computes `v_n_3015_ = lean_nat_sub(v_x_2889_,1)` after the zero-fuel return; line 9105 passes that predecessor into the helper. |
| Block helper → `Layout.block` or `Layout.inlineItems` | Lines 10118 and 9940 pass the same predecessor `v_n_3161_`; lines 10200–10205 increment the sibling index and execute `goto _start;`. |

`scan_c_file` from the unchanged recursion audit tool finds exactly two SCCs
for these declarations: each layout function plus its specialized Array
helper. Each helper has one tail jump, no real self-call and no recursive
closure. Each layout entry has no direct self-call; its retained helper call
is the other edge in its SCC. The block helper can enter `inlineItems`, but
there is no edge back to `block` from the inline SCC. That transition also
uses the predecessor fuel. Boxed wrappers do not introduce another cycle.

Thus a complete reentrant SCC traversal lowers the fuel once. It does not
lower it on both C edges separately: the entry passes its predecessor to the
loop, and the loop passes that predecessor unchanged to the child. Sibling
iterations reuse the loop's current frame after the child has returned.
The audit tool's textual class is `length` because the signatures contain
Array/String-bearing arguments and results; that ranking is not a proved
input-length stack bound, as the tool's own documentation states.

## Entry points and proof boundary

The production call in `Rendering.Layout.render` is
`block dom styles font embedding 64 …`. The only nonrecursive production
call to `inlineItems` outside Layout is `Rendering.FontRequests.forDOM`:
inside its `node.type == .text` branch it calls `inlineItems … 1 id`. The
text case returns before child traversal. Repository call-site search found
no other production use of either lower-level API. Lab HTML, RDF and supplied
font producers call `Layout.render`, so all use the fixed rendering budget.

Within Layout, `block` calls both child traversals with the predecessor of
its own fuel, and `inlineItems` does the same. It never resets the budget when
switching formatting context. Inference from these source and C edges gives
at most 64 positive-fuel layout activations plus the zero-fuel refusal. With
one retained Array helper per positive activation, a conservative bound on
these SCC frames is 129. Other helper/library/embedding frames are outside
that count; this is not a formal theorem about C compiler stack allocation.

The public lower-level functions still accept arbitrary Nat fuel. Their
general stack bound is O(fuel), and callers that supply an unbounded fuel
do not receive this production guarantee. Their doc comments now state that
fact. Arbitrary caller-supplied font/embedding callbacks are likewise outside
the audited entry-point claim.

`Rendering/LayoutStackAudit.lean` proves the exact zero-fuel refusal for all
DOMs, style arrays, font/embedding values, node IDs and coordinates. These
equations use only `propext`, `Classical.choice` and `Quot.sound` inherited
through the definitions. Six executable guards accept nested block/inline
documents at 60 explicit elements, reject 61 with the unchanged depth error,
and accept 1,000 block/inline siblings. The document/html/body wrappers and
terminal text consume the rest of the fixed 64 budget. This test module is
separate from the production implementation.

## Actual native and WASM checks

`tests/stack/rendering_layout.mjs` passed 17 controls through the real compiled
Lean ABI in both runtimes. It compared the complete parsed artifacts, including
every layout box and glyph run. Every native process ran with
`LEAN_STACK_SIZE_KB=512` and `LEAN_MAIN_USE_THREAD` unset, requesting a 512 KiB
stack for Lean's separately created main thread. The existing WASM build uses
its unchanged 4 MiB stack.

- 1, 1,000, 10,000 and 50,000 empty block siblings, followed by painted text.
- The same widths with inline span siblings.
- 60 nested block elements accepted; 61 and 10,000 refused with the exact
  existing depth error. The same three controls for inline spans.
- Mixed block/inline nesting accepted at total depth 60 and refused at 61.
- 2,000 block siblings followed by an admitted 60-deep block subtree.

The largest inputs are 550,001 bytes (blocks) and 650,001 bytes (spans), inside
the existing 1 MiB input limit. Native and WASM passed all controls without
a stack overflow. These controls measure the unchanged production path;
they do not establish arbitrary-fuel stack safety or all-platform behavior.

Report: `/private/tmp/factoidal-layout-stack-runtime-verified.json`. Before
the 17 controls, the test verifies the existing deliberately non-tail
`tests/stack/StackControl.lean` binary: 100 elements succeed with the same
environment, 204,800 elements report stack overflow, and 204,800 succeed with
the default runtime environment. This confirms that the runtime reads the
budget on this host. The native launcher also uses `ulimit -s 512 && exec …`,
but RLIMIT_STACK alone does not constrain Lean's separate main thread.

Correction to the earlier audit report: its shell-only RLIMIT reduction did
not establish the claimed Lean-thread budget. Generated `WebRenderCLI.c`
calls `lean_run_main`, so the earlier claim needed the runtime variable and
a negative control. The new mandatory control and complete 17-case rerun
replace that claim. All cases pass with the verified environment.
Native SHA-256:
`82053979c7960447ff10318f4ca32e280dcf7d80a96941489b11d63698001b40`.
WASM SHA-256:
`ce2f61b2ba4fe11f7ba86075025bb5d9630e039b836327f8e65f5e6499a4104a`.

Reproduce from the repository root:

```sh
/opt/homebrew/opt/node@22/bin/node tests/stack/rendering_layout.mjs \
  labs/demos/foafnaut/.build/web-render/engines/web-render.mjs \
  labs/demos/foafnaut/.build/web-render/web-render-native \
  /private/tmp/NEW-layout-stack-report.json \
  /private/tmp/factoidal-rendering-scene-canary/stack-control
```

Build and calibrate that control, without the full fixture suite, with
`bash tests/stack/run.sh --route native --canary 512 --control-only --fixtures
/private/tmp/factoidal-rendering-scene-canary`.

Run the proof/guard check with `formal/lean4/` as the explicit working
directory: `lake env lean L4Factoidal/Rendering/LayoutStackAudit.lean`.
It passed. A targeted `lake build L4Factoidal.Rendering.Layout
L4Factoidal.Rendering.LayoutStackAudit` also passed, including six guards and
both universal equations. The regenerated Layout C has the exact SHA above;
the comment-only Layout edit made no generated-code change.

After the separate Path and Scene repairs, `python3
tools/lean-tail-recursion-audit.py --gate --top 1` returned exit 0. Both the
recursion and mandatory csimp-reach gates passed over the current 43 compiled
C files. This is the local compiled closure, not a fresh build of the full
Lean corpus. Log: `/private/tmp/factoidal-layout-reviewed-tail-final.log`.
The two precise `(c)` recursion allow entries link to this audit; the gate's
detection, classification and other entries are unchanged.
