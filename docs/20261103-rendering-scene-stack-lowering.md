# Scene lowering with an explicit stack, 3 November 2026

`Rendering.Scene.Node.lowerTR` called itself from a child `foldl`. The compiled
call graph retained a cycle through that fold. An accumulator for siblings did
not remove stack growth with group depth.

The replacement uses one direct-tail `lowerLoop` over pending sibling frames.
Each frame contains the current transform and reversed group/clip contexts.
Entering a group composes its transform with the current parent in the same
order as the specification. Entering a clipped node also records its clip in
the independent parent frame. Paint items restore forward context order and
enter a reverse output accumulator. Reversed contexts share their tails;
pending ancestor frames do not retain separately copied context prefixes.

The existing `Node.lower` and `Node.lowerList` definitions remain the reference
specifications. `lowerLoop_eq` proves the accumulator invariant against the
pending reference paint lists. `Node.lowerListTR_eq` and `Node.lowerTR_eq`
establish exact list equality for every input and inherited frame. The two
existing `@[csimp]` theorems select the new implementation. The proof preserves
source IDs, painter order, group paths, clip order and exact Float composition
nesting. It does not reassociate Float arithmetic or prove rasterized pixels.
No new axiom, `sorry`, unchecked implementation attribute or allow-list entry
was added for scene lowering. Weight and pending-reference functions are
noncomputable proof-only definitions; the executable loop does not calculate
subtree sizes or invoke reference recursion.

Validation on macOS ARM64 with Lean 4.33.1:

- `lake build L4Factoidal.Rendering.Scene L4Factoidal.Rendering.Tests` passes,
  including the existing independent content/clip frame and source-ID guards.
- The emitted C loop has one `_start:` label, four `goto _start;` transitions
  and no recursive self-call. The previous scene C fails the unchanged audit
  on `Node.lowerTR`; the replacement removes that executable cycle.
- The unchanged recursion gate and its chained `csimp` reach gate pass over
  the current 44-file compiled tree, exit 0. The reach check finds 73 calls of
  registered replacements. This is the targeted compiled closure present
  locally, not a claim that every repository module was rebuilt.
- A native executable from `tests/stack/RenderingScene.lean` links the new scene
  C with existing native dependency objects. With `LEAN_STACK_SIZE_KB=512` and
  `LEAN_MAIN_USE_THREAD` unset it checks 100,000 sibling
  source IDs in order, 30,000 nested group transforms and group paths, and
  30,000 nested clip widths/frames including a primitive's own clip. It passes
  under that budget. The existing independent stack control passes: 100 elements
  run, 204,800 elements overflow with that budget, and 204,800 run with the
  default budget. A process stack limit alone does not constrain Lean's separate
  main thread and is not used as evidence of this budget. This establishes the
  tested native cases; a new WASM build
  and browser check remain part of the coordinated renderer rebuild.

Local evidence: `/private/tmp/factoidal-scene-before-fullgate.log`,
`/private/tmp/factoidal-scene-after-fullgate.log`,
the permanent `tests/stack/RenderingScene.lean`, and
`/private/tmp/factoidal-scene-stack-stress.json`.

## Reproduce the native canary

From the repository root, validate the runtime stack knob first:

```sh
bash tests/stack/run.sh --route native --canary 512 --control-only \
  --fixtures /private/tmp/factoidal-rendering-scene-canary
```

The following small build reuses existing compatible native lab dependency
objects. Run it from `formal/lean4/`, after the targeted Scene module and native
lab objects have been built. It replaces the lab's cached Scene object with a
fresh one and does not rebuild the whole renderer or modify the cached objects.

```sh
python3 - <<'PY'
from pathlib import Path
import os, subprocess, tempfile

project = Path.cwd()
task_dir = Path(tempfile.mkdtemp(prefix='factoidal-scene-stack-'))
lab = project / '../../labs/demos/foafnaut'
objects = [str(path.resolve())
           for path in (lab / '.build/web-render/obj-native').glob('*.o')
           if path.name not in {'Core_L4Factoidal_Rendering_Scene.o', 'WebRenderCLI.o'}]
assert objects, 'Build the native lab dependency objects first'

def run(args):
    subprocess.run(['lake', 'env', *args], cwd=project, check=True)

run(['lean', '-j1', '-R', '../..', '-c', str(task_dir / 'fixture.c'),
     '../../tests/stack/RenderingScene.lean'])
run(['leanc', '-O2', '-c', '.lake/build/ir/L4Factoidal/Rendering/Scene.c',
     '-o', str(task_dir / 'Scene.o')])
run(['leanc', '-O2', '-o', str(task_dir / 'scene-stack'),
     str(task_dir / 'fixture.c'), str(task_dir / 'Scene.o'), *objects])
env = dict(os.environ, LEAN_STACK_SIZE_KB='512')
env.pop('LEAN_MAIN_USE_THREAD', None)
subprocess.run([str(task_dir / 'scene-stack')], env=env, check=True, timeout=30)
print('Native canary artifacts:', task_dir)
PY
```
