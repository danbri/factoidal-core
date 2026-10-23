# Final native tail-refinement replay, 2026-10-22

Source `37746b673` combines the existing XSD repair with the reviewed tail
refinement `84cb4ddc7`. The parent integrated that refinement as `4bc80d56d`.
Six changed source files match the reviewed refinement byte for byte; all
four XSD repair files remain identical to `f90efa6f5`. The allowlist-only
cherry-pick conflict retained the actual new classifications and omitted
unchanged context for newer-main modules absent from this checkout.

`LEAN_NUM_THREADS=2 lake build l4rif l4xsd-datatypes`, from
`formal/lean4`, passed 160 jobs. Both native runners were replayed on the
same unmodified fixtures; full output is byte-identical to the pre-tail run.

| Native check | Result | Exit |
| --- | --- | ---: |
| W3C RIF Core_v1.22 Approved | 42 pass, 1 fail, 3 unknown, 0 unread | 1 |
| XSD pin 7bc3365c652a322f3d762021b3879eb92dae7e30 | 16,135 pass, 0 fail, 10,222 excluded | 0 |
| Selected CLI controls | 4 methods pass | 0 |

XSD pattern exclusions remain 2,925. Unknown/excluded results are not
passes; the RIF suite remains red. The CLI controls exercise decided
failure, empty inventory, stale override and the existing seven-case import
control. No extra suite was expanded. Commands, actual source hashes,
timings and new binary SHA256 values are in the JSON reports.

The initial root-directory invocation failed before compilation because
there was no Lake configuration there; its exact setup error is retained.
The successful build used the explicit Lean project directory. This is
finite native evidence, not a performance benchmark or a standards-adequacy
proof. The parent owns final combined library, Wasm, CI and hygiene gates.
The earlier [73-file capture](../pr1-integration-20261022/README.md) is
unchanged. No binaries, suite trees, caches or external dependencies are
copied. Preserve captured bytes and make a later snapshot for future runs.

Verify from the repository root:

```sh
python3 - <<'PYVERIFY'
from pathlib import Path, PurePosixPath
import hashlib, json
r = Path('docs/audits/pr1-tail-final-20261022')
assert not any(p.is_symlink() for p in r.rglob('*'))
m = json.loads((r / 'manifest.json').read_text())
for f in m['files']:
    rel = PurePosixPath(f['path'])
    assert not rel.is_absolute() and '..' not in rel.parts
    b = (r / rel).read_bytes()
    assert len(b) == f['size'] and hashlib.sha256(b).hexdigest() == f['sha256']
assert {p.relative_to(r).as_posix() for p in r.rglob('*') if p.is_file()} == {f['path'] for f in m['files']} | {'manifest.json'}
print(f"verified {len(m['files'])} files")
PYVERIFY
```
