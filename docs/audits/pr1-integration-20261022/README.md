# PR1 reconciliation evidence, 2026-10-22

Finite local evidence for source commits `aeb5c4494`, `884647492` and
`f90efa6f5`, reconciled onto `87af61c`. The original PR1 was `ed19f090`.
See the [worknote](../../20261022-pr1-main-reconciliation.md) for behavior,
normative references and remaining limits. These files are an immutable
capture: retain original names and add a later capture for future runs.

| Pinned XSD stage | Pass | Fail | Excluded | Pattern exclusions |
| --- | ---: | ---: | ---: | ---: |
| Independent main+PR2+PR3 baseline | 18,955 | 0 | 7,402 | 105 |
| Initial integrated 1.0-profile routing | 15,880 | 0 | 10,477 | 3,180 |
| Corrected 1.1 name profile | 16,135 | 0 | 10,222 | 2,925 |

All 26,357 instance tests remain accounted for; all 93 sets were read.
The corrected profile recovers 255 scored cases. The remaining 2,820 fewer
scored cases match NIST instance groups using `\d`; the legacy parser
uses ASCII digits, while XSD specifies a Unicode category. These are
excluded, not passes. The metadata scan is a structural cross-check, not
a semantic oracle. Its raw examples and the old/new admission probe are
preserved. No new Unicode-category implementation is claimed.

Final RIF: **42 pass, 1 fail, 3 unknown, 0 unread**, exit **1**. The original
native binary exited zero with exactly the same output. Three durable exit
controls were red against that binary; the fixed runner and final parser
revision pass those controls plus the existing seven-case import control
(four selected unittest methods). Original suite inputs remain unchanged.

The `xsd11-complement-red` log records a real failed U+00B7 complement guard.
The corrected range normalization and 16 new guards pass in the 21-job
targeted build. Final native build passes 160 jobs. Earlier build attempts
include real compile failures, not current passes. The frozen PR1-only full
build was intentionally interrupted at 856/969 for the parent's combined
build: exit 143 is neither a pass nor a proof rejection. The tail-audit log
records an IR-file race during an active build, not a passing tail gate.
Historical aggregate controls contain 27/29 at that stage; the later shared
comparator corrected the two red cases. Both the original mutation
classifier and its reviewed correction are preserved. The reuse inventory
was captured before the new Xsd11 module and is not a final-tree count.

Runners are native Lean executables. Exact commands, source revisions,
fixture pin, timings and binary SHA256 values are in adjacent JSON files.
The XSD pin is `7bc3365c652a322f3d762021b3879eb92dae7e30`; RIF uses the
unmodified W3C Core_v1.22 Approved suite. Fixtures, their original licenses,
external dependencies, binaries, caches and suite trees are not included.
This capture does not claim complete standards conformance, a passing RIF
suite, a final combined build, or all findings repaired. The parent owns
the final combined build, Wasm, CI and full hygiene gates.

To verify every captured byte from the repository root:

```sh
python3 - <<'PYVERIFY'
from pathlib import Path, PurePosixPath
import hashlib, json
r = Path('docs/audits/pr1-integration-20261022')
assert not any(p.is_symlink() for p in r.rglob('*'))
m = json.loads((r / 'manifest.json').read_text())
expected = set()
for f in m['files']:
    rel = PurePosixPath(f['path'])
    assert not rel.is_absolute() and '..' not in rel.parts
    p = r / rel
    assert not any(q.is_symlink() for q in [p, *p.parents])
    b = p.read_bytes()
    assert len(b) == f['size'] and hashlib.sha256(b).hexdigest() == f['sha256']
    expected.add(f['path'])
actual = {p.relative_to(r).as_posix() for p in r.rglob('*') if p.is_file()}
assert actual == expected | {'manifest.json'}
print(f'verified {len(expected)} files')
PYVERIFY
```
