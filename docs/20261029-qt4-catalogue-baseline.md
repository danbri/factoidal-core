# QT4 catalogue inventory and XQuery measurement

Date: 2026-10-29. Tracking:
https://github.com/danbri/factoidal/issues/1101.

Measured source: `425317127cba1f7a60eb04881a9d9bece4789ba9`, the initial
head of https://github.com/danbri/factoidal-core/pull/268. This is a baseline
for subsequent changes, not a claim that every selectable configuration runs.

The default XQuery command covers ten families. The catalogue also contains
`xs`, `ser`, `bin` and `file`, so a second disjoint run covers those four.
The binary was frozen with an APFS clone before further builds. Its SHA-256:
`cbce4b4c9ef20be1886ad1e9322fe030d1dc2f4155a3362bc20d1acda0ab7dca`.

Independent XML inventory finds **742 test sets and 49,159 test cases**.
Both runs together account for every set and case exactly by inventory totals:
**47,457 pass, 591 fail, 1,076 unsupported (49,124 scored), plus 35 existing
defective-data exclusions**. Unsupported configurations and exclusions are not
passes. Existing exclusions retain their issue references in the harness.

| Family | Pass | Fail | Unsupported | Scored |
| --- | ---: | ---: | ---: | ---: |
| prod | 14113 | 401 | 434 | 14948 |
| op | 4672 | 20 | 97 | 4789 |
| fn | 17408 | 120 | 334 | 17862 |
| map | 358 | 0 | 3 | 361 |
| array | 533 | 1 | 3 | 537 |
| math | 181 | 0 | 0 | 181 |
| app | 3019 | 16 | 21 | 3056 |
| misc | 4128 | 15 | 89 | 4232 |
| ft | 675 | 0 | 0 | 675 |
| upd | 798 | 0 | 27 | 825 |
| xs | 219 | 1 | 12 | 232 |
| ser | 434 | 17 | 56 | 507 |
| bin | 649 | 0 | 0 | 649 |
| file | 270 | 0 | 0 | 270 |

Two sets timed out with a 60-second isolation limit: `op-same-key`, at
`same-key-023`, leaves six tests unfinished; `app-Demos`, at `itunes`, leaves
eleven unfinished. All seventeen count as failures, not skips. Other failures
include named schema types, labeled record semantics and schema-based
element-to-map conversion. These need implementation work; this measurement
does not reclassify them as inapplicable.

Commands ran from `formal/lean4` on macOS ARM64 with `ulimit -s 65520`:

```sh
.lake/build/bin/l4qt4 --lang xquery --list-fails --isolate 60
/private/tmp/l4qt4-42531712 --lang xquery --family xs --family ser --family bin --family file --list-fails --isolate 60
```

Raw logs are `/private/tmp/qt4-combined-final-xquery.log` and
`/private/tmp/qt4-42531712-extra-families.log` in the measuring workspace.
The local JSON cache `depmap/cache/qt4/20261029-42531712-xquery.json` holds
per-set counts, reported failure/unsupported details, catalogue inventory,
commands and log hashes. These are native-run measurements; full source CI
and the exact-head package gate remain separate merge requirements.
