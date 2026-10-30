# Compact snapshot base64 codecs

The WebDAV executable gate still fails on large reads:
https://github.com/danbri/factoidal/issues/1202 (49 MB memory panic and encoded names).
This is a bounded repair on
https://github.com/danbri/factoidal-core/pull/265 (executable gate), based on
`323a739998c48acac664179f07196d1cb3e8ae92`.
It does not establish that the complete large-read failure is fixed.

## Change and semantics

`LWS/Snapshot.lean` keeps the original `encode`, `decode?`, `encGo`, `decGo`
and all existing theorem statements. Two whole-function equalities,
`encode_eq_fast` and `decode_eq_fast`, register compiler substitutions.

The encoder indexes the compact input ByteArray with a tail loop, keeps at
most two pending bytes and pushes symbols directly into a String. The decoder
uses String.foldl's UTF-8 traversal, keeps at most three alphabet values and
pushes decoded bytes directly into a ByteArray. Neither replacement builds an
input-sized linked list or generic output array. The emitted C calls the fast
encoder from entryJson and the fast decoder from the snapshot body reader.
The reference functions remain available for proofs and differential tests.

Exact equality preserves refusal of whitespace, non-ASCII, URL-safe alphabet,
short groups, interior padding, extra padding and characters after a padded
group. Nonzero unused padding bits remain accepted, including `Zh==`, `Zm9=`,
`/x==` and `//9=`. This change does not tighten or broaden decoder admission.

The new tests spell out the original bodies independently, so compiler
substitution cannot reduce their comparisons to fast-versus-fast. There are
38 guards, including RFC 4648 vectors, arbitrary binary bytes, all one-byte
values, patterned lengths 0 through 512, malformed strings and unused bits.
Two kernel proof examples instantiate the whole-function equalities.

Both equality proofs depend only on `propext`, `Classical.choice` and
`Quot.sound`, as reported by `#print axioms`. There are no new assumptions,
proof holes, recursion limits or audit allowlist entries.

## Local validation and measurements

Named Snapshot compilation (olean and C) and Base64FastTests pass, using a
private output overlay under `/private/tmp/factoidal-base64-fast`. Dependencies
are read-only cached qt4 oleans; Store and Binding sources were compared and
are identical. No cache was initialized in this checkout. A minimal Lean
setup specifies the normal `l4factoidal` package prefix for compiled auditing.

The following single-run ladder uses `lean --run`, not a native executable
or WASM. Codec time excludes input creation; peak RSS includes the Lean runner,
imports, typechecking and guards. The shared startup cost dominates these
small probes. These measurements do not establish native/WASM throughput.

| Input bytes | Reference codec ms | Compact codec ms | Reference RSS bytes | Compact RSS bytes |
| ---: | ---: | ---: | ---: | ---: |
| 65536 | 90.64 | 132.09 | 501350400 | 494338048 |
| 131072 | 182.69 | 262.10 | 506658816 | 495435776 |
| 262144 | 378.14 | 517.70 | 519766016 | 495353856 |

Every probe checked the full decoded bytes against the original input.
The compact implementation was slower in this VM probe while peak RSS stayed
approximately flat at this scale. Native measurements follow below; WASM timing and memory remain to be
measured. The Darwin sysctl-based `/usr/bin/time -l` could not report RSS in
this sandbox; the table uses child getrusage instead.

## Compiled native codec probe

A standalone Darwin arm64 probe links the exact emitted Snapshot C using the
installed Lean 4.33.1 `leanc -O2`, existing runtime libraries and dead stripping.
It does not build Lake dependencies. The C harness initializes Init and the
exact padding constant from Snapshot's initializer; unused Store/Binding code
is stripped. This isolates the codecs rather than exercising full Snapshot or
WebDAV startup. The initial reference probe omitted that constant and crashed;
the corrected probe initializes it before either implementation is measured.
No generated codec body was changed.

The probe constructs bytes by `byte[i] = (73*i+19) mod 256`, retains the original
input, encodes, decodes, checks length and every byte with memcmp, and compares
OpenSSL SHA-256 of input and output. SHA-256 and comparisons are outside codec
timers. Peak RSS covers the whole native process, including input, encoded and
decoded buffers. Each row is a fresh process; these are single measurements,
not a statistical throughput benchmark. MB below means decimal bytes.

| Input bytes | Implementation | Encode ms | Decode ms | Peak RSS bytes |
| ---: | --- | ---: | ---: | ---: |
| 65536 | compact | 1.718 | 2.815 | 6455296 |
| 65536 | reference | 4.259 | 2.654 | 13484032 |
| 1048576 | compact | 27.298 | 43.312 | 12140544 |
| 1048576 | reference | 72.897 | 43.002 | 107102208 |
| 8388608 | compact | 209.418 | 353.995 | 59834368 |
| 49000000 | compact | 1278.221 | 2049.199 | 275251200 |
| 51000000 | compact | 1288.206 | 2156.972 | 282165248 |

All seven rows passed exact byte equality and equal SHA-256 hashes. The
49,000,000-byte hash was
`fb4dac6dde3e66b9840504abd5624be6be426968335e162d07100cbb5f48f7e3`;
the 51,000,000-byte hash was
`ab2d36562a011c551ea2468bc9b275c7f93632d91a5c765fba6a9449e5a5cab0`.
The compact total was faster at both small comparison sizes; the VM timing
regression did not carry over to this native probe. Reference probes were
limited to 1 MiB. No large reference allocation was attempted. Every compact
row stayed below the probe supervisor's 512 MiB continuation threshold.

Probe source, binary and JSONL evidence are under
`/private/tmp/factoidal-base64-fast/{native_probe.c,native_probe,native-measurements.jsonl}`.
Total private outputs are approximately 9.1 MB, below the 50 MB budget. The
build uses existing OpenSSL headers and the toolchain's existing crypto
library; it adds no dependency. Native codec success does not establish WASM
memory use or complete WebDAV response/snapshot allocation behavior.

The probe source is retained at [tests/lws/base64-native-probe.c](../tests/lws/base64-native-probe.c)
and the seven measured rows at [docs/benchmarks/20261030-webdav-base64-native.jsonl](benchmarks/20261030-webdav-base64-native.jsonl).
The retained harness uses an include search path for the unchanged generated
`Snapshot.c`, refuses reference runs above 1 MiB, and explicitly compares both
hash strings in addition to `memcmp`. It is a Darwin/Lean 4.33.1 diagnostic,
not a new production dependency or a full WebDAV test.

To reproduce with already-built Lean dependencies, run from `formal/lean4/`:

```sh
CODEC_OUT=$(mktemp -d)
printf '%s\n' '{"plugins":[],"package":"l4factoidal","options":{},"name":"L4Factoidal.LWS.Snapshot","isModule":false,"importArts":{},"dynlibs":[]}' > "$CODEC_OUT/Snapshot.setup.json"
lake env lean --setup "$CODEC_OUT/Snapshot.setup.json" -c "$CODEC_OUT/Snapshot.c" L4Factoidal/LWS/Snapshot.lean
CODEC_SDK=$(xcrun --show-sdk-path)
leanc -O2 -mmacosx-version-min=14.0 -isystem "$CODEC_SDK/usr/include" \
  -I/opt/homebrew/opt/openssl@3/include -I"$CODEC_OUT" -Wl,-dead_strip \
  -o "$CODEC_OUT/probe" ../../tests/lws/base64-native-probe.c
"$CODEC_OUT/probe" fast 51000000
```

Module-scoped compiled tail-recursion and csimp reach gates both pass. The
reach scan finds real calls of both replacements and no surviving reference
callers; this is not a full-library compiled audit.

The actual 49 MB and 51 MB WebDAV/WASM tests, byte equality, and a following
request on the same handle remain mandatory. The independent colon-name
routing failure remains open. No fixtures, harness checks, memory limits or
URI routing changed. Snapshot JSON serialization and other response copies
can still contribute to allocation pressure.
