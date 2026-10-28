# EXPath Binary 4.0 and EXPath File 4.0 in Lean

Date: 2026-10-28. Tracking: https://github.com/danbri/factoidal/issues/1101
(QT4, EXPath stage). Open items: https://github.com/danbri/factoidal/issues/1142.
Defective test data: https://github.com/danbri/factoidal/issues/1141.

Specifications: EXPath Binary Module 4.0 and EXPath File Module 4.0, qtspecs
commit b4723ff52fd9d4fabf2b4cd33bd44f21939c512c
(`specifications/expath-binary`, `specifications/expath-file`). Tests: qt4tests
commit b39c4bc027a56c82407f479709bc59e2122be5fc, `bin/` and `file/` (vendored in
`third_party/testing/qt4tests`).

## Scores

Command (from `formal/lean4/`, `ulimit -s 65520`): `lake build l4qt4`, then
`.lake/build/bin/l4qt4 --family bin --family file --isolate 60`.

- `bin`: 647 pass, 0 fail, 2 unsupported (out of 649); 23 excluded (defective
  test data, https://github.com/danbri/factoidal/issues/1141).
- `file`: 265 pass, 2 fail, 3 unsupported (out of 270). The same with
  `--file-host io`.
- The existing families (prod, op, fn, map, array, math) gave the same numbers
  per test set before and after the change: 24152 pass, 4327 fail, 10180
  unsupported (out of 38659).

Unsupported: 2 `bin` cases have a `limits big_integer` dependency, which the
runner does not read; 3 `file` cases are XQuery only.

## Where the code is

`formal/lean4/L4Factoidal/EXPath/` (not imported by the library root
`L4Factoidal.lean`, so the wasm and the npm package do not change):

| File | Content |
|---|---|
| `Catalog.lean` | the `bin:` and `file:` signatures, generated from the two `function-catalog.xml` files |
| `Hook.lean` | `expathLookup`: the one entry point that `XPath4.Ext.libLookupAll` asks |
| `Binary/Octets.lean` | octet operations on `List Nat`: pack, unpack, part, find, bit operations, `bin:hex`/`bin:bin`/`bin:octal` |
| `Binary/Text.lean` | encodings (UTF-8, UTF-16, UTF-16BE/LE, ISO-8859-1, US-ASCII); decoders are those of `XML.Encoding` |
| `Binary/Lib.lean` | the 33 `bin:` functions with the error codes |
| `Binary/Theorems.lean` | 22 theorems |
| `File/FS.lean` | the in-memory file system, path strings |
| `File/Host.lean` | the host interface `Host m` and the in-memory instance `memHost` |
| `File/Ops.lean` | the 41 `file:` functions, written once over `Host m` |
| `File/Exec.lean` | the evaluator that orders writing calls |
| `File/IOHost.lean` | the real file system under one sandbox directory; the qt4tests `sandpit` loader |
| `File/Theorems.lean` | 13 theorems |

Shared files changed (each change is marked "EXPath hook"):
`XPath4/Catalog.lean` (`catalogExt`), `XPath4/Core.lean` (prefixes `bin` and
`file`, the signature table, the field `Env.fileSys`), `XPath4/Ext.lean` (the
lookup), `Harness/Qt4Run.lean` (features `binary` and `expath-file`, the
`sandpit` environment, `--file-host`, `Q{...}` error codes, the defective-data
list).

## How a `file:` call is evaluated

The XPath 4.0 evaluator `XPath4.eval` is a pure function of the dynamic context
(`Env`). It can read a file system but cannot change one. File 4.0 § Function
Execution says the writing functions are nondeterministic, must be evaluated
fully and in order, and that users must keep their calls "statically explicit"
and in contexts "where the order of execution is predictable". The
implementation follows that text:

1. **The host interface.** `Host m` is a structure of operations in a monad
   `m`: `stat`, `read`, `write`, `mkdir`, `remove`, `list`, `fresh`, and the
   paths `cwd` and `tmp`. Every `file:` function (`Ops.fileTable`) is written
   once against it: the parent checks, the recursion of copy, move and delete,
   and the error codes.
2. **Two hosts.** `memHost` is the pure in-memory file system `FS` in the monad
   `StateT FS M`. `ioHost` is the real file system in `ExceptT Err IO`: a path
   is a list of segments with no `..` (resolution removes it), mapped below the
   sandbox directory, and symbolic links are not followed, so no operation
   reaches a file outside the sandbox. Only the qt4tests runner uses `ioHost`
   (`--file-host io`); the library evaluator does no I/O.
3. **Reading.** In the pure evaluator a `file:` function runs on
   `Env.fileSys` (a snapshot of the file system). A function that only computes
   with path strings (`file:name`, `file:resolve-path`, ...) also runs with no
   file system. A writing function is refused there (`file:io-error`).
4. **Writing.** `File.exec` evaluates the expression in the host monad. A
   subexpression with no static call of a writing function goes to
   `XPath4.eval`, with the current file system in `Env.fileSys`. The forms whose
   order XPath fixes are evaluated by `exec` itself, in order: the comma
   operator, `let`, `for`, `if`, `and`, `or`, `!`, a static function call
   (arguments left to right), and the operand of the unary, cast, instance-of,
   treat, filter, lookup and arrow forms (bound to a variable, then the form is
   evaluated by `XPath4.eval`). A writing call in any other place gives
   `FOER0000` (https://github.com/danbri/factoidal/issues/1142, item 3).

The runner copies the test set's `sandpit` directory into an `FS` at
`/work/sandpit` (the current directory; `/tmp` is the temporary directory)
for each test case, so every write stays in memory. With `--file-host io` it
writes that `FS` to a new temporary directory, runs `exec` with `ioHost`, uses
the real clock and the real modification times, and removes the directory.

## Decisions

- **Error codes for a wrong `$order` and an octet outside 0..255** are
  `XPTY0004`, as the 4.0 text says. 23 `bin` tests expect the 1.0 codes; they
  are excluded as defective test data
  (https://github.com/danbri/factoidal/issues/1141).
- **`file:write-binary` with two arguments replaces the file.** The catalog
  gives `$offset` the default `0`, but the rules distinguish "if $offset is
  specified" (overwrite from it) from the plain form, and test
  `EXPath-file-writeBinary2-002` expects the replacement. `EXPath/Catalog.lean`
  gives `$offset` the default `()` and says why.
- **`UTF-16` text** is written most significant byte first after a byte order
  mark (implementation-defined; § file:write-text). `bin:encode-string` writes
  no byte order mark, as its rules say.
- **`file:copy` and `file:move`** create the missing parent directories of a
  new target (test `EXPath-file-copy-006`).
- **Static base URI** of a `sandpit` test with none in its environment:
  `file:///work/test-set.xml` (the test set file, in the directory whose
  `sandpit` is `/work/sandpit`), so `file:base-dir()` is `/work/`.
- **Implementation-defined values**: directory separator `/`, line separator
  `&#10;`, path separator `:`, one root `/`, temporary names
  `<prefix>tmp<n><suffix>`, case-sensitive glob matching, the largest unpacked
  integer is 2^20 octets.

## Theorems

`Binary/Theorems.lean`: pack and unpack are inverse (`beValue_packBE`,
`packBE_beValue`, `unpack_pack_unsigned`, `signedOf_twosComplement` for the
signed range); the loop `packBEAcc` is `packBE` (`@[csimp]`); octet order is an
involution; `bin:hex` reads `XSD.hexOfBytes` back (`ofHex_hexOfBytes`);
`bin:from-base64url` inverts `bin:to-base64url` through the proved codec
`JOSE.Base64Url.decode_encode` (`fromBase64url_toBase64url`); bit `not` and
`xor` laws.

`File/Theorems.lean`: `FS.put` and `FS.erase` change one path and no other
(`get_put_self`, `get_put_other`, `get_erase_self`, `get_erase_other`); write
then read on `memHost` (`memHost_write_read`); the `file:` write path stores
the octets, appends to the old ones, and reads back what it wrote
(`writeOrAppend_write`, `writeOrAppend_append`, `write_then_read`); a write
under a missing directory fails with `file:no-dir` (`writeOrAppend_noDir`).

All 35 depend only on `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms`). Theorems still to prove are listed in
https://github.com/danbri/factoidal/issues/1142, item 6.
