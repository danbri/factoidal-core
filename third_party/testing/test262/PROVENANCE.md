# Test262 subset (provenance)

- Source: https://github.com/tc39/test262
- Commit: `5ef1e5723be95296f36afb0386676fed0205869c` (the commit that QuickJS-NG
  v0.18.0 pins; the same commit as the QuickJS-in-WasmVM sample of
  `docs/designissues/2026-11-07-wasmvm-engine.md`).
- Archive: `test262-5ef1e5723be95296f36afb0386676fed0205869c.tar.gz` from
  GitHub's archive of that commit.
- Licence: BSD-3-Clause, Ecma International (`LICENSE`, copied unmodified).
- Files are copied unmodified.

## What is here

Only the files that `lake exe leanjs test262` runs for the Lean JavaScript engine
(`formal/lean4/L4Factoidal/JS/`, record
`docs/designissues/2026-11-08-lean-js-engine.md`):

- `harness/`: `assert.js`, `sta.js`, `propertyHelper.js`, `compareArray.js`, `doneprintHandle.js`, `asyncHelpers.js`,
  `tcoHelper.js` (the includes that the tests below name, except
  `resizableArrayBufferUtils.js`, which one test names; that test is skipped).
- `test/language/`: 6,301 files in 70 directories of `expressions/` and
  `statements/`, chosen as the directories of the language features the engine
  implements first. The list of directories is in `DIRECTORIES`.

The whole suite at this commit has about 48,600 test files under `test/built-ins`,
`test/language` and `test/annexB`; it is not vendored.

## Run

    cd formal/lean4
    lake exe leanjs test262 ../../third_party/testing/test262 $(cat ../../third_party/testing/test262/DIRECTORIES)
