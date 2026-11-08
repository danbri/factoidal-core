#!/usr/bin/env python3
"""Prepare a random sample of Test262 for `lake exe wasmvm-bench test262`
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").

Usage: test262-sample.py [N] [SEED] [WORKDIR]
  N (default 500) tests, chosen with random.Random(SEED) (default 1244) from
  test/built-ins, test/language and test/annexB of Test262 at the commit that
  QuickJS-NG v0.18.0 pins (its test262 submodule). WORKDIR (default ~/working/qjs-wasm)
  gets the Test262 tarball and WORKDIR/test262-sample/NNNN.js. Nothing is written into
  the repository. Test262 is BSD-3-Clause (LICENSE in the tarball).

Each prepared file is one script to evaluate. Its first line says what to expect:
  // expect: pass | negative <ErrorType> | async ; <test path> ; <mode>
Rules, after QuickJS-NG's run-test262.c and test262.conf in "default" mode, with one
difference: a test with no strictness flag runs once, non-strict (the upstream runner
runs it twice, strict and non-strict).
  - harness: assert.js, sta.js, doneprintHandle.js for async tests, then `includes`;
    no harness for `raw` tests; "use strict" first for `onlyStrict` tests.
  - Not prepared (counted as skipped): `module` tests, tests with a feature that
    test262.conf marks `skip`, and tests in its [exclude] section.
"""
import os, random, re, sys, tarfile

COMMIT = "5ef1e5723be95296f36afb0386676fed0205869c"
N = int(sys.argv[1]) if len(sys.argv) > 1 else 500
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1244
WORK = sys.argv[3] if len(sys.argv) > 3 else os.path.expanduser("~/working/qjs-wasm")
CONF = os.path.join(WORK, "src/quickjs-0.18.0/test262.conf")
TAR = os.path.join(WORK, f"test262-{COMMIT[:12]}.tar.gz")
OUT = os.path.join(WORK, "test262-sample")

if not os.path.exists(TAR):
    import urllib.request
    urllib.request.urlretrieve(f"https://codeload.github.com/tc39/test262/tar.gz/{COMMIT}", TAR)

skip_features, excludes, section = set(), [], None
for line in open(CONF):
    line = line.strip()
    if line.startswith("["):
        section = line
    elif section == "[features]" and line.endswith("=skip"):
        skip_features.add(line[:-5])
    elif section == "[exclude]" and line and not line.startswith("#") and not line.startswith("!"):
        excludes.append(line.removeprefix("test262/"))

with tarfile.open(TAR) as t:
    members = {m.name.split("/", 1)[1]: m for m in t.getmembers() if "/" in m.name and m.isfile()}
    harness = {k.removeprefix("harness/"): t.extractfile(m).read().decode() for k, m in members.items()
               if k.startswith("harness/") and k.endswith(".js")}
    population = sorted(k for k in members
                        if re.match(r"test/(built-ins|language|annexB)/", k) and k.endswith(".js")
                        and "_FIXTURE" not in k)
    sample = random.Random(SEED).sample(population, N)
    os.makedirs(OUT, exist_ok=True)
    for f in os.listdir(OUT):
        os.remove(os.path.join(OUT, f))
    counts = {"prepared": 0, "module": 0, "feature": 0, "excluded": 0}
    for i, path in enumerate(sorted(sample)):
        src = t.extractfile(members[path]).read().decode("utf-8")
        meta = re.search(r"/\*---(.*?)---\*/", src, re.S)
        meta = meta.group(1) if meta else ""
        def lst(key):
            m = re.search(rf"^\s*{key}:\s*\[(.*?)\]", meta, re.M | re.S)
            if m:
                return [x.strip() for x in m.group(1).split(",") if x.strip()]
            m = re.search(rf"^\s*{key}:\s*\n((?:\s+-\s*.*\n)+)", meta, re.M)
            return [x.strip()[1:].strip() for x in m.group(1).splitlines()] if m else []
        flags, includes, features = lst("flags"), lst("includes"), lst("features")
        neg = re.search(r"negative:\s*\n\s*phase:\s*(\w+)\s*\n\s*type:\s*(\w+)", meta)
        if any(path.startswith(e) for e in excludes):
            counts["excluded"] += 1; continue
        if "module" in flags:
            counts["module"] += 1; continue
        if any(f in skip_features for f in features):
            counts["feature"] += 1; continue
        if neg:
            expect = f"negative {neg.group(2)}"
        elif "async" in flags:
            expect = "async"
        else:
            expect = "pass"
        if "raw" in flags:
            body, mode = src, "raw"
        else:
            files = ["assert.js", "sta.js"] + (["doneprintHandle.js"] if "async" in flags else []) + includes
            body = "".join(harness[f] + "\n" for f in files) + src
            mode = "strict" if "onlyStrict" in flags else "non-strict"
            if mode == "strict":
                body = '"use strict";\n' + body
        with open(os.path.join(OUT, f"{i:04d}.js"), "w") as o:
            o.write(f"// expect: {expect} ; {path} ; {mode}\n" + body)
        counts["prepared"] += 1
    print(f"Test262 {COMMIT[:12]}: population {len(population)}, sample {N} (seed {SEED}): "
          f"{counts['prepared']} prepared; skipped: {counts['module']} module, "
          f"{counts['feature']} feature marked skip, {counts['excluded']} excluded; in {OUT}")
