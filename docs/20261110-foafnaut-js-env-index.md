---
title: "Indexed JavaScript lookup agrees with the scan"
date: 2026-11-10
draft: false
tags: [foafnaut, javascript, theorems]
---

`Env.slotN_eq_scan_of_indexOf` proves that an environment whose index is
`FunInfo.indexOf e.names` returns exactly the reference scan's slot for every
name. `Env.get?_with_indexOf` lifts this to equality of the complete optional
binding, including the value, initialization and mutability flags. Duplicate
names select the first slot; absent names stay absent. No uniqueness premise
or minimum layout size is needed.

This checks an existing optimization: `Resolve.rFun` builds `FunInfo.index`
from its layout, and the plain-parameter path of `callClosure` installs both
in the environment. Large function activations share that hash index instead
of scanning names. The proof uses the actual builder, scan and lookup. The
producer connection above is a source inspection; the proof does not establish
that every environment producer or later mutation preserves index consistency.
No runtime code changes or speed gains are claimed here.

Checks: targeted proof build; four boundary/duplicate/absence/binding guards;
91 JavaScript regression guards and the importer typechecked with shared cached
dependencies whose sources match; hygiene and import gates; standard axioms
only. A mutation that overwrites duplicate slots makes the builder theorem
fail; restoring the implementation passes. The shared-cache check is not a
fresh build of the whole JavaScript engine.

Files: `JS/IndexTheorems.lean`, `JS/EnvIndexTheorems.lean` under
`formal/lean4/L4Factoidal/`. Tracking:
https://github.com/danbri/factoidal-core/issues/388 (theorem contributions).
