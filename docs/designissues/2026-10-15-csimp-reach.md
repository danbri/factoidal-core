# A `@[csimp]` replacement must reach its callers

Tracking: https://github.com/danbri/factoidal/issues/871. Found while repairing
https://github.com/danbri/factoidal/issues/867 (record: `skills/lean4-proof-patterns`,
section 9d). Tool: `tools/lean-csimp-reach.py`; self-test:
`tools/test_lean_csimp_reach.py`; allow list: `tools/lean-csimp-reach-allow.txt`;
known-bad fixture: `formal/lean4/L4Factoidal/CsimpReachFixture.lean`.

## Result

- `lake build` and the tail-recursion audit cannot tell whether a `@[csimp]`
  replacement reaches the functions that call the replaced one. The new tool reads the
  emitted C and says which functions still call the left side of each theorem.
- On the tree at e98ec076 (160 `@[csimp]` theorems, 159 left sides) the first run gave
  55 findings. Six of them, in three places, were defects of the kind the issue describes;
  they are repaired (section 6). Of the 49 others, 24 were read and listed with a reason in
  `tools/lean-csimp-reach-allow.txt`, and 25 are held by a specification that no live code
  reaches (section 6). Reading one of the 24 showed a seventh defect: the specification
  `XML.parseChildren` has a compiled caller that no theorem covered. It is repaired, and its
  line left the allow list (section 6, item 3).
- Final state of this landing: 163 theorems, 162 left sides, 56 findings: 0 new, 28 on the
  allow list (23 and the 5 of the fixture), 28 held by a specification that no live code
  reaches.
- No finding in the tree is of the instance-inlining kind that started the issue. That
  kind is shown only by the fixture. The tool cannot see a path that copies the body of
  the left side into the caller (section 4).

## 1. What Lean does

`Lean/Compiler/CSimpAttr.lean` (Lean 4.33.1). A `@[csimp]` theorem must state `@f = @g`
with `f` and `g` constants and the same universe parameters. The environment keeps a map
from `f` to the entry; a second theorem for the same `f` replaces the first.

`Lean/Compiler/LCNF/ToLCNF.lean` lines 547, 685 and 818 call `CSimp.replaceConstant` on the
head constant of each application, while it converts the kernel value of the declaration
that is being compiled. So the replacement happens in the value of a declaration
compiled after the theorem. A later pass that inlines the stored body of another
declaration brings in a body that was converted earlier, and does not replace again.

## 2. Paths that keep a call of `f`

| path | reason code | example in this tree |
|---|---|---|
| the caller is declared above the theorem in the same module | `before-theorem` | `RDF.Term.joinKeyLoop` (calls `Term.joinKey` on a leaf, on purpose) |
| the caller's module does not import the theorem's module | `not-imported` | `Qlvr.Side.sortChunk` (repaired); `Storage.DeltaLogBytes.sameChecked` |
| the caller is in the `mutual` block of `f` | `before-theorem` | `XML.parseChildren` calls `parseElement` |
| a specification with two entries: the theorem covers one, compiled code calls the other | none (the other has no theorem) | `XML.parseChildren` called by `Syntax.RdfXml.parseChildrenFold` (repaired) |
| `f` is a `where` helper of its only caller | `before-theorem` | `JSONLD.matchingSubjects` (repaired) |
| an inlined instance, `@[inline]` or specialised definition compiled before the theorem | `after-theorem` | the fixture only |
| the instance is a static closure over `f` (a constant, not a call) | `before-theorem` | the fixture only |
| the compiler copied the body of `f` into the caller | not visible | none known |

The `where`-helper path was not on the list before this work. A helper is part of the
declaration of its caller, so no theorem can stand between them. The theorem for
`matchingSubjects.matchingSubjectsGo` (issue 746) therefore never reached its caller, and
the tail-recursion audit still counted the helper as `replaced`.

## 3. The tool

Source: the header of `tools/lean-csimp-reach.py` (method, five steps, exclusion rules
with reasons, exit codes, limits). In short:

1. Read every `@[csimp]` theorem from the Lean source (derived from the tree on every run;
   an empty list is exit 2). Map `f` and `g` to C symbols with Lean's own name mangling
   (`Lean/Compiler/NameMangling.lean`). A name counts only if its symbol is defined in the
   emitted C, so a mangling error shows as an unresolved theorem.
2. Read the emitted C (`formal/lean4/.lake/build/ir`). A reference to `f` is its symbol, or its
   `___boxed`, `___redArg` or `___redArg___boxed` form, in a function body or in a
   file-scope static closure; a specialised copy of `f` is a reference by the function it
   was made for.
3. Name the declaration that holds each reference (the owner). Exclude `f` itself and its
   helpers. Exclude an owner that is itself a replaced specification that no live code
   reaches. Every other owner is a finding.
4. Say why from the import graph and the line of the owner (reason codes above).
5. `--gate`: exit 1 for a finding that is not on the allow list, a theorem that cannot be
   resolved, or an allow line without a reason. Exit 2 when there is nothing to check or
   the scan sees no use of any replacement (the positive control: 556 uses on this tree).

Run it from the repository root after a full `lake build` (it takes about 7 s):
`python3 tools/lean-csimp-reach.py --gate`. A finding that is right to leave goes on the
allow list with its reason (`leaf`, `bound`, `twin`, `guard`, `spec`, `dead arm`,
`fixture`). A finding to repair is repaired as section 6 shows.

## 4. Method and what the tool cannot see

- It sees a path that keeps a CALL of `f`. If the compiler inlined the BODY of a small or
  `@[inline]` `f` into a caller, there is no symbol to find and the tool reports nothing.
- It reads the C of the last build. A module that is not built gives an unresolved theorem
  (the gate fails). The `verify-lean4` workflow of this repository builds only the
  `L4Factoidal` library, so it does not build `Harness.CryptoProbe`, which holds one
  theorem; the check belongs after a full `lake build`.
- It finds references by symbol. A function reached only through `lean_apply` of a closure
  built in another module is seen where the closure is built.
- It reads `formal/lean4` only. A repair by an instance of higher priority
  (`instHashableTermLoop`) is not a `@[csimp]` theorem and is not audited.
- It lists the callers of the left sides of theorems. A specification that compiled code calls and
  that has no theorem of its own is not listed (`XML.parseChildren` until 2026-10-15); it shows
  only as the OWNER of a finding.
- It does not measure speed.

## 5. Checks of the tool, with their results

Each check below was run on the tree of this landing.

- **Completeness of the theorem list.** `--cross-check` imports every built module into Lean and
  reads `Lean.Compiler.CSimp.ext`: 163 theorems of this package in Lean's table, 163 in the
  source scan, none on one side only. 99 modules that define the root-level `main` cannot be imported together; none of them holds a
  theorem (the source scan found none; a theorem in them that a macro generates would not be
  seen).
- **Scan of the C.** Two criteria for a function header (the tool's definition pattern, and
  "column 0, ends in `){`") give the same count in each of 966 files (81,701). Every
  occurrence of a wanted symbol outside a prototype or a header is inside a function body
  (1,063) or in a static closure (6); none is anywhere else.
- **Mutation.** 17 deliberate breaks of the tool (no static closures, no own-family rule, no
  boxed or reduced-arity forms, a single `_` in the mangling, no disambiguation, no
  specialised copies, no liveness, allowed findings that make a specification live, no
  positive control, no private names, a fixed reason, no required reason, the attribute
  command ignored, comments not blanked, stale C kept) each fail at least one synthetic case
  of the self-test.
- **Self-test.** `python3 tools/test_lean_csimp_reach.py`: 27 synthetic cases (the mangling
  rules against symbols the compiler emitted, the owner of a function, every exclusion rule,
  exit codes, reasons, the source reader) and 6 cases on the real build (the fixture, the
  repairs, the guard lines, the cross-check, the gate).
- **Fixture.** `CsimpReachFixture.lean` holds a specification `weightSpec`, its loop twin and
  a proved theorem, then five callers: `callDirect` (after the theorem; the C calls
  `weightFast`), and `callBefore`, `callViaInstance`, `callViaInline`, the instance and the
  `@[inline]` definition (the C calls `weightSpec`). It is a known-bad example kept on
  purpose. The four `#guard` lines emit no function.

## 6. Findings on the tree and what was done

First run on e98ec076 plus the fixture, with an empty allow list: 60 findings, 42 not
suppressed (a finding is suppressed when its holder is a specification that live code does
not reach). Without the five of the fixture: 55 findings, 37 not suppressed. After the
repairs, with an empty allow list: 56 findings (the fixture's five included), 35 not
suppressed. The allow list below makes 7 more findings suppressed: the code that reached
their specification is on the list, so the specification is no longer live. Final: 56
findings, 28 allowed (23 and the fixture's 5), 28 suppressed, 0 new.

Repaired (items 1 and 2: six findings in three files; item 3: a defect found by reading one finding):

1. **`JSONLD.matchingSubjects`** (`L4Factoidal/JSONLD/Frame.lean`). The twin of the `where` helper
   `matchingSubjectsGo` (`matchingSubjectsGoTR`, issue 746) had no caller: the only caller is
   `matchingSubjects`, compiled before the theorem. The helper takes one native frame for each
   matching subject (the emitted C has one non-tail self-call; the twin has none and three
   `goto _start`). Repair: `matchingSubjectsFast` and `@[csimp] matchingSubjects_eq_fast`
   after the existing theorem; the caller `frameRec` is compiled after it. Test: the W3C
   json-ld-framing suite before and after, 91 pass, 0 fail, 1 local-override, 0 unsupported
   (out of 92) both times, and the 92 outputs byte-identical (`L4_JSONLD_DUMP`). The effect
   on a large input is not measurable end to end: a frame of 10,000 subjects aborts under
   `LEAN_STACK_SIZE_KB=512` in the expansion (`expandFieldsList`, `expandGraphItems`; issue
   https://github.com/danbri/factoidal/issues/753), before and after.
2. **`Qlvr.Side`** (`sortChunk`, `sideLookupM`, `testLookup`) and **`Harness/Qlvr`**
   (`SideIdx.lookup`, `runSideIndex`) called `cmpBytes` without importing
   `Qlvr.CmpBytesFast`, the module of its twin (issue 804). Repair: the import, with a comment, in
   both modules. The C now calls `cmpBytesFast`. Test: `lake build` (the guards of `Side.lean`);
   the 21 QLever oracle queries of `tests/qlvr/queries.sh` with the `l4qlvr` built before and after:
   21 pass, 0 fail, 0 refused (out of 21), the same 21 result lines; `tests/sbm11/run.sh`:
   2,823 pass, 0 fail, 30 expected-fail (out of 2,853) (it runs `Sbm11PermCheck`, which imports
   `Side`). The speed change is not measured.

3. **`XML.parseChildren`** (`L4Factoidal/XML/Parser.lean`; the caller is in `Syntax/RdfXml.lean`).
   Found by reading a finding; the tool did not report the defect itself. The finding "`parseElement`
   is called by `parseChildren`" is in the `mutual` block that no theorem reaches, and the allow list
   of the tail-recursion audit said that `parseChildren` is a specification with one compiled caller,
   `parseElement`. `parseChildrenFold` in `Syntax/RdfXml.lean` is a second compiled caller. It reads the
   replacement text of a markup entity that is referenced directly from the content of `rdf:RDF` with
   `parseChildren`, which calls itself for each nested markup entity: one native frame for each level.
   The theorem `parseElement_eq_parseElementW` (issue 755) reaches the document element only, and the
   case `xml-markup-chain` puts its reference inside a node element, so no case reached this call.
   Measured before the repair (`l4wasm-cli call parseToDatasetJson`, native, `LEAN_STACK_SIZE_KB=512`,
   a chain of markup entities under `rdf:RDF`, one triple for each level): 3,000 levels ran; 6,000,
   10,000, 15,000, 20,000 and 30,000 overflowed. The same chain inside a node element ran at 30,000.
   Repair: `parseChildrenFromStart` (the worklist with an empty worklist) and
   `@[csimp] parseChildren_eq_parseChildrenFromStart`, proved from `parseChildrenW_eq` and
   `resumeC_nil`; the emitted C of `parseChildrenFold` calls `parseChildrenFromStart` now. Test: the
   case `xml-markup-chain-top` of `tests/stack/run.sh` and `wasm_case.mjs` (10,000 levels; the answer
   must count 10,000 triples). After the repair, native, 512 KB: 10,000 levels run (2.4 s) and 30,000
   levels run (43 s), with the same output as the default stack. At the default stack the outputs are
   byte-identical to those of the build before: 10,000 levels took 3.3 s before and 2.4 s after,
   30,000 levels 59.8 s before and 50.1 s after. Suites before and after, with identical result lines:
   RDF 1.1 1,041 pass, 0 fail (out of 1,041); RDF 1.2 1,358 pass, 0 fail (out of 1,358); XML 1.0
   conformance 1,861 pass, 0 fail (out of 1,861 in profile); RDF/XML probe 132, 41 and 132 pass, 0
   failures. The line for `parseChildren` left both allow lists, and the self-test asserts that
   `parseChildrenFold` calls the replacement.

   After item 3 the other claims of this kind were checked against the emitted C (method: for each
   declaration, the functions of the C that name it, outside its own family, followed to the end of
   the call chain). The 7 rows marked `(s)` in `tools/lean-tail-recursion-allow.txt` name the callers
   that the C shows. The owners of the `guard`, `spec` and `dead arm` lines of this tool's allow list
   have no compiled caller other than other guard helpers, test definitions (`Tests.chain2`,
   `Tests.sat`) and `labelsLoop` for `labelStepSem` (the dead arm).

The wasm build (`formal/lean4/Wasm/build-wasm.sh`, step 6) compiles the C of every library module
except `Harness_*`, `Wasm_Main` and `Wasm_Cli`, and the linker drops the code that the entry modules
do not reach. `JSONLD/Frame.lean`, `Qlvr/Side.lean` and `XML/Parser.lean` (changed) and
`CsimpReachFixture.lean` (new) are in the compile set. `JSONLD/Frame.lean`, `Qlvr/Side.lean` and the
fixture are not in the import closure of `Wasm.Exports` or `Wasm.CoreExports`, so the linker drops
their code. `XML/Parser.lean` IS in the closure of both: the wasm modules change when they are rebuilt
(item 3 changes the code of `parseChildrenFold`). They are not rebuilt by this landing, so the `wasm`
and `wcanary` rows of `tests/stack/run.sh` are NOT SCORED here, and the row `xml-markup-chain-top` is
not measured in the wasm routes. `Harness/Qlvr.lean` is not compiled for wasm. The message of the
commit `e2ca67a0` says "No module of the wasm build changes"; that is wrong for the compile set and
for item 3.

Gates on the merged tree (`b6ec77b9`, which merges `accac951` of issue 870 into this work): `lake build`
1726 jobs, exit 0; `tools/lean-tail-recursion-audit.py --gate`, `tools/lean-unbuilt-modules.py --gate`
(795 modules, 0 not reached) and `tools/lean-csimp-reach.py --gate --cross-check`, exit 0; self-test 33
pass, 0 fail, 0 not run (out of 33); mutation test 17 killed (out of 17); `tests/sbm11/run.sh` 2,823 pass,
0 fail, 30 expected-fail (out of 2,853); `tests/stack/run.sh --canary` 101 pass, 2 fail (out of 103), where
the 2 failures are the wasm rows, NOT SCORED because this checkout has no wasm module; the RDF 1.1, RDF 1.2,
XML 1.0 conformance and RDF/XML probe result lines equal those of the build before item 3.

Left, 23 allow lines plus 5 for the fixture, by reason (the file has each line's module and caller):

| reason | lines | meaning |
|---|---|---|
| `leaf` | 5 | the loop calls the specification for an input where the specification does not recurse (RDF 1.2 triple terms: `joinKeyLoop`, `readObject12Down`, `toNTriplesClose`, `readTtObjectLoop`, `readTripleTermDown`) |
| `bound` | 3 | the branch is for a size no array reaches: 2^64 characters (`expandEntityLoop`, `entityWsLoop`) or `USize.size` bytes (`cmpBytesFast`) |
| `twin` | 2 | the twin handles the shapes it improves and calls the specification for the others (`freshTopFast`, `finishSelectRowsPrefix`) |
| `dead arm` | 1 | `labelStepSem`: the loop calls it with `.union2`; the arm that names the specification is not taken |
| `guard` | 7 | private definitions that only `#guard` lines call: `hasV`, `checkedIs`, `sameChecked`, `sameCheckedV1` and three test logs |
| `spec` | 5 | specifications whose callers are `#guard` lines and theorem statements: `OWL.RL.inconsistent`, `inconsistentPlus`, `RdfBased.rbRound`, `rbSaturate`, `scopeStepSem` |
| `fixture` | 5 | the known-bad example |

Held by a specification that no live code reaches: 28 findings, among them the pairs
`ggpLabeledBnodes` and `ggpLabeledBnodesQ`, `serializeNode` and `serializeNodes`,
`readTripleTerm` and `readTtObject`, and `parseElement` and `parseChildren`. The tool computes this;
nothing is listed for them. Two of the 28 are the call of `matchingSubjectsGo` in `matchingSubjects`
(item 1) and the pair `parseElement`/`parseChildren` (item 3): each specification has a replacement
now, and no live code calls it.

## 7. Cost of the missing check

2026-10-15, issue 867: a `@[csimp]` theorem for the derived `Hashable Term` passed `lake build`
and every gate. The C of `FastGraph` still called the recursive hash; it was found by reading the
C of a caller, three minutes into a full build.
2026-10-15, this work: the theorem for `matchingSubjectsGo` had been in the tree since issue 746,
counted `replaced` by the audit, with no caller. The same first run found two modules that call
`cmpBytes` without the import its twin needs (a rule that `lean4-performance` states).
2026-10-15, this work: `XML.parseChildren` was marked "specification only" in the allow list of the
tail-recursion audit, with `parseElement` as its one compiled caller, since issue 755. A second compiled
caller read a chain of markup entities under `rdf:RDF` with one native frame for each level, and the
stack case did not reach it (6,000 levels overflowed 512 KB). It was found by reading the finding
whose owner is `parseChildren`; no finding names `parseChildren` as a left side, because it had no
theorem of its own (section 4). When an allow-list line gives a count of callers, count them with `grep`.
Rule for the next theorem: after `lake build`, run `python3 tools/lean-csimp-reach.py --gate`; a
new `@[csimp]` theorem is finished when the tool shows a caller of its replacement and no finding.
