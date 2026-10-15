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
  they are repaired (section 6). Of the 49 others, 24 are read and listed with a reason in
  `tools/lean-csimp-reach-allow.txt`, and 25 are held by a specification that no live code
  reaches (section 6).
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
   the scan sees no use of any replacement (the positive control: 555 uses on this tree).

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
- It does not measure speed.

## 5. Checks of the tool, with their results

Each check below was run on the tree of this landing.

- **Completeness of the theorem list.** `--cross-check` imports every built module into Lean and
  reads `Lean.Compiler.CSimp.ext`: 162 theorems of this package in Lean's table, 162 in the
  source scan, none on one side only. 99 modules that define the root-level `main` cannot be imported together; none of them holds a
  theorem (the source scan found none; a theorem in them that a macro generates would not be
  seen).
- **Scan of the C.** Two criteria for a function header (the tool's definition pattern, and
  "column 0, ends in `){`") give the same count in each of 966 files (81,699). Every
  occurrence of a wanted symbol outside a prototype or a header is inside a function body
  (1,058) or in a static closure (6); none is anywhere else.
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
repairs, with an empty allow list: 55 findings (the fixture's five included), 36 not
suppressed. The allow list below makes 7 more findings suppressed: the code that reached
their specification is on the list, so the specification is no longer live. Final: 55
findings, 29 allowed (24 and the fixture's 5), 26 suppressed, 0 new.

Repaired (three defects, each with a proof that already existed or a short new one):

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
   both modules. The C now calls `cmpBytesFast`. Test: `lake build` (the guards of `Side.lean`),
   `tests/qlvr/queries.sh` before and after, `tests/sbm11/run.sh` (it runs `Sbm11PermCheck`,
   which imports `Side`). The speed change is not measured.

Left, 24 allow lines plus 5 for the fixture, by reason (the file has each line's module and caller):

| reason | lines | meaning |
|---|---|---|
| `leaf` | 6 | the loop calls the specification for an input where the specification does not recurse (RDF 1.2 triple terms: `joinKeyLoop`, `readObject12Down`, `toNTriplesClose`, `readTtObjectLoop`, `readTripleTermDown`), or reads the replacement text of a markup entity (`XML.parseChildren`) |
| `bound` | 3 | the branch is for a size no array reaches: 2^64 characters (`expandEntityLoop`, `entityWsLoop`) or `USize.size` bytes (`cmpBytesFast`) |
| `twin` | 2 | the twin handles the shapes it improves and calls the specification for the others (`freshTopFast`, `finishSelectRowsPrefix`) |
| `dead arm` | 1 | `labelStepSem`: the loop calls it with `.union2`; the arm that names the specification is not taken |
| `guard` | 7 | private definitions that only `#guard` lines call: `hasV`, `checkedIs`, `sameChecked`, `sameCheckedV1` and three test logs |
| `spec` | 5 | specifications whose callers are `#guard` lines and theorem statements: `OWL.RL.inconsistent`, `inconsistentPlus`, `RdfBased.rbRound`, `rbSaturate`, `scopeStepSem` |
| `fixture` | 5 | the known-bad example |

Held by a specification that no live code reaches: 26 findings, among them the pairs
`ggpLabeledBnodes` and `ggpLabeledBnodesQ`, `serializeNode` and `serializeNodes`, and
`readTripleTerm` and `readTtObject`. The tool computes this; nothing is listed for them.
One of the 26 is the call of `matchingSubjectsGo` in `matchingSubjects` (defect 1 above):
`matchingSubjects` has a replacement now, and no live code calls it.

A line of `tools/lean-tail-recursion-allow.txt` said that `XML.parseChildren` has one compiled
caller, `parseElement`. `Syntax/RdfXml.lean` (`parseChildrenFold`) also calls it, for the
replacement text of an entity that holds markup. The line now says so.

## 7. Cost of the missing check

2026-10-15, issue 867: a `@[csimp]` theorem for the derived `Hashable Term` passed `lake build`
and every gate. The C of `FastGraph` still called the recursive hash; it was found by reading the
C of a caller, three minutes into a full build.
2026-10-15, this work: the theorem for `matchingSubjectsGo` had been in the tree since issue 746,
counted `replaced` by the audit, with no caller. The same first run found two modules that call
`cmpBytes` without the import its twin needs (a rule that `lean4-performance` states).
Rule for the next theorem: after `lake build`, run `python3 tools/lean-csimp-reach.py --gate`; a
new `@[csimp]` theorem is finished when the tool shows a caller of its replacement and no finding.
