Integration recursion review and repair, 2026-10-22

The 17 newly gated declarations were not all flat-input recursion bugs.
Inspection of the Lean source and emitted C separated five flat-input
loops from document/term nesting and one unrecognized existing compiler
replacement. The patch was prepared in `integrate-pr3`, branch
`claude/integration-tail-loops`, from source base `ae5cef545`. It does not
include the parallel XSD 1.1 admission repair.

The flat-input repairs retain the specification definitions and prove
equality to executable twins using `@[csimp]`:

- `Regex.Ecma.lower`: five original C self-call sites traversed pattern
  codepoints. `lowerAcc` builds reversed output and loops over the input.
- `Regex.Profiles.xsdLiterals`: five original C self-call sites traversed
  pattern characters. `xsdLiteralsAcc` preserves escaping and class state
  with reversed output.
- `Regex.quoteReplacement`: two original C self-call sites traversed the
  replacement text. `quoteReplacementAcc` escapes the same characters
  while accumulating reversed output.
- `RIF.groundMatches`: the original C called itself and then combined the
  answer, retaining one frame per sibling. The executable ground matcher
  and list accumulator have a mutual refinement proof preserving yes/no/
  unknown. Both public entry points get compiler replacements so the
  old nested caller cannot bypass the loop.
- `RIF.matchTms`: this already appeared in the inherited allow list, but
  the newly recursive `matchTm` exposed it to the gate as a cycle. The
  original C retained a sibling frame while combining blocked flags.
  The new matcher and accumulator have a mutual refinement proof that
  preserves the substitution and accumulated blocked status, including
  later failure. Both entry points get compiler replacements. The obsolete
  allow-list entry for the specification was removed.

The following classifications justify precise existing-policy `(b)` entries:

- SRX namespace validation: `childrenInSrxNamespace` advances siblings
  with `goto _start`; recursion through `inSrxNamespace` follows XML
  nesting. Original emitted evidence: `ResultsXml.c:282` and line 305.
- XML namespace view/projection: `namespaceViewsAcc` and the specialized
  `List.mapTR` for vocabulary projection loop over siblings. Frames remain
  while processing nested elements. Original emitted evidence:
  `NamespaceView.c:1530`, line 1601, line 2083, and line 2139.
- XSD value identity/enumeration: `valsIdentical` and
  `valsEqualOrIdentical` loop over sibling values; mutual calls follow
  nested `Val.seq` items. Original emitted evidence:
  `Datatypes.c:25275` and line 26534, both with a tail jump on success.
- `Regex.CRe.eraseAssertions` traverses a regex AST. This matches the
  existing allowance scope for `CRe.dotAll` and `CRe.size`. Concatenation
  can produce a linear-depth AST from a flat pattern: this allowance is
  an acknowledged expression-depth limit, not a constant bound or a
  claim of stack safety for arbitrary patterns.
- The new RIF executable workers retain term-nesting recursion, while
  sibling accumulators emit tail jumps. These receive four narrowly
  described `(b)` entries. No pending-length allowance was added.

`OWL.CertNames.frame` already had a proved `frameTR` replacement.
The audit parser missed the theorem's equation because it lacked explicit
`@` names. The signature now uses `@frame = @frameTR`. Before the change,
the only emitted call to `frame` was its own reference body, while `fields`
called `frameTR`; there was no executable naming repair to invent here.

Verification:

- The [focused build](integration-tail-focused-build-second.log) completed
  successfully with 56 jobs, covering the changed proofs and existing
  regex oracle/profile/replacement and RIF matching/engine regressions.
  The first draft's failed simplification is preserved in
  [the earlier build log](integration-tail-focused-build.log).
- [The tail-recursion and compiler-replacement reach gates](integration-tail-repaired-gate.log)
  both passed on the available emitted C. The report includes source and
  cache scope; the parent must still run its final combined build.
- [Nine Lean evaluator controls](integration-tail-flat-inputs.log) passed:
  long regex transforms, long certificate-name framing, RIF value-equal
  and unknown lists, mismatch controls, and long pattern binding. The
  long inputs each contain 100,000 items. The
  [exact probe](IntegrationTailFlatInputs.lean) states its backend limit:
  this is not a Wasm execution.
- The seven printed replacement theorems depend only on Lean's standard
  `propext`, `Classical.choice`, and/or `Quot.sound`. No new axiom, sorry,
  partial definition, or native-decision proof was introduced.
- [Source and emitted-C hashes](integration-tail-source-manifest.json)
  preserve the reviewed implementations and probe results. Native corpus
  and final Wasm replay belong to the parent integration run.

The patch leaves the existing document/term nesting limits explicit. It
does not certify all previously allow-listed recursion or all input sizes.
