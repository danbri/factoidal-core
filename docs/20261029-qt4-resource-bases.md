# QT4 query and stylesheet resource bases

Date: 2026-10-29. Tracking:
https://github.com/danbri/factoidal/issues/1161 and
https://github.com/danbri/factoidal/issues/1101.

The QT4 harness gave external query files the test-set directory as their
default static base URI. `fn-transform-94` consequently resolved
`../identity.xsl` from the wrong directory. External queries now use their
own file URI, and their literal resource references are scanned relative
to that file's directory. Inline queries retain the test-set directory.
Explicit environment bases and `#UNDEFINED` remain authoritative; environment
parameter expressions still use the test-set directory for fixture discovery.

Inline stylesheet text can have a base URI in another directory.
`fn-transform-err-9a` supplies such a base and includes `staticbaseuri.xsl`.
The pure evaluator cannot fetch missing text. The harness now preloads literal
references relative to directories named by other literal paths in the same
input. Newly inferred resources have only absolute file URI keys. Two files
with the same basename remain distinct; the engine resolves the actual URI.
The query-input registry preserves each input's absolute logical URI base.
It never combines raw relative aliases from query files and environment
parameter expressions. Explicit static bases define logical URIs while
fixture directories provide the bytes. This prevents a same-named file in
another input directory from hiding a missing query-relative resource.
Normalized relative paths and a canonical-root check confine these inferred
reads to the fixture root. No test-name or option-name rules, semantic
reparsing, fixture edits, or exclusions are involved.

This is a literal-resource preload for the test host. General computed URI
retrieval still needs a resource provider; it is not implemented by this patch.

## Validation

All Lean builds used `formal/lean4` as their working directory. Named
`lake build l4qt4` passed. `tests/qt4-resource-base/run.sh` checks the score,
because the corpus runner itself exits zero even when cases fail.

- Six local cases: external query location, existing and nonexistent inline
  base filenames, identical basenames in distinct directories, and two
  outside-root refusal cases. Before alternate-directory preload: 3 pass,
  3 fail. After: 6 pass, 0 fail, 0 unsupported.
- Six additional identity controls expose same-name collisions across query
  and parameter inputs and check explicit virtual bases and `#UNDEFINED`.
  Before the scoped registry: 9 pass, 3 fail out of 12. The final local set
  is **12 pass, 0 fail, 0 unsupported**.
- Official XQuery `fn-transform`: 130 pass, 6 fail, 1 unsupported before
  these resource fixes; 131/5/1 after query-base repair; **132 pass, 4 fail,
  1 unsupported (137 total)** after resource preload. Cases 94 and err-9a
  now pass. The earlier QName and assertion changes improved the original
  127 pass, 9 fail, 1 unsupported result by another three passes.
- After query-base repair, related sets retained their measured results:
  `fn-doc` 75 pass/1 fail/3 unsupported; `fn-unparsed-text` 94/0/13;
  `fn-resolve-uri` 50/0/1; `fn-static-base-uri` 18/0/0;
  `fn-base-uri` 82/0/1. Broader final-candidate results are recorded separately.
- Core CI builds `l4qt4` and runs the twelve local cases. Full-library CI and
  exact-head package `web-gates` remain required before merge.

Remaining transform failures: 27, 67, 70 and 82e. Unsupported case 48 still
needs selectable older-language behavior. These counts are not a claim that
the entire QT4 library or its unsupported cases are complete.
