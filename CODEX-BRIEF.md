# Brief: XProc 3.1 in Lean (factoidal-core), agent "codex-xproc"

Owner (Dan Brickley) goal, 2026-10-28: "Complete qt4cg.org and pass all its
tests", "zero fails would be massive for publicity", "if we need to
implement more specs, we DO SO!", and "don't forget xproc". Other agents have
put XPath 4.0 (`formal/lean4/L4Factoidal/XPath4/`), XQuery 4.0 (`XQuery4/`),
XSLT 4.0 (`XSLT4/`), XSD 1.1 (`XSD11/`), EXPath and Serialization in Lean.
Your part: an XProc 3.1 processor in Lean on top of them, scored against the
XProc test suite, and bridged to the Factoidal dataflow theorems.

Read first: `CLAUDE.md`, `AGENTS.md`,
`docs/designissues/2026-10-28-dataflow-and-xproc.md` (design record; stage 1a
= acyclic graphs with named ports is merged: `formal/lean4/L4Factoidal/Dataflow/Graph.lean`,
`GraphStages.lean`, `GraphClaim.lean`), and the runner
`formal/lean4/L4Factoidal/Harness/Qt4Run.lean` (model for a test runner).
Issues (read-only for you): danbri/factoidal 1129 (epic), 1130-1134.

Specs: XProc 3.1 https://spec.xproc.org/3.1/xproc/ and the Standard Step
Library https://spec.xproc.org/3.1/steps/ (you have no network; work from
the tests and your knowledge). Tests: `third_party/testing/xproc-test-suite/test-suite/tests/`
(about 3360 test files; documents, schematron, pipelines and lib beside them).

Scope, in order:
1. New tree `formal/lean4/L4Factoidal/XProc31/` (OUT of the library root
   `formal/lean4/L4Factoidal.lean`; add a `lean_exe` `l4xproc` in
   `formal/lean4/lakefile.*` like `l4qt4`). Parse XProc 3.1 pipeline
   documents with the existing XML parser; static analysis (ports,
   connections, cycles XS0001, static options, `use-when`); documents with
   properties (content-type, base-uri); AVTs and XPath options through `XPath4`.
2. Runtime: atomic steps of the standard library (p:identity, p:sink,
   p:count, p:split-sequence, p:wrap-sequence, p:wrap, p:unwrap, p:insert,
   p:delete, p:replace, p:rename, p:add-attribute, p:set-attributes,
   p:label-elements, p:make-absolute-uris, p:namespace-delete, p:string-replace,
   p:add-xml-base, p:filter, p:pack, p:compare, p:error, p:cast-content-type,
   p:json-merge, p:json-join, p:text-* steps, p:xslt (via `XSLT4`), p:xquery
   (via `XQuery4`), p:validate-with-xml-schema (via `XSD11`), p:load, p:store,
   p:archive steps as far as possible, ...) and compound steps p:for-each,
   p:viewport, p:choose/p:when/p:otherwise, p:if, p:try/p:catch/p:finally, p:group,
   user-defined steps and libraries (p:import, p:declare-step).
3. Runner `l4xproc`: run every test, compare with the expected result
   (`t:expect-pass` with schematron assertions; `t:expect-fail` with error
   codes); print TOTAL pass / fail / unsupported and per-feature counts;
   `--list-fails`. Unsupported = a feature not yet implemented; it is not a pass.
4. Bridge theorems (owner priority, "make the codebase a network"): a
   pipeline of XProc atomic steps with one primary port each denotes a
   `Dataflow` graph (stage 1a) and the graph check agrees with the XProc
   static check on cycles (XS0001); p:identity is the identity; p:for-each
   over a sequence is the map of the subpipeline; p:xslt/p:xquery steps
   evaluate exactly as `XSLT4`/`XQuery4` do (definitional theorems).
   No `sorry`, no new `axiom`.

Rules:
- Logic in Lean only. Build from `formal/lean4/` with `ulimit -s 65520`:
  `export PATH=$HOME/.elan/bin:$PATH; lake build l4xproc`.
- Do not edit files outside `formal/lean4/L4Factoidal/XProc31/`, the lakefile
  (one `lean_exe` entry), `docs/designissues/` (a status note) and this
  worktree's `CODEX-PROGRESS.md`, unless a tiny fix in a shared module is
  needed (then list it in the progress file).
- Do not run git commit or git push; the coordinating session commits and
  opens PRs. Write `CODEX-PROGRESS.md` after each milestone: what works, the
  measured score with the exact command, open items.
- Keep compute moderate: build only `l4xproc` and what it needs, not the full
  library; run the test suite with a per-test timeout.
- Work as long as you make progress; aim for the highest pass count with 0
  fail. Report honestly; never mark an unimplemented test as pass.
