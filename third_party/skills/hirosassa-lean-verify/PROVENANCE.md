# Provenance: hirosassa/lean-verify (vendored, unmodified)

- Source: https://github.com/hirosassa/lean-verify
- Commit: 4ab3c516e2e118c16bb0d05db87dc87188ee1a77 (branch main, dated 2026-11-24, fetched 2026-11-26)
- Licence: MIT (LICENSE alongside this file)
- Files: skills/lean-verify/ (SKILL.md, references/, assets/examples/, scripts/), copied byte
  for byte with `git clone` and `cp -r`. All files were read before vendoring; the two scripts
  only look for elan, lean, lake and a lakefile, and use a temporary directory.
- Why: owner request, 2026-11-26, verbatim: "file an issue to test this:
  https://github.com/hirosassa/lean-verify and add it to skills already". Trial tracked in
  https://github.com/danbri/factoidal-core/issues/1136 (test targets and the decision to keep it).
- What it is for here: small functions and single rewrite rules in code that has no Lean source
  (C primitives beside Lean reference bodies, Rust and TypeScript host code), modelled in Lean
  core to find counterexamples or prove equivalence.
- Local policy on top:
  - A proof is "proved in the model". Write it that way; never "the code is correct".
  - Each counterexample becomes a failing test in the original code, with an issue.
  - `native_decide` may confirm a counterexample during a session, but nothing with
    `native_decide`, `sorry` or a user axiom is committed (CLAUDE.md, `factoidal-lean-basics`).
  - It does not audit axioms or `sorry`: run `lean-review` and `#print axioms` on any Lean that
    is committed.
  - Installing elan or adding `plausible` follows `factoidal-lean-basics` and the Lake working
    directory rule, not the skill's `references/setup.md`.
- Do not edit the vendored files; refresh by re-fetching and updating the commit here.
