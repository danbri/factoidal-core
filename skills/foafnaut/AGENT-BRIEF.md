# Foafnaut: the standard agent brief

Every agent working on Foafnaut reads this first, then `skills/foafnaut/SKILL.md` (code map, builds, traps) and
`skills/local-lean-rules/SKILL.md` (Lean soundness rules). A task brief adds only the task.

## What the project is

Foafnaut is a web browser whose engine, BubblePopKit, is written in Lean 4. The point of writing a browser in Lean is
trust: what the browser does with web content, and what it says about itself, is decided by code that can be read,
checked and proved, not by unverified glue. The aim is a browser that is competitive on the Web Platform Tests and
that is fast, efficient, private, accessible, international and secure, with those qualities weighted equally with
standards conformance.

## The core rule: decisions in Lean, the host moves bytes

- Everything that decides something about web content is Lean: parsing, style, layout, text, paint, scripts (BubblePopJS,
  BubblePopWASM), networking policy (origins, CORS, redirects, address checks), isolation (frames, workers, sandbox),
  find in page, accessibility, and anything else a page or a user relies on.
- **The browser's own words are Lean too.** Internal pages (`about:foafnaut`, `foafnaut:` pages, error and refusal pages,
  version answers) are written by Lean. The engine's identity (version, commit, build time, hygiene counts) is compiled
  into the engine. Facts only the host knows (runtime, platform, file hashes) reach Lean as data and are shown labelled as
  reported by the host. If the two disagree, the page says so.
- The hosts (`run_html.ts`, `native_window.m`, the Hub's `.mjs`) open windows, pass input, fetch bytes, run GPU commands
  that Lean emitted and show what Lean drew. They hold no layout, policy or page-writing logic.
- No JavaScript copy of Lean logic, not even a "fallback". A missing engine op turns the feature off.
- No host drawing cheats: never draw page content with host elements (DOM, AppKit, host iframes or video).
- No Foafnaut-only page APIs. Pages see the web platform.

## Proof and hygiene

- No `sorry`, user axioms, `native_decide`, `unsafe`, `@[implemented_by]` or new `partial def`.
  `labs/demos/foafnaut/LabHygiene.lean` (`lab_ratchet`) must still compile: counts may only fall.
- Linux CI runs a tail-recursion gate (`tools/lean-tail-recursion-audit.py --gate`): prefer tail-recursive or structural
  code over allow-list entries.
- Security decisions come with theorems where they are cheap, and the rest is listed as open in the design record.
- Say exactly what is proved, and what is only tested.

## Performance

- A page that doesn't use a feature pays nothing for it. Give before/after timings in every hand-back.
- Hot paths get cost tests that fail if they turn quadratic.

## Working on the shared Mac

- Commits are authored by Dan Brickley <danbri@danbri.org>, with no Co-Authored-By or session trailers.
- Work in your own worktree on a `wip/` branch. Push it after each passing step. Open a PR; don't merge or push to main
  unless the brief says so.
- One Lean build at a time: use the build lock (`leanlock.sh`, path in the task brief).
- The cloud build queue (`danbri/factoidal-builds`, `build.yml`) holds one pending run, and a new dispatch cancels it.
  Dispatch only when the brief allows it, and log it.
- Coordination log: `/tmp/foafnaut-coordination.log`. One line per claim, result or release, with a prefix naming you.
- Never kill or signal processes you didn't start. Never touch other agents' worktrees.
- Disk is tight: keep scratch small, delete copies you don't need, and stop and report below 4 GiB free.
- Don't sit idle. Commit early and often.

## Words

- User-facing text says "the built-in engine", not "Lean". Name Lean only where the language is the subject.
- Names: Foafnaut (browser), Textnaut, BubblePopKit (engine), BubblePopJS, BubblePopWASM.
- Don't use the word "honest". Plain British English.
- GitHub: technical content only; never quote the owner's chat; no links to upstream Lean issues; never suggest
  contacting people outside the project.
- Real web pages are copyright: probe live, never commit them. Test fixtures are original constructs.

## Hand-back

What changed (PR, commits), what was verified (tests, counts, timings, cloud build), what wasn't and why, open security
items. Don't claim anything you didn't run.
