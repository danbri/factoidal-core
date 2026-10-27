## How to write to the owner (read this first)

Owner, 2026-08-24, verbatim:

> "I pay Anthropic for you to ALWAYS BE STRAIGHT WITH ME. Every time you
> highlight your alleged honesty or straightness in a particular context
> wastes tokens undermining everything else you say."

1. **Never advertise honesty.** No "to be straight with you", "to be
   honest", "I need to be clear with you", "the truth is", "candidly".
   Straightness is the baseline. Announcing it in one place implies its
   absence everywhere else.
2. **Plain technical English**, with domain terminology from established
   authorities — the W3C specifications, the RDF/OWL/SPARQL literature,
   the Lean 4 and F\* manuals. Do not invent vocabulary.
3. **No unsolicited metaphors.** State the mechanism.
4. **Report in ASD-STE100 Simplified Technical English.**
5. **Keep it short.** The owner reads on a phone, between other
   commitments. Lead with the result or the decision needed.
6. **A repeated steer means the last report failed.** Record decisions
   in this file the first time, not the third.
7. **Every issue, PR and CI run you mention gets a full URL and a short
   gloss in parentheses**, e.g. "https://github.com/danbri/factoidal/issues/1009
   (SBM11 in npm)". Only a passing mention may have one of the two. Status
   lists are short paragraphs, not tables; text the owner may paste into
   another session goes in its own code block (the iOS app copies whole
   messages only). Owner, 2026-10-25: "Urls pls always as i am on phone";
   "Please when you mention issues, either link them fully or give a brief
   gloss in parens, ideally both unless the mention is very much \"in
   passing\"."
7. **An explanation of how a subsystem works, once given in chat, is
   written into `docs/designissues/` in the same landing** and linked
   from the worknote index and the relevant skill. Owner, 2026-09-03,
   verbatim: "this and similar ought to be recorded properly somewhere I
   can find it. Ephemeral coding logs aren't that place." The first such
   record: `docs/designissues/2026-09-03-rdf-parsing-strategy.md`.

> **only report to me in ASD-STE100 Simplified Technical English.**

## Repository layout (owner, 2026-10-09)

Owner, 2026-10-09, verbatim:

> "We want factoidal to be built in factoidal build from fstar and lean4
> trees in factoidal-core."
> "Ensure all target specs have a complete and tested lean4
> implementation"
> "/goal complete performant suite all in lean4"

- **`danbri/factoidal-core`** (this repository, branch `main`; it was
  `claude/core-split` until the owner's rename of 2026-10-11): the
  source. `formal/fstar` and `formal/lean4` with their git history
  (rewritten from `danbri/factoidal` to `formal/` paths only), plus tests,
  tools, skills, docs sources and npm sources. No compiled artifacts.
- **`danbri/factoidal-builds`**: the CI that builds Factoidal from a core
  commit (Lean native and wasm, F\* native, JS and wasm), runs the gates,
  and publishes one release per (core commit, artifact set). Its git
  history holds only workflows, build scripts, the `toolchain-cache` and
  `checked-cache` branches, and `latest/<set>.json` pointers.
- **`danbri/factoidal`**: the previous single repository. Its full
  history (2,531+ commits, binaries included) stays there as the record.
  Issues stay there until moved.

# Factoidal — a linked information system with graph data and the Web at its heart

(Owner's framing, 2026-08-22.)

**The product is the system**: a highly optimised, flexible, performant
environment for graph data on the Web — storing it, querying it,
linking it, and serving it over Web protocols. F\* and Lean 4 are how
its APIs, interfaces and protocols are grounded in the W3C
specifications and in mathematics. They are not a separate deliverable, and a specification
is not a substitute for the code that satisfies it.

That grounding is what buys the freedom to go fast: implementations
may be varied, tuned and replaced aggressively, because the specs make
it impossible for an improvement to silently destroy standards
compliance. Executable code is still obtained by **extraction from the
formal source**, never by hand-writing Rust/JS/OCaml that "mirrors" a
spec — that is the mechanism, not the goal.

## Founding view (danbri, 2026-08-22) — verbatim

> "The key thing is to define APIs and interfaces and protocols
> grounded via F\* and Lean4 in W3C specs and maths. These should be
> implemented faithfully, efficiently, tunably, and formally, but
> don't confuse the spec and the code satisfying it. Even as we use
> F\* and/or Lean 4 to define and implement everything. The use of
> these formal languages gives us, and coding agents, collaborators
> etc., a safe platform for experimentation and variation without
> fear that small improvements will destroy standards compliance."
>
> "If we get this right we may get a good chance of creating SOTA
> technology and a highly optimised, flexible, performant rdf db and
> querying etc environment."

What follows from it, and settles recurring arguments:

- **Spec and implementation are DISTINCT artifacts even when both are
  written in F\* or Lean.** A fast implementation is not a betrayal of
  the spec; a spec-shaped definition is not a performance failure. The
  correct relation between them is a proof, not a resemblance.
- **Efficiency and tunability are in scope, not concessions.** Speed
  work is legitimate everywhere, in either tree, provided the spec it
  satisfies stays fixed and the satisfaction is proved or measured —
  never assumed.
- **The point of the formal layer is freedom to experiment.** Agents
  and collaborators should be able to vary implementations
  aggressively; the specs are what make that safe. Treat a refusal to
  optimise "because it is the spec tree" as a category error — move
  or prove the boundary instead.

**Goal:** a performant, compliant engine for RDF Core 1.1 (all concrete
syntaxes), RDF/S, OWL, SHACL, RDFC-1.0 canonicalization, and full
SPARQL 1.1 (query, update, protocol, results) — grounded in F\* and
Lean 4, extracted to native/JS/wasm (and C via KaRaMeL), with
correctness and speed each established by proof, test suites and
measurement, never by assertion.
Standing priorities: `docs/claude-rules/current-state.md` § Standing
priorities.

## Repository and branch (owner, 2026-10-10 and 2026-10-11)

Owner, 2026-10-10, verbatim: **"Factoidal-core should be the new home for
Factoidal."** New Shardborough work belongs here, Lean 4 first and test
first.

Owner, 2026-10-11, verbatim: **"We should call default branch “main”."**
The mainline of this repository is the branch `main`. It continues the
history of `claude/core-split`. Start every work branch from `origin/main`.
Before reusing any Lean file from another checkout or repository (the
`factoidal` monorepo, or a local working copy such as
`/Users/danbri/working/factoidal/formal/lean4`), fetch `origin/main` here
and compare: the file here is newer unless a diff shows otherwise.

Cost of not having this rule: on 2026-10-10 an agent imported Shardborough
Lean files from the `factoidal` monorepo (about 2026-09-07 content) onto a
2026-08-30 branch with no common history with `claude/core-split`. Of 59
changed Lean files, 18 were older than the mainline copies. The landing
took one more agent session (re-applied on `claude/core-split`, commits
`4bfa8b49`, `69e92e14`, `19a32098`).

Second cost, 2026-10-10 to 2026-10-13: the batch 1 coordinator kept landing
on `claude/core-split` after `main` became the mainline, because the
layout note above still read "until the owner renames it, the branch is
`claude/core-split`" in that checkout and it never fetched `main`. The two
lines diverged by 82 and 87 commits; another session merged them
(`a7e9adee`) and both sides had written the same `escapeString` fast form.
Rule: before every push, `git fetch origin main` and check that
`origin/main` is an ancestor of what you push
(`git merge-base --is-ancestor origin/main HEAD`); push to `main` only.

## The public site (owner, 2026-10-25)

Owner, 2026-10-25, verbatim, on the publishing proposal of
https://github.com/danbri/factoidal-core/pull/98: "site serves from /factoidal/
repo". The URL stays https://danbri.github.io/factoidal/. Its Pages workflow
(`danbri/factoidal/.github/workflows/deploy-pages.yml`) builds `docs/` of this
repository, branch `main`, daily and on a `repository_dispatch` that
`.github/workflows/dispatch-pages.yml` here sends when the site sources change
(it needs the secret `FACTOIDAL_PAGES_DISPATCH_TOKEN`). Edit the site here,
never in `danbri/factoidal/docs/`.

## Shardborough is a persistent store for very large data (owner, 2026-10-11)

Owner, 2026-10-11, verbatim: "As for “all in memory” that undermines whole
point of Shardcore which is to support very large persistent stores
efficiently."

Rules that follow:

- A Shardborough performance result is measured on the disk-resident
  query path, with peak RSS and on-disk size reported next to latency. A
  mode that materialises a whole generation in memory
  (`l4block-snapshot-session`, mode `ibk3-full-snapshot`) is an in-memory
  engine; its numbers are not Shardborough results and are not compared
  with disk-backed engines as if they were.
- Gap: query execution materialises the selected blocks (or the whole
  generation) before evaluation:
  <https://github.com/danbri/factoidal/issues/775>.
- Gap: no end-to-end theorem that a persisted query answers the same as
  the in-memory reference evaluator:
  <https://github.com/danbri/factoidal/issues/776>.
- Next layout, approved by the owner on 2026-10-12 ("2 yes", to the
  question "start the new Shardborough layout (SBM11) from the design
  record, in its stages?"): SBM11, wire version 11 — 64-bit global term
  ids, a byte-order global dictionary, sorted quad permutations PSO, POS,
  SPO, OSP with per-block key metadata, and a streaming id query path.
  Design and measured reasons:
  `docs/designissues/2026-10-11-shardborough-vs-qlever.md`. Tracking:
  <https://github.com/danbri/factoidal/issues/787>. IBK3 and IBK5 stay
  readable as the differential oracle until stage 7.
- Owner, 2026-10-12, verbatim: "Consider smb11 our baseline for
  shardcore." SBM11 is the Shardborough baseline: every new Shardborough
  performance or design result is compared with SBM11, not with IBK3/IBK5.
- Owner, 2026-10-14, verbatim: "SMB11 should store rdf graphs regardless of
  source formats - this is why we have reflected w3c rdf core concepts into
  Lean. I don't see any reason for the format to be made so explicit for
  internal data manipulation- file formats are for exchange and publishing".
  Rule: the store takes the RDF abstract syntax (the `L4Factoidal.RDF` terms,
  triples and quads of RDF 1.1 and RDF 1.2 Concepts) from one source layer
  and gives it to one serialiser layer. A concrete syntax is named only at
  those two edges. No module under `L4Factoidal/Storage/` imports an
  `L4Factoidal.Syntax` module. Cost of not having this rule: until
  2026-10-14 the SBM11 packer read only N-Triples and N-Quads, and the
  coordinator asked the owner whether SBM11 should "accept TriG", a question
  that the RDF abstract syntax already answers. Tracking:
  <https://github.com/danbri/factoidal/issues/837>.

## COTTAS suspended; Shardborough is primary; QLever reader (owner, 2026-10-11)

Owner, 2026-10-11, verbatim: "All work on cottas is suspended; Shardborough
is our primary persistent rdf storage mechanism."

- No new work on COTTAS in either tree (F\* `Cottas.*`, Lean
  `L4Factoidal/Cottas/*`, the npm COTTAS functions, which 0.9.0 removed).
  Existing COTTAS code and tests stay as they are; do not delete them
  without a further decision. Persistent RDF storage work goes to
  Shardborough. This replaces the 2026-08-24 "Not urgent: COTTAS" line
  below.
- Owner, 2026-10-13, verbatim: "cottas work is suspended as unnecessary
  unless you think needed for other goals". So the 25 F\* COTTAS theorems
  stay class A ("intentionally abandoned") in
  `docs/fstar-theorem-classification.tsv`
  (https://github.com/danbri/factoidal/issues/757), and COTTAS functions are
  not converted for other gates (the `namedGraphsAux` line of
  https://github.com/danbri/factoidal/issues/752 stays PENDING). Reopen a
  COTTAS item only when another goal needs it, and say which goal.

Owner, 2026-10-11, verbatim: "Can we build a medium sized qlever database
instance and work up enough Lean machinery (call it Factoidal/qlvr) to be
able to access its data on disk for query, or even create/edit? This may
teach us something about Lean." and "consider tail recursive approach".

- `Factoidal/qlvr`: Lean code that reads a QLever index from disk (and
  later may write or edit one). It is a study of an external on-disk
  format, in the same family as the Oxigraph reader
  (https://github.com/danbri/factoidal/issues/671). Tracking:
  https://github.com/danbri/factoidal/issues/778.
- Owner, 2026-10-11, verbatim: "I am interested to see if we can create
  Lean that approximates qlever perf avainst native qlever data, so we can
  work out why our own efforts are too slow: how much is lean vs approach."
  The qlvr performance work separates two causes of slowness: the cost of
  the Lean implementation (the same algorithm, measured in Lean and in C)
  and the cost of the storage and query design (the same Lean code, run
  on QLever's layout and on Shardborough's). Every claim in that record
  names the measurement that supports it.
- Every decoder over input-proportional data is a loop or tail call
  (accumulator), never one stack frame per item. Check with
  `python3 tools/lean-tail-recursion-audit.py --gate` (read the exit code)
  and a `tests/stack` case at a size above any wasm stack limit.
- Support library: owner, 2026-10-12, "library yes" (`L4Factoidal/Prim/Bytes.lean`,
  https://github.com/danbri/factoidal/issues/797). Rule: a C primitive
  (`@[extern c inline]`) always has a Lean reference body, a separate non-extern
  reference definition, and a differential test that runs on every target
  (native and wasm32: `tests/prim/run.sh`).

## Capability-aware planner (owner, 2026-10-12)

Owner, 2026-10-12, verbatim: "capability-aware, cost-based planner for data
access, computation and service interaction, with Lean-defined semantics and
adaptive execution." and "SPARQL would be one way to express requirements.
SQL, REST, MCP tools, file sources and LLMs would offer different ways of
satisfying them. Shardborough would be an execution and storage option, not
the place everything must first be imported."

- Owner, 2026-10-12, verbatim: "service descriptions and adaptive tool
  orchestration. Lean supplies knowledge the planner can exploit;
  Shardborough supplies one efficient place to retain and execute data;
  temporal reasoning makes the distributed strategies composable." A proved
  Lean equivalence is a planner rewrite; an unproved one needs a
  differential check.
- Do not design a path that must import data into Shardborough first.
- Probing and discovery are costed work: do a step only when the expected
  saving is more than its cost.
- Semantics in Lean; system behaviour as a state machine with invariants
  (TLA+ discipline). Candidate Lean framework: Veil (owner, 2026-10-12:
  "Keep Veil on the relevant mentions lists too").
- Full direction, model and prior work (PDQ, Calcite, Comunica, SPARQL
  Anything, Veil): `docs/designissues/2026-10-12-capability-aware-planner.md`,
  skill `capability-planner`. Epic:
  https://github.com/danbri/factoidal/issues/800. OKR batch 2 (proposed):
  https://github.com/danbri/factoidal/issues/801. Parallel block scans, then
  PushIR: https://github.com/danbri/factoidal/issues/799.

> **CLAUDE.md is short on purpose.** Operational detail lives in
> per-topic skill docs (`skills/<name>/SKILL.md` —
> [agentskills.io](https://agentskills.io) format, vendor-neutral) and
> design docs (`docs/designissues/`). The rules below are the ones
> every session must have in working memory. The rest is one click
> away — the `## Skills` section at the bottom of this file lists what
> exists, follow the link when a topic comes up.

## :warning: F\* Syntax Traps :warning:

Full examples + more traps: [`skills/fstar-module-style/SKILL.md`](skills/fstar-module-style/SKILL.md).
The two that corrupt files silently:

1. **F\* block comments `(* ... *)` NEST.** A stray `*)` inside a
   comment (e.g. quoting `construct(*)`) closes it early and F\*
   reports a syntax error **hundreds of lines later**. Never put `*)`
   or `(*` inside a block comment — reword ("COUNT-star") or use `//`
   line comments. Same trap in OCaml: write `(F-star)`, not `(F*)`.
2. **Reserved-ish identifiers with off-by-one errors.** `total`,
   `synth`, `in_mem`, and anything a parser can read as a dangling
   `in` are rejected with the error pointing at the line **after**
   (or below) the offender. Prefix with the domain noun
   (`triples_total`, `mem_dataset`). On any unexplained "Syntax
   error", check the line *above* the reported one first.

## Iron Rules

1. **The formal source is the source of truth.** RDF/SPARQL logic
   lives in `.fst` files (`formal/fstar`, the shipping engine) and in
   `.lean` files (`formal/lean4`, `L4Factoidal`) — never in
   hand-written code downstream of them.
2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen OCaml`
   or KaRaMeL for C/WASM; the Lean tree compiles via Lean→C→wasm. Never
   vibe-code an implementation that "mirrors" the spec. Optimising an
   implementation IS allowed and wanted — inside the formal source,
   where the refinement can be proved.
3. **`assume val` = acknowledged gap OR allowed realisation — never a
   silent hole.** An `assume val` is one of two things, and each has a
   home:
   (a) an acknowledged **GAP** (logic that should be extracted-from-F\*
   but isn't yet) — MUST have a stub patch in
   `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`
   named `<issue>_<description>.sh` with a corresponding open GitHub
   issue; or
   (b) an allowed **realisation** under rule #11 (pure I/O — file/clock/
   socket; a host-engine call-out; a vendored crypto primitive; or an
   Option-B perf realisation whose byte-format spec lives in F\* with a
   hash-witness CI test) — realised in `experimental_ocaml_glue/*.sh`.
   Most of the **82** `assume val`s today (18 modules, measured
   2026-09-03) are (b) (the COTTAS/HDT storage I/O layer). Count them,
   do not quote this line: `grep -rhE '^[[:space:]]*assume val '
   formal/fstar --include='*.fst' --include='*.fsti' | wc -l`. This rule
   said "~148" from an unmeasured estimate until 2026-09-03; per-module
   figures are in `docs/claude-rules/current-state.md` § assume val
   inventory, beside the same command.
   Neither kind may be a *silent* hole: a (a)-gap without an
   issue, or a (b)-realisation carrying semantic/planning/byte-layout
   logic that belongs in F\*, is a violation. (Audit: `docs/designissues/
   fstar-ocaml-boundary-audit.md`.)
**Lean Lake working directory.** `formal/lean4/` is the self-contained
Lake project. Every `lake build`, `lake exe`, or `lake env` command must run
with `formal/lean4/` as its explicit working directory. Repository Git
commands run at the repository root. Do not combine them in a command which
depends on a preceding `cd` remaining in effect. Never invoke `lake` from the
repository root: check the current tool call's working directory before every
Lean command. This was repeatedly missed on 2026-08-31 and produced invalid
root-level Lake failures.
4. **Parsers belong in F\*.** RDF format parsers (N-Triples, Turtle,
   N-Quads, TriG, RDF/XML, CSV/TSV results) are F\*-implemented and
   extracted. New parsers MUST be written in F\* first.
5. **Full SPARQL 1.1 is the target.** Query, Update, Protocol, SERVICE,
   all result formats. Never default to 1.0 manifests when 1.1 exists.
6. **Run the real W3C test files.** Read manifests, `.rq`, `.srx`,
   `.ttl` from disk. No synthetic queries "inspired by" W3C tests.
7. **No cobbling.** No hand-written JS/Rust/OCaml reimplementations of
   what F\* defines. Add functionality in F\* first, then extract.
8. **RDF semantics are not optional.** rdf-mt tests verify literal
   equivalence, datatype handling, language-tag normalization, RDFS
   closure rules. Core requirements, not "just inference."
9. **Binaries are built and published by `danbri/factoidal-builds`,
   never committed here.** (Changed 2026-10-09 by the core/builds split;
   until then this rule said "commit compiled binaries". Owner, 2026-10-10,
   verbatim: "Actually we have committed build artifacts before to aid
   testing in CI, but it got heavy hence new builds repo.") A fresh clone
   still runs tests with no toolchain: `tools/fetch-builds.sh` installs
   the newest release whose source commit is in this checkout's history
   into `bin/<platform>/` (plus the wasm and JS bundles under `npm/` and
   `docs/`), after checking every file's sha256 against the release's
   `build-info.json`. `tools/ensure-test-env.sh` calls it. The installed
   paths are in `.gitignore`. A binary that does not match a source
   commit of this repository is not a test subject: never copy one in by
   hand. Record: `docs/designissues/2026-10-09-core-builds-split.md`.
10. **No `--lax`.** All F\* must verify under z3 4.13.3 with no `--lax`,
    no `--admit_smt_queries`, no escape-hatch flags. The last legacy
    exception (`SPARQL11.Parser.fst`'s two `--admit_smt_queries true`
    pragma regions, 119 definitions) was eliminated 2026-07-10; the
    rule now holds with no carve-outs. Never add a new one.
11. **Inside the verified library boundary, OCaml is `assume val`
    realisations only.** Hand-written `.ml` in
    `formal/fstar/ocaml-output/*.ml` and patches in
    `formal/fstar/experimental_ocaml_glue/*.sh` may only realise
    `assume val` declarations: pure I/O (file/clock/socket),
    host-engine call-outs (e.g. regex), or vendored crypto primitives.
    Byte-layout for a companion file is **not** acceptable here — the
    byte assembly belongs in F\* (`serialize : data -> Tot (list u8)`),
    and the OCaml side reduces to `write_bytes`. Consumer tools (CLI,
    runners, HTTP entry points) are not part of the verified library
    and belong in `bin/<consumer>/`.

    **Recovery plan + boundary audit + I/O verification pattern:**
    - [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](docs/designissues/2026-05-07-query-planning-fstar-recovery.md)
    - [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](docs/designissues/2026-05-07-io-verification-and-third-party.md)

    **Until** the boundary audit completes and recovery Phase 9 lands,
    the project carries the qualifier "**parser and algebra spec
    verified in F\*; on-disk backend has unverified OCaml-side
    optimization layers being migrated back to F\* (see fstar-purity-
    unwind.md)**" on READMEs, demo pages, talks, and PR descriptions.
12. **Activate the F\* opam switch before any F\* work.**
    `eval $(opam env --switch=fstar)` — every shell, every time, before
    `make verify` / `build-ocaml.sh` / `fstar.exe`. If `fstar.exe` is
    missing from PATH, stop and activate; do not burn time on partial
    builds. See the `fstar-env` skill for setup.
13. **No Claude attribution anywhere in git history.** This covers
    two things, and the second was missed for a month:
    (a) **Message content** — no `Co-Authored-By: Claude`, no
    "Generated with Claude Code", no session links, no prose crediting
    Claude in commit messages.
    (b) **Author and committer identity** — every commit is attributed
    to the responsible HUMAN. Owner instruction, 2026-08-26, verbatim:
    "all attributions are to responsible human only".
    This repo policy overrides the harness default, and the harness
    actively pushes the other way: the hosted CCR image ships a
    SessionStart hook setting the GLOBAL identity to
    `Claude <noreply@anthropic.com>`, plus a Stop hook that instructed
    the agent to run `git config user.name Claude` whenever a commit
    failed GitHub's Verified check. An agent obeying that hook would
    have rewritten the human author out of the commit — the hook and
    this rule were in direct contradiction, and the hook was the one
    with teeth. `tools/sandbox-bootstrap.sh` now pins the
    REPOSITORY-LOCAL identity on every session start, which git prefers
    over the global one regardless of hook ordering, and reports it in
    the bootstrap block. Accepted cost, stated so nobody "fixes" it:
    the container's SSH signing key is registered to the bot address,
    so human-committed commits show as "Unverified" on GitHub. Correct
    attribution outranks the badge. Full rule:
    [`skills/github-coauthor-policy/SKILL.md`](skills/github-coauthor-policy/SKILL.md).
14. **A repaired methodology error is not done until the docs that
    prevent its repetition are updated.** After identifying and fixing
    an error in our own working method — a wrong causal claim, a
    silent-failure mechanism, a discipline that was skipped — revise
    CLAUDE.md and/or the relevant `skills/<name>/SKILL.md` in the SAME
    landing, so the next session inherits the correction instead of
    rediscovering the mistake. Name the error concretely, with its
    date and cost; a rule without its war story does not stick
    (`skills/measuring-inference/SKILL.md` is the model — every rule
    carries the wrong claim that paid for it). The repair commit and
    the doc update belong together; "fixed it, will document later"
    is how the same failure bills twice.

## Known sound-but-narrow rewrites

`OWL.QueryRewrite.fst` — N=1 qualified `CE_MaxCardinality` rewrite
emits an anchor triple `?subj P ?_mxqc1_anchor_<k>` to make parent7
pass. The anchor silently drops vacuous-truth individuals (zero
`P`-edges satisfy max-1) and OWL Full punned class-individuals — that
narrowness remains. The internal-variable LEAK the 2026-07-09 strict
runner exposed (`?_sv_`/`?_mc_`/`?_mxqc1_` vars appearing in `SELECT *`
result rows) is FIXED (task #100): `OWL.QueryEval.eval_select_query_owl`
strips rewrite-internal vars from the FINAL user projection only, via
`SPARQL11.Algebra.strip_rewrite_internal_vars`. It must stay at the
top level — inner `wrap_distinct_over_ggp` Select_All sub-selects
deliberately re-expose the anchor var so the enclosing pattern can JOIN
on it (simple5), so stripping inside them decorrelates the join. The
regime suite is at 70 pass, 0 fail (out of 70; re-measured 2026-07-10). Tracked in **#236**. Generalise from anchor
→ UNION as documented there before relying on this rewrite for OWL DL
outside the entailment regime suite (the anchor still MULTIPLIES rows
per P-edge and drops vacuous-truth individuals).

## Standing decisions (owner, 2026-08-24)

Recorded here because they were repeated several times before being
written down. Verbatim; paraphrase drifts.

### Port functionality, not files

> "the key thing is to port functionality not files. The port was partly
> motivated by fear F\* version was accumulating cruft and this may help
> to clear it."

Module-count coverage is a progress indicator, not the goal. Where an
F\* module is cruft, the Lean side implements the FUNCTION correctly and
the F\* file is marked, not transcribed.

### Priority order

> "Good to progress Cottas but I suggest core of rdf/s, sparql, owl, rif,
> csvw, shacl, shex, xml, xpath, cslt, schematron are more urgent. Cottas
> rdf store didn't really get mature enough to use in f\*, we may ship
> Factoidal and make a separate FactoidalDB repo to focus attention on
> the issues."

- **Urgent:** RDF/S, SPARQL, OWL, RIF, CSVW, SHACL, ShEx, XML, XPath,
  XSLT (read from "cslt"), Schematron.
- **Not urgent:** COTTAS. Possible future split into a FactoidalDB repo.

### Lean 4 is the intended full-scope target (owner, 2026-08-29)

> "The Lean port is only a week old, but improved quickly enough that I am
> inclined to make the switch. It hasn't yet been applied to the full scope of
> Factoidal but that is my intent."

This newer direction makes the Lean 4 tree the target for the full Factoidal
scope. It changes the 2026-08-24 COTTAS ordering for the block-engine
workstream. It does not claim current Lean/F* parity. Keep the existing F*
path executable as lineage and a differential oracle until the corresponding
Lean functionality and gates land. Port functionality, not files.

### F\* stays as the reference until every relevant theorem is classified (owner, 2026-10-10)

> "preserve the F* implementation as a reference until every relevant
> theorem is classified as:
> Reproved in Lean with the same meaning and hypotheses.
> Replaced by a clearly stronger Lean theorem.
> Superseded by a different explicitly justified semantic formulation.
> Intentionally abandoned, with the loss of assurance documented."

- This is the exit criterion for retiring the F\* tree. It adds to the
  2026-08-29 decision below (keep F\* as lineage and differential oracle
  until the Lean functionality and gates land): both must hold.
- Until every relevant F\* theorem has one of the four classes, with the
  Lean theorem named (or the justification or the loss written), F\* stays
  in `danbri/factoidal-builds` CI and in the differential tests (`l4diff`,
  `tests/known-defects`). Nothing under `formal/fstar` is deleted.
- Tracking: https://github.com/danbri/factoidal/issues/757.

### Work is organised as OKR batches (owner, 2026-10-10)

> "Ok lets organize work as OKRs, can you batch up some work as OKRs "batch
> 1"? Track in a single issue and point to issues. I will review and approve
> the goal."

- One GitHub issue per batch holds the objectives and key results. Each key
  result has a measured baseline, a target number, the command that measures
  it (in its issue) and links to the issues that do the work.
- The owner approves a batch before its new work starts. Work already
  running when the batch is proposed continues.
- Batch 1: https://github.com/danbri/factoidal/issues/768.
- Owner, 2026-10-12, verbatim: "OKRs - extend batch 1 to 2026-10-15." and
  "/goal OKRs addresses successfully especially perf and scaling should
  approach SOTA". So batch 1 runs to 2026-10-15, and performance and
  scaling are measured against state-of-the-art engines on the same machine
  and the same input (for example Oxigraph and Serd for parsing and SPARQL,
  HermiT for OWL DL), never only against the F\* engine or an earlier
  Lean build.
- Batch 2: https://github.com/danbri/factoidal/issues/801 (approved
  2026-10-12). Owner, verbatim: "Batch 2 yes, noting that some lean overhead
  may be unavoidable". A Lean-against-C speed target is a goal: when it is
  not met, name each remaining cost and say whether Lean's semantics need it
  or an issue removes it.
- Batch 1 KR 1.3 (TriG packs in chunks,
  https://github.com/danbri/factoidal/issues/769): owner, 2026-10-13,
  verbatim: "Kr 1.3 store". It belongs to the store session.

### OKR batch 3 approved; IBK refuses empty graphs (owner, 2026-10-22)

> "Batch 3 / Work on Batch 3 progress. Issue 880: refusal."

- Batch 3 (https://github.com/danbri/factoidal/issues/875) is approved.
- https://github.com/danbri/factoidal/issues/880: the IBK4 and IBK5 stores
  refuse a request whose result needs a named graph with no triple (CREATE
  GRAPH, a TriG graph block with no triple), with a message that names the
  rule. They do not get the SBM11 graph list. IBK stays a read oracle until
  SBM11 stage 7.
- KR 1.2 (4 threads against 1 thread), owner, 2026-10-23, answers to two
  questions: "Start now" (the allocator work deferred on 2026-10-22 with "Yes
  lets come back to allocator later") and "Remove it" (d17, which block
  metadata answers with no scan). KR 1.2 is judged on d10, q07, q19 and q21.
  The allocator work starts from branch `batch3/kr12-percache`; a change to
  the default allocator settings is shown to the owner with its measurements
  before it lands. Record: https://github.com/danbri/factoidal/issues/961.
- Owner, 2026-10-23, answer "Land it" (to: land branch `batch3/kr12-thp` on
  `main`): `l4sbm11` turns transparent huge pages off at the start of `main`
  (`prctl(PR_SET_THP_DISABLE, 1)`; `L4_THP=on` keeps them), and each pool
  worker keeps a 2,048-page dictionary page cache. Reason: d10 peak RSS 4/1
  2.10 to 1.19 with no time change (stage 1i of
  `docs/designissues/2026-10-12-parallel-block-scans.md`).
- KR 1.2 closed, owner, 2026-10-24, answer "Close: 3 of 4 met" (to: how to
  finish KR 1.2). d10 0.39, q19 0.38 and q21 0.36 meet the 0.4 ratio; q07 is
  0.50 and not met. Stage 1p measured that block decode scales with threads;
  the rest of the q07 gap is variation between processes on the 4-vCPU VM
  (single q07 runs 1.8 to 2.6 ms at 4 threads), larger than any remaining
  fix. https://github.com/danbri/factoidal/issues/961 stays open for q07.

### Issue 566 — the hex layer. RULED, do not ask again.

> "Yeah DO NOT PORT THAT TERRIBLE HEX CRAP!!!"
> "We have no users so rip it up where it is crap."
> "Fix it upstream in F\* and do not worry about legacy. You can defer
> that for now just mark the F\* file as fucked and link to GitHub. Do it
> right in Lean. F\* Cottas is essentially unused. I am only human using
> anything."

- Do NOT port the hex layer to Lean. Lean implements the byte format
  directly.
- The F\* file carries a header marking it broken and linking
  <https://github.com/danbri/factoidal/issues/566>. Legacy compatibility
  is deferred; there are no users.
- `Parquet.Footer` was waiting on this call. The call is made and the
  same ruling applies. It is not blocked and needs no further asking.

### RDF.NQuads.Streaming and SPARQL11.Parser.AskBgpRoundTrip

> "These are important. We need performant nquads and sparql
> implementations across all surfaces!"
> "Rdf.nquads.streaming it is ok to make the changes, ideally both f\* and
> lean4 behave same"

Changes approved. The two trees should agree in behaviour; where the
Lean side changed (the streaming offset), the F\* side follows rather
than the two drifting.

### Prove over an abstraction

> "Ideally we should prove it over an abstraction of both, in lean4 and
> also optionally f\*"

Where a property holds of both trees, state it once over an abstraction
(a typeclass or parameterised structure in Lean) and instantiate it,
rather than proving it twice. Lean first; F\* optional.

### One fat core wasm; no demo content in the package (owner, 2026-10-20)

> "Ok that settles it / For now, we have a single fat core. / PUT EVERYTHING
> IT. Remove demo triplestore fontent and demo functions from npm zip. We can
> revisit efficient modules later. / We will also try to improve LWS before
> shipping"
> Earlier the same day: "Hold off on the grouping" (no README tiers of
> conformance-tested / own-suite / experimental).

- `@factoidal/core` is one module with one wasm that carries every
  capability the Lean tree has. Owner, same day, verbatim: "all this stuff
  goes into a single mod we call Factoidal/core and a dingle wasm. Filename
  is less important". No capability is removed: the old second wasm
  (`l4factoidal-core.wasm`) served a subset of the full table
  (`Wasm/Dispatch.lean` holds every core op; `Wasm/CoreDispatchTests.lean`
  checks this at build time), so dropping it from the package removes a
  duplicate, not a function. Profiles per package (`@factoidal/kgx`,
  `kgx-lite`, `xml`) are deferred, not refused.
- The bundled sample-store data (4,434 triples) and the demonstration-only
  functions (`matrix*`, `sigmoid*`) leave the tarball. Every CLI command
  stays. Owner, verbatim: "All the CLIs are still bundled i just didn't
  want any actual demo triples cluttering the file." The `sample-store`
  command builds a small store from inline triples on demand.
- LWS work happens before 0.10.0 is published.
- Tracker: https://github.com/danbri/factoidal/issues/882.

### The npm package is Lean 4 only (owner, 2026-10-10)

> "I understand our NPM module Factoidal/core is currently a mix of components
> derrived from the F\* and/or Lean4 trees here. This looks potentially bloated
> and bug-prone. We should make the main module Lean4-based. Private builds
> might compare this with F\* (or indeed different wasms from different
> toolchains)."

The published `@factoidal/core` carries one engine, the Lean 4 build. F\*
bundles and builds from other toolchains are for private comparison builds
(factoidal-builds artifacts, `l4diff`), not for the package. Plan and gaps:
`docs/designissues/2026-10-10-npm-lean-only.md`,
https://github.com/danbri/factoidal/issues/713.

### OWL 2 test scoring (owner, 2026-10-10)

> "711 accept your recommendation"
> "721 Add an OWL 2 RDF-Based Semantics"

- https://github.com/danbri/factoidal/issues/711: `WebOnt-I5.5-005` is a
  disputed fixture. It is a local override that names the issue, counted
  apart, and stale (the run fails) if it ever passes. Reason: OWL 2 Mapping to
  RDF Graphs §3.1.2 Table 4; its conclusion has no ontology header.
- https://github.com/danbri/factoidal/issues/721: the Lean tree gets an OWL 2
  RDF-Based Semantics regime. The 12 PositiveEntailmentTests that are DIRECT
  with species FULL only, and the catalog's 482 RDF-BASED cases, are judged
  there. They are not moved to an "unsupported" or "not applicable" bucket.

### rdf:first and rdf:rest functionality in the RDF-Based regime (owner, 2026-10-10)

> "as rdfs editor and rdfcore wg cochair I consider those properties
> functional by their definitions, even if the available languages at the
> time didnt make it easy to state. We can go either way, be guided by
> related specs/tests. Just decide and move on."

- Decided by the coordinator, guided by the related specifications as asked:
  WebOnt-I5.5-001 and -002 are local overrides of suite `owl-rdf-based`
  (https://github.com/danbri/factoidal/issues/734), counted apart and STALE
  (the run fails) if they ever pass. Reasons: RDF 1.1 Semantics Appendix D
  imposes no well-formedness conditions on the collection vocabulary and
  leaves them to semantic extensions; OWL 2 RDF-Based Semantics section 5,
  that extension, declines them; the catalog marks both cases `Proposed`.
- The owner's reading (functional by definition) is not built into the
  regime, whose rules are proved against the 2012 conditions. A semantic
  extension that adds it is permitted by Appendix D and would be its own
  opt-in regime with its own condition bundle.

### GRDDL: 13 disputed cases are not valid tests currently (owner, 2026-10-10)

> "Grddl - postpone for now, i am making enquiries. So just mark it as not a
> valid test currently."
> "Grddl should not be postponed, only that test"
> "730 - do langconneg2 and langconneg3 join h - yes"

- GRDDL work continues. Only the cases under the owner's enquiries are marked
  not valid: the 7 cases whose networked inputs the W3C edited after 2007 and
  the 4 `loopx` cases whose served stylesheet contradicts the expected outputs
  (https://github.com/danbri/factoidal/issues/730). The third quote adds
  `langconneg2` and `langconneg3`: both served language representations of
  `td/conneg.html` link to `https://musicbrainz.org/...` where the 2007
  expected outputs say `http://`. They are files
  `tests/local-overrides/grddl__*.json`; `l4grddl` counts them apart and
  reports a STALE override (a failure) if one starts to pass.
- Coordinator error, recorded per rule 6: the first message was read as
  "postpone the GRDDL suite", and for about 30 minutes the whole suite was
  labelled not valid in `tools/lean-scoreboard.sh` with its failures
  uncounted. The owner corrected the scope; the suite-level label is removed.

### Triple-term transparency and the isomorphism row (2026-10-19)

Owner, verbatim, on two open questions: "Decisions: go with your gut".
The choices below are the coordinator's, under that delegation.

- https://github.com/danbri/factoidal/issues/873, W3C `opaque-iri`: the
  OWL 2 RL closure op applies `owl:sameAs` substitution to IRIs inside a
  triple term, as RDF 1.2 Semantics and the W3C positive entailment test
  require, and as `regimeEntails .rdfsPlus` already does. The OWL 2
  Profiles §4.3 rule table is the floor, not the ceiling.
- https://github.com/danbri/factoidal/issues/868, row
  `iso-many-bnodes-relabel`: keep the time bound of 3.0 per doubling.
  Instructions grow linearly (4.01x for 4x input); the extra time is
  cache misses, and a linear parse alone gives 2.1 to 2.2 on the same
  machine. No instruction-count harness is added for this row.

### JSON-LD-star follows the RDF 1.2 direction (owner, 2026-10-26 and 2026-10-27)

> "implement JSON-LD-star: JSON-LD-star is SOTA. It will likely change a bit,
> but let's start there first."
> "decisions - do something sensible and record the choice. Go for whatever is
> closer to RDF 1.2 direction."

- Target: the json-ld-star PR 61 tests (`third_party/testing/json-ld-star`),
  Lean 4 only, opt-in option `rdfstar`; score `l4jsonld-api --star`.
- Where the fixtures or the outline disagree with RDF 1.2 Turtle, follow RDF
  1.2 and record a local override: an annotation's `@id` may be an IRI; fromRdf
  folds any reifier of an asserted triple into `@annotation`.
- Record: `docs/designissues/2026-10-26-jsonld-star.md` § Decisions.

### Freeform composition over checked components (owner, 2026-10-25)

> "we want to enable and underwrite freeform composition as I sketch, using
> checked components and checkable paths, without anticipating each path
> explicitly. ANd maybe sure do stuff \"off the ranch\" but know we're in the
> jungle when doing so"

- Prove each component's contract once, against the wire types; a general
  composition lemma gives the guarantee of any pipeline that type-checks.
  Do not write one theorem per path (`pipeline_sound` was one path; the
  replacement is `query_sound` over any `LawfulStore` plus one theorem per
  data source).
- The guarantee of a path is computed: the composed contract plus the union
  of the named assumptions of its components (npm `run()` reports it).
- A component that is not proved may run after an explicit opt-in; its
  evidence record says so. Never report a guarantee the path does not have.
- Record: https://github.com/danbri/factoidal/issues/975#issuecomment-6393905605

### Network retrieval goes into the evidence record, as high-risk data (owner, 2026-10-25)

> "Any transactions with the global web also need to go into the evidence
> pipeline system - if we dereference http or https at least. maybe ftp,
> gopher and others, keep records of headers, ip addresses, certs, timing etc
> etc. Treat this information as potentially high risk re security/privacy."

- Every HTTP or HTTPS read for a pipeline step gives a retrieval record
  (request and response headers, redirects, remote address, TLS and server
  certificate fingerprints, timing, body SHA-256). A scheme with no record type
  is refused, not fetched without a record.
- Default deny: credential values (Authorization, Cookie, Set-Cookie, token
  query parameters) are removed, never hashed; no local address or client
  certificate; the full record stays in a local store; shared provenance gets
  a small subset unless the caller opts in.
- TLS: keep the crypto details (version, cipher suite, key exchange group,
  signature algorithm, ALPN, SNI, the full server certificate chain in DER,
  the verification result and trust anchor, SCTs, a stapled OCSP response).
  Owner, 2026-10-25, verbatim: "Re recording tls, keep more of the crypto
  details too, certs etc". Never session keys, key logs or client
  certificates.
- A retrieval is an assumption of the run, named with the body checksum, never
  a theorem.
- Pipeline wires: SELECT gives `table` ("select give table? Sure"); a source's
  name has no default from its locator ("no default"). Owner, 2026-10-25.
- Design: section 4 of `docs/designissues/2026-10-25-tabular-and-source-models.md`;
  tracking https://github.com/danbri/factoidal/issues/1035.

### Experimental code notice; AES through WebCrypto (owner, 2026-10-27)

Owner, 2026-10-27, verbatim: "main docs, cli, readme, hub should say that all
protocol, auth/security code, CLIs etc (core library) “EXPERIMENTAL
UNDEREEVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.”"

- The notice, spelled `EXPERIMENTAL UNREVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.`, is at the top of `README.md`,
  `npm/factoidal/README.md`, the hub index and the hub servers page, in the
  npm package description, in every `factoidal` help text, and on standard
  error when a server, client or key command starts (`REVIEW_WARNING` in
  `npm/factoidal/bin/factoidal.mjs`). A new server, protocol or security
  surface carries it too.
- AES (for XML Encryption and JWE, https://github.com/danbri/factoidal/issues/1081):
  WebCrypto on every JavaScript host, decisions in Lean, measured by vectors
  and a differential run. Owner, verbatim: "Why not just WebCrypto everywhere
  (browser/node or wasm fallback?)"; then "Yes" to amending the crypto policy.
  Native executables: owner, 2026-10-27, verbatim: "Ok for now: “My proposal
  is HACL* Vale on x86-64 and a refusal on other CPU”". So native x86-64 uses
  HACL\* Vale AES-GCM; other native CPUs refuse AES with a message that names
  https://github.com/danbri/factoidal/issues/677. Rule text:
  `skills/crypto-policy/SKILL.md` § AES through WebCrypto.

### There are no users. Prefer the right structure to the compatible one

The issue-566 ruling above says "We have no users so rip it up where
it is crap." That is a GENERAL rule, not a hex-layer one. Owner
restatement, 2026-08-26, verbatim:

> "You speak like this is a huge codebase with many users. Thw honest
> truth is that I made it using my anthropic claude subscription
> overnight, and it has zero audience and users so far."

Blast radius, backwards compatibility and migration cost are not
arguments here. When a design is wrong, change the design; keep the
superseded artifact only as the record of why it changed. Cost of
getting this wrong: on 2026-08-26 the coordinator recommended the
conservative option for
[issue 609](https://github.com/danbri/factoidal/issues/609) item 3 —
adopt the divergence as a stated interpretation condition rather than
repair the dataset embedding — on blast-radius grounds that only apply
to a codebase with users. The owner overruled it: "The correct path is
(3.)".

### A stated shortfall is a failing test plus an open issue (owner, 2026-09-07)

Owner, verbatim, on a hub sentence saying a module header "states plainly" that
PRECIS is not implemented:

> "If you're talking about prose in comments, that is better than nothing, but
> it is close to nothing. You must use failing tests, annotated to show the
> expected failure, and an associated open github issue to track the
> shortfall."

Rule: any "not implemented", "not yet", "deliberately does not", "out of
scope for now" or "known gap" in code, README, design record or hub post
carries (1) an OPEN GitHub issue (full URL in the text), and (2) a test that
FAILS today, marked as an expected failure naming that issue, whose harness
turns the suite RED when the case unexpectedly passes, so the flip to a real
assertion and the issue closure cannot be forgotten. Prose alone is not a
record of a shortfall. First instance: PRECIS for XMPP JIDs,
<https://github.com/danbri/factoidal/issues/676>, with the `xfail` cases in `npm/factoidal/test/xmpp.test.mjs`.
Conventions per test kind: `skills/test-suites/SKILL.md` § Expected failures.

### Defective W3C test data is not our failure (owner, 2026-10-21)

> "Dont list bad tests as our failing"

A test with defective upstream data is reported apart, after the total, as
"K excluded (defective test data)", with an open issue that gives the
evidence. It is not in pass, fail or the total, and it is not an expected
failure. The run still fails if the case passes. An engine shortfall is never
put in this category. Rules: `skills/test-suites/SKILL.md` § Defective test
data. First case: CSVW validation test308,
https://github.com/danbri/factoidal/issues/700.

### Test failures and scores: Lean 4 only (owner, 2026-10-21)

> "No focus on lean4 here. F* out of scope"

Said in reply to a report that put an F\* RDF 1.2 Semantics failure beside
the Lean scores. Read it as: when you report or work on test failures and
scores, report the Lean 4 engine only, and do not open F\* failures as work.
It does not decide the general F\* direction, which the owner left open on
2026-10-21 ("I don't need to decide now").

### LWS: Touchstone is the conformance target (owner, 2026-10-21)

> "ok work with touchstone to make our stuff State of the Art compliant!!!"

Touchstone (https://github.com/ebremer/touchstone, the LWS conformance
harness of another implementer, 221 tests, results for six servers at
https://ebremer.com/lws/conformance) is the external measure for LWS. Our own
tests (`tests/lws/*.mjs`, the `#guard`s) check our reading of the draft;
Touchstone checks it against another reading. Target: `tools/lws-touchstone.sh`
exits 0 in both configurations (open and authorization on), with 0 failed and
no test inapplicable for a feature we could implement, which is the level of
the best servers on that page (lws-drupal: 210 passed, 0 failed, 11
inapplicable). A test is called defective only with the spec text quoted, and
then it is reported to the Touchstone author, not worked around. First run,
2026-10-21: 0 tests ran (https://github.com/danbri/factoidal/issues/911).
Features to add: https://github.com/danbri/factoidal/issues/890 (notifications),
https://github.com/danbri/factoidal/issues/912 (type index and search),
https://github.com/danbri/factoidal/issues/913 (access grants),
https://github.com/danbri/factoidal/issues/914 (moving resources).

### LWS extras: Merkle, encryption at rest, confidential computing, search results (owner, 2026-10-21)

> "1. After, yes. As an optional, probably default off until we settle on
> stronger motivating usecase but good to have the fundamentals there and I
> believe we have Merkel in the codebase somewhere already.
> 2. Yes env var please. Again off by default but good to show we can.
> 3. Research note for now.
> Also what do we think a Content-Locatioon results resource looks like? Can
> we draft an anticipatory impl flagged as likely unstable?"

- Merkle trees (https://github.com/danbri/factoidal/issues/919): after
  access grants (https://github.com/danbri/factoidal/issues/913) land. An
  option, off by default. Build on `L4Factoidal/Storage/BlockMerkle.lean`
  (hash as a parameter; pure Lean SHA-256 as the specification instance).
- Encryption at rest of the LWS storage: key from an environment variable,
  off by default. Crypto per `skills/crypto-policy`.
- Confidential computing (SEV-SNP, TDX, Nitro, SGX, TPM measured boot): a
  research note only.
- Type search `Content-Location` results resource: an anticipatory
  implementation, off by default and marked unstable in code, docs and the
  storage description, because lws10-index defines no such resource and only
  says a server that exposes one "MUST subject it to the same authorization
  filtering on every access and MUST prevent its reuse across clients".

### Order after LWS storage stage 2 (owner, 2026-10-22)

> "Approved. Do auth server (as a component other servers might use too).
> Then LWS client. Then also the XMPP-related work items in the conversation
> quoted here"

1. Finish LWS storage on disk stage 2 (https://github.com/danbri/factoidal/issues/918).
2. An authorization server as a component that other servers can use, not
   only `lws-serve` (https://github.com/danbri/factoidal/issues/916).
3. An LWS client (https://github.com/danbri/factoidal/issues/917).
4. The three items from the glitchcan-minigam foafos report of 2026-10-21
   (`magpie/miniapps/lws/README.md` there): CORS headers in the LWS HTTP
   binding; XMPP over WebSocket (RFC 7395) in `l4xmpp-serve`; LWS
   notifications sent as XMPP messages. Issues are linked from
   https://github.com/danbri/factoidal/issues/901.

### Loops yes, new partial def no (owner, 2026-10-23)

> "Re partial def, I don't want more non-proofy code but loops aren't
> inherently evil. Sometimes we have chosen a looping construct to avoid eg a
> fueled deep recursion blowing up memory use unpredictably, rather than a
> fixed usage making streaming processors more feasible."

- No new `partial def` (`tools/lean-hygiene-audit.py`; the baseline does not
  go up).
- An `IO` loop that ends on an outside event (a worker's stop flag, a value
  from another thread, a socket) is a `repeat`/`while` loop in `do` notation,
  with a comment that names the event. `repeat` runs on Lean core's own loop,
  so it proves nothing about termination; it keeps the code out of new opaque
  declarations and in one frame.
- Work over input-proportional data is a loop or a tail call with fixed
  memory, total, with theorems where a property is claimed.
- Cost of not having this rule: on 2026-10-23 two such loops in
  `Harness/WorkerPool.lean` were written as `partial def`, the count went to
  165 against the baseline 163, and "Verify Lean 4 corpus" on main was red for
  about a day (https://github.com/danbri/factoidal/issues/965).

### Ill-formed BCP 47 language tags (owner, 2026-10-24)

Owner, 2026-10-24, verbatim answer "B." to the question on
https://github.com/danbri/factoidal/issues/1004 and
https://github.com/danbri/factoidal/issues/1005, where option (b) was: "Jena
style: the readers keep the triple and warn, and the writers write the tag
unchanged."

Specifications: RDF 1.2 Concepts §3.4 says a language tag MUST be well-formed
per BCP 47 §2.2.9; RDF 1.2 N-Triples §6.4 leaves "Error detection, reporting,
and recovery" to implementors; the RDF-star WG thread of July 2025
(https://lists.w3.org/Archives/Public/public-rdf-star-wg/2025Jul/0005.html)
lists the options; Apache Jena keeps the triple and warns.

Rule, in Lean, on every surface:

- A reader that meets a language tag which its concrete-syntax grammar reads
  (LANGTAG [144s] of RDF 1.1, LANG_DIR of RDF 1.2) and which is not
  well-formed per BCP 47 §2.2.9 keeps the triple and gives a warning that names
  the tag and its position (class `ill-formed-language-tag`): the `warnings`
  member of the `datasetOpen`, `parseToDatasetJson` and `parseDocument`
  envelopes, `Dataset.warnings` in npm, standard error in the CLI.
- Every writer writes the tag unchanged (after its case normalisation) and
  does not refuse it.
- One predicate: `RDF.isWellFormedLangTag` (`RDF/LangTag.lean`). The positions
  come from `Syntax/LangTagWarnings.lean`.
- Exception, decided by the W3C suite: the RDF 1.2 N-Triples negative syntax
  test `ntriples-langdir-bad-4` (`"Hello"@cantbethislong`) requires the RDF 1.2
  readers to refuse a subtag of more than 8 characters. That case stays a
  syntax error in RDF 1.2 mode, and an RDF 1.2 writer refuses to write it
  (`langTagWritable`), because no RDF 1.2 reader reads the text. In RDF 1.1
  mode it is read with a warning and written.

## Reading owner steers: prioritization is not prohibition

The owner usually steers this project from a phone, between other
obligations, against a fast stream of agent output — with no good
tooling for bookmarking, tagging, or cross-referencing what scrolled
past. Instructions given under those conditions are prioritizations
made on a partial view, and the owner has said plainly that they are
sometimes inaccurate or flawed — most likely for protocol-shaped work,
which is harder to test casually than format-shaped work (a format
test is files-in/triples-out; a protocol test needs simulated or live
endpoints, so a quick scope judgment about it is easier to get wrong).

Rules that follow:

1. **"X deprioritized" is an ordering decision, never a scope
   prohibition.** Do not let a steer calcify into "out of scope by
   owner directive" through document inheritance. (It happened: a
   2026-07-11 "protocols deprioritized" was inherited three documents
   deep into "owner-excluded" labels on specific CSVW tests. The owner
   never made that call; see the 2026-07-15 correction in the CSVW
   triage ledger. The owner's own account of what that steer meant,
   given 2026-08-22, verbatim: "Protocols were not deprioritised but
   we needed basic sparql first - and early f\* was glacially slow at
   points where io bridged the non f\* universe." Note that BOTH the
   original label and the earlier gloss recorded here were wrong: it
   was a sequencing constraint plus a performance problem at the I/O
   boundary, not a judgement about protocol work.)
2. **Quote steers with date and original wording** when writing them
   into ledgers or design docs. Paraphrase drifts; drift compounds.
3. **Never invent a rationale and attribute it to the owner.** State
   who decided a thing, or label it a Claude-inferred default. In this
   repo `git blame` CANNOT settle provenance — every commit carries
   the owner's git identity by iron rule #13 — so provenance survives
   only if the prose carries it. (It happened: 2026-08-22, a
   Claude-authored skill bullet said the Lean tree's plain evaluator
   split was "absolute — never port performance machinery here",
   placed under an "owner priority" heading it was never given. It
   hardened into "must stay that way" in a design doc, then into a
   chat claim that the owner considered indexed joins destructive.
   Owner: "BS, I never said this." Cost: a real design question —
   should the Lean tree get indexed joins and a refinement proof? —
   was recorded as closed for a day. Corrected in
   `skills/factoidal-lean-basics` with a standing provenance note.)
4. **Load-bearing implications get surfaced, not inferred.** Before
   recording "owner excluded N tests" or dropping a suite from a
   goal, put the implication back to the owner as one short question.
   A sentence of friction now beats a fabricated decision that future
   sessions will read as settled.
5. **Write for phone-triage.** The owner's instruction quality is a
   function of our output quality: lead with the result or the
   decision needed, keep it short, no pseudo-private jargon (glossary
   rule), scores always labelled. A wall of codenames upstream
   becomes a flawed instruction downstream.
6. **Use a small, stable emoji palette as visual anchors** (owner
   request, 2026-07-15): colored emoji render as scannable texture on
   a phone, letting the owner navigate giant scrolling blocks at
   flick-speed. Fixed meanings, applied sparingly (one marker per
   line that matters, never decoration): ✅ landed/gates green ·
   ❌ regression/gate failure · 🔴 blocker needing action ·
   🟡 in flight · 📊 score line · 🧭 decision needed from owner ·
   ⚠️ risk/caveat · 🧹 cleanup/hygiene. Owner messages may use emoji
   as markers too — treat them as tagging, not tone. Full register
   rules: `skills/markdown-style/SKILL.md`.
7. **Work tracking lives in GitHub issues, not session state** (owner
   correction, 2026-08-11, verbatim: "This is unacceptably shit for
   ios app users - you spew thousands of lines of blabber at us with
   no tooling to organize it. Use github properly."). Session-local
   task lists are invisible on mobile and die with the container.
   Every workstream gets a real issue; the one-page index is
   **#404 Active work tracker** (update it at every harvest cycle —
   staleness there is a bug). Status reports LINK issues instead of
   restating their content.
8. **Old steers decay — re-verify before acting on one.** "Protocols
   deprioritized" predated SPARQL Protocol reaching 56 pass, 0 fail
   (34 protocol + 19 graph-store + 3 service-description, both trees);
   citing a steer against a tree that has since moved is acting on
   stale data.

## Agent Work Strategy

Use subagents aggressively for parallelism — independent work
(verification + compile + test) runs concurrently. Top-level Claude
coordinates and never blocks the main loop. Use `run_in_background:
true` for long-running ops.

**Per anti-pattern #23/#24:** scope every subagent to a single
commit-sized goal; ship code sketches, not "figure it out". When
dispatching against the COTTAS backend or evaluator, the agent prompt
MUST forbid additions to `experimental_ocaml_glue/` other than the
rule-#11 acceptable forms.

**Check `df -h /` before dispatching a worktree agent, cap concurrency at
three, and remove each worktree in the same turn you land its commit.**
Each worktree holds a 1.5-2.8 GB copy of the Lean build cache; seven live
at once filled the disk on 2026-09-03 and every tool call failed, including
the one that would have diagnosed it. Before deleting a worktree, check it
for unlanded commits (`git -C <path> log --oneline origin/main..HEAD`)
— that sweep rescued a 301-line design document written twelve days
earlier. Full recovery procedure: hazard #36 in
`skills/workflow-gotchas-debugging`.

**Worktree agents start with `tools/ensure-test-env.sh`** — worktrees
inherit zero test submodules, and absent fixtures produce lying 0/0
scores and phantom ENOENT failures (hazard #15,
`skills/workflow-gotchas-debugging`). Never trust a suite number from
a checkout where that script exits 1. **Exception:** when a worktree's
`third_party/testing` entries are symlinks into the main checkout, never
run that script or any `git submodule` command there: git follows the
symlink and rewrites the main checkout's submodule `core.worktree`
(2026-10-12: 21 submodules pointed at a removed worktree and every `git
status` in the main checkout failed; hazard #40).

## Anti-patterns (one-line summaries)

Full text + war stories: [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md).
Commit messages and inline comments reference these by number ("per
rule #17").

1. Writing OCaml parsers instead of F\* parsers.
2. Dismissing rdf-mt tests as "needing an inference engine."
3. Reporting misleading test scores (unlabelled numerators/denominators).
4. Building parallel OCaml toolkits instead of extending the F\* spec.
5. Symlinks/hacks for version mismatches (esp. z3) — fix the env.
6. Promoted-type blindness: handle `ER_Num`/`ER_Dec`/`ER_Dbl`/`ER_Bool`
   alongside `ER_Term(T_Literal _)` everywhere.
7. Parser/evaluator AST mismatch: grep `SPARQL11_Parser.ml` first.
8. `parse_to_scaled` before `parse_double_to_scaled` — try double-aware
   first; E-notation gets mis-parsed otherwise.
9. Recursive string-function base cases kill metadata — handle the
   single-element case explicitly to preserve lang tags + datatypes.
10. OCaml `Str` regex operates on bytes, not codepoints; unmatched
    group back-refs raise `Not_found`.
11. `build-ocaml.sh compile` does NOT apply `ocaml-patches.sh`. Use
    `extract` after a fresh extraction.
12. `(*` inside F\* comments silently swallows the file. Use `//`.
13. Never edit extracted `.ml` files in `ocaml-output/` directly —
    fix the `.fst` or add a patch.
14. Never `|| true` to swallow shell failures — capture exit code
    explicitly (`CMD_RC=0; cmd || CMD_RC=$?`).
15. Never sneak semantic logic into `ocaml-patches.sh` or `w3c_runner.ml`.
16. Never truncate command output with `tail -N` / `head -N` — use `tee`.
17. Never let ad-hoc parse / SPARQL runs hang — cap at 10 min
    (`timeout 600`). Kill and shrink input on cap trips.
18. Dump in-flight plan to `.claude-worklog.md` at checkpoints.
19. Long-running processes log to `.claude-runs/` with hard wall-clock cap.
20. Never burn clock foregrounding long parses/full builds — background them.
21. Never stall on parallel work in flight; pick the next item.
22. Subagent stall is a checkpoint, not a loss — check `git status`/log.
23. One subagent = one commit = one deliverable.
24. Subagent prompts ship code sketches + file:line + signatures.
25. Never write cryptic score strings. "972/59" without labels is
    banned — write "972 pass, 59 fail (out of 1031)".
26. **Three language bans** in prose AND code comments (owner
    correction, 2026-08-23). Rewrite table:
    `skills/markdown-style/SKILL.md`.
    (a) **Sycophantic adjectives**: `honest`, `genuine`, `important`,
    `critical`, `big-picture`, `headline`, `key insight`, `key
    finding`.
    (b) **Aphorisms** — a short balanced sentence written to sound
    like a maxim. Banned examples from this repo: "A vacuous truth is
    not an entailment", "a cap that hides which test it costs is a
    silent cap", "Withholding is sound; manufacturing emptiness is
    not". Write the rule as a rule. Also banned: "not X, but Y"
    contrast pairs, and telling the reader which of your points
    matters ("worth noting", "the point is", "this matters
    because"). These are named patterns in the published catalogue of
    Claude writing tics.
    (c) **Metaphor in any statement of a SEMANTIC RULE.** "A spelling
    difference is not a value difference" was metaphor AND factually
    wrong — `"colour"` and `"color"` ARE different `xsd:string`
    values. The actual rule is about whether a datatype's LEXICAL
    MAPPING is injective. Use the specification's own term from
    [`docs/w3c-glossary.md`](docs/w3c-glossary.md); if the term is
    missing, add it there first.
27. Landing an old-branch agent commit onto a much newer tip silently
    drops `build-ocaml.sh` module-list entries (auto-merge) and
    consumer `.ml` changes — the build exits 0 but the feature isn't
    built. Verify the module list + force ancestor-safe consumer files;
    prefer a dedicated landing agent. Full text: hazard #11 in
    `skills/workflow-gotchas-debugging/SKILL.md`.
28. An audit that finds nothing is evidence about the AUDIT's reach
    before it is evidence about the code. State the method next to the
    result, and pick one that can see the failure you are looking for.
    (2026-08-23: a squashed-module-name audit of the Lean port gap
    reported "no other false negative"; four modules, 1,298 F* lines,
    were already covered — the method cannot see a consolidation or a
    substantive rename, and its silence about exactly those was read as
    coverage. The reported figure was 120 of 220; the real one was 125.
    Full text: hazard #28 in `skills/workflow-gotchas-debugging`.)
29. A theorem whose hypothesis restates its conclusion type-checks
    and proves nothing. Before claiming a theorem discharges an
    obligation, unfold the conclusion and check no premise contains it;
    a proof body of `exact h` is the tell. Delete such a theorem, never
    weaken it -- it makes commit messages and design docs claim the
    obligation is met. (2026-08-23, `Cottas.PresenceWriter`: a
    `buildPresence_correct` under the heading "the producer-side
    obligation, closed" took `BuiltCorrectly` with re-indexed bounds as
    a hypothesis. Full text: hazard #29 in
    `skills/workflow-gotchas-debugging`.)
30. A measurement tool must derive its inputs from the repository on
    every run. A cached file list reports the cache, not the tree, and
    says nothing about being old. (2026-08-23:
    `tools/lean-port-gap.py` read its Lean module list from the
    session scratchpad and reported a module as not covered minutes
    after its Lean file landed; the same cache would have made the
    tool crash on a fresh container. Fail loudly on an empty walk, and
    write generated reports to a temp path. Full text: hazard #30 in
    `skills/workflow-gotchas-debugging`.)
31. Coverage is an explicit decision, never a name resemblance. A
    matching last name component is a suggestion to audit, not a
    result; and a lookup table whose misses fall through to a
    heuristic cannot report its own breakage. (2026-08-23: adding
    `HDT/Store.lean` made `SPARQL11.Store` — 1,452 lines, unported —
    vanish from the Lean port gap's not-covered list, because both end
    in `Store`. The audit found seven such false positives and two
    aliases pointing at a Lean module that does not exist, hidden
    because the leaf rule matched something else. The reported count
    had been over by five. A count that moves without a cause is a bug
    report: chase it before writing the number down. Full text: hazard
    #31 in `skills/workflow-gotchas-debugging`.)
32. A hub post's live cells run against the js/npm bundle, not the
    native binary. A docs landing that adds cells calling a new F\*
    feature is NOT docs-only — rebuild the bundle (the js build
    incrementally SKIPS npm-entry; force it) and gate on `node --test
    tests/hub/postNN` AND the headless-browser sweep
    `tests/web-demos/hub_browser_all.sh` — the node harness binds
    `fn` to the node package, so it cannot see browser-surface gaps
    (missing hub.njk wrappers, Turtle-vs-N-Quads calling-convention
    mismatches: two owner-reported live breakages, 2026-08-07/08).
    Full text: hazards #12 and #22 in the same skill.
33. A `.ml` under `ocaml-output/` captured between `fstar.exe --codegen
    OCaml` and `./ocaml-patches.sh` compiles and is missing every glue
    realisation. Three Lean-titled commits swept such files into git on
    2026-08-24; the shipping linux binary was rebuilt from them and lost
    the COTTAS on-disk companion chain, the SPARQL extension-function
    registry, the Parquet footer glue and the SHACL `sh:sparql` marker
    for two days, with `git status` clean and every suite green. Commit
    `.ml` only after a COMPLETE `extract`, stage it by explicit path,
    and never let a commit carry files its subject does not name. Full
    text: hazard #34 in `skills/workflow-gotchas-debugging`.
34. A routing change that moves query shapes from the reference evaluator
    to a backend runner must be gated by a query only the reference
    semantics decide (EXISTS/NOT EXISTS, MINUS, OPTIONAL+FILTER,
    sub-SELECT) on the path that changed. (2026-09-02: the WASM/CLI query
    op was routed through the physical-plan runners without
    `env.dataset`; FILTER NOT EXISTS answered zero rows for a day while
    `lake build`, native-smoke, the hub suite and CI were all green, none
    of which ran an EXISTS query through that path. Found by
    `tools/w3c-persisted-census.sh`. Full text: hazard #35 in
    `skills/workflow-gotchas-debugging`.)
    The same applies to a feature added to the reference evaluator: every
    path that bypasses it must refuse the feature until it implements it.
    (2026-10-12: `text:query` landed on `claude/core-split` while the SBM11
    id path, the qlvr reader, the planner and the COUNT fast path landed on
    `main`; three of the four would have answered `text:query` patterns
    from stored triples with all gates green. Hazard #41.)
35. A theorem file that no build root imports is never type-checked, and a
    record that calls its theorems proved has no build behind it. Run
    `python3 tools/lean-unbuilt-modules.py --gate` (exit 0) before writing
    "proved". (2026-10-13: `Storage.Sbm11.ParallelScanTheorems`, reported
    as proved for issue 799 stage 1, had never been built; two OWL and RDF
    theorem files from 2026-09-07 were in the same state. All three build;
    they are now imported from a root.)
36. A purity lint that scans only the server hosts says nothing about the
    rest of the JS. RDF, SPARQL, datatype and IRI decisions in any npm or
    hub `.mjs`/`.js` file are iron-rule-7 violations. (2026-10-21 audit:
    `tools/host-purity-lint.sh` passed 10 of 10 while `rdfjs.mjs` carried
    its own N-Quads parser and writer, `fn.js` its own isomorphism check,
    and `bin/ext.mjs` chose `xsd:integer` for `1e21`; each gave a wrong
    answer. Owner, verbatim: "The ja leak fix is p0 yop urgent. Get that
    shit into lean 4 and proven asap. We can't undermine whole project this
    way!" Fix and lint extension:
    https://github.com/danbri/factoidal/issues/894.)

37. A set-valued specification object (an RDF graph or dataset) needs an
    enforced invariant at every producer and a test of observable
    cardinality (count, `COUNT(*)`, serializer line count); membership
    theorems give the same answer for `[t]` and `[t, t]`. (2026-09-08: a
    Codex brief said to keep "the graph list's order and duplicate triples"
    on parse; npm review finding R02, 2026-10-21, found count 2 and
    `COUNT(*)` 2 for `<urn:s> <urn:p> "x", "x" .`; published in npm 0.11.0
    and 0.12.0. Fixed by PR 26 and the `CertifiedDataset` handle store.
    Full text: hazard #46 in `skills/workflow-gotchas-debugging`.)

## Skills (operational details, on-demand)

Skill files live at `skills/<name>/SKILL.md` in the
[agentskills.io](https://agentskills.io) format — a vendor-neutral
spec adopted by ~30 agent products (Claude Code, Cursor, Codex,
Gemini CLI, Goose, Copilot, OpenHands, Roo, …). `skills/` is the
single source of truth; `.claude/skills/` contains per-skill symlinks
so Claude Code discovers them natively (frontmatter preloaded at
session start). Other harnesses: point your skill discovery at
`skills/` or add your own symlink dir — do not fork the content.
Read the linked file the first time you touch that topic in a
session.

- [`session-economy`](skills/session-economy/SKILL.md) — fresh-session
  bootstrap contract, token prudence, subagent model/effort selection,
  and how to pick the next piece of work. **Read first in autonomous
  sessions.**
- [`session-cost-accounting`](skills/session-cost-accounting/SKILL.md)
  — measure a session's real cost incl. subagent children
  (`tools/session-cost.sh`, agentsview recipe + traps).
- [`skos-integrity`](skills/skos-integrity/SKILL.md) — check a SKOS
  vocabulary against the SKOS Reference integrity conditions using
  the SHACL validator, SPARQL property paths, and OWL-RL closure;
  ships shapes, queries, SKOS OWL axioms, and a valid/broken sample
  vocabulary pair.
- [`session-restore`](skills/session-restore/SKILL.md) — restore a
  fresh/recycled VM to working state in minutes: cache-branch
  inventory (toolchain-cache, checked-cache), what the hook restores
  automatically, skill-symlink regeneration, and the never-again
  rules from the 90-minutes-of-compiles incident.
- [`factoidal-lean-basics`](skills/factoidal-lean-basics/SKILL.md)
  — the Lean 4 side (formal/lean4/, L4Factoidal,
  https://github.com/danbri/factoidal/issues/466): toolchain,
  build/demo/test, the no-sorry/no-axiom policy + audit, the purity
  doctrine replacing `assume val`, lean-lsp-mcp + lemma search, and
  the paid-for Lean pitfalls.
- [`blockengine`](skills/blockengine/SKILL.md) — design, implement, and
  review the Lean-generated RDF block engine: landed Cottas/SPARQL reuse,
  term and graph IDs, block denotation, physical plans, PushIR, bitmap
  indexes, PostgreSQL/TiKV adapters, and refinement gates.
- [`lws-solid`](skills/lws-solid/SKILL.md) — the W3C Linked Web Storage
  Protocol 1.0 core and the Solid Protocol (server and client): the Lean
  modules, the wasm ABI the Node hosts call, `factoidal lws-serve` /
  `solid-serve` / `solid-client`, the three host test suites, the three
  community interop scripts with what makes each exit 2, the conformance
  ledger, and the authentication boundary.
- [`shardborough-storage`](skills/shardborough-storage/SKILL.md) — operate
  the Lean persisted store: pack → activate → query the collection root →
  update through the delta log → compact, the `l4block-*` CLI table, what a
  generation directory contains, the corpus ladder and census tools, and
  the rules for changing a format (encoder admission equals decoder
  admission; byte change means new wire version).
- [`qlvr`](skills/qlvr/SKILL.md) — Factoidal/qlvr, a QLever index read
  from Lean: rebuild the pinned QLever instance and its query oracle, the
  byte-level format record, the Python format probe, and the loop rule for
  the decoders (https://github.com/danbri/factoidal/issues/778).
- [`capability-planner`](skills/capability-planner/SKILL.md) — the
  capability-aware, cost-based planner across SPARQL, SQL, REST, MCP,
  WebMCP, files, LLMs and Shardborough: the six questions, capabilities with
  access patterns and costs, structural and runtime planners, probing as
  costed work, Lean semantics (https://github.com/danbri/factoidal/issues/800).
- [`lean-proof`](third_party/skills/leanprover-skills/lean-proof/SKILL.md)
  and [`lean-mwe`](third_party/skills/leanprover-skills/lean-mwe/SKILL.md)
  — vendored unmodified from leanprover/skills (Apache-2.0, provenance in
  `third_party/skills/leanprover-skills/PROVENANCE.md`): the upstream
  one-tactic-at-a-time proof method and the minimal-example recipe for
  upstream bug reports. Local policy on top: nothing with `sorry` is
  committed.
- [`lean-review`](third_party/skills/lean-agent-skills/lean-review/SKILL.md)
  — vendored unmodified from gotrevor/lean-agent-skills (Apache-2.0): the
  diff-scoped trust and hygiene check registry for Lean changes
  (`maxHeartbeats`, `native_decide`, `axiom`, `sorry`, `unsafe`/`partial`,
  silenced linters), `#print axioms` as the authoritative check.
- [`lean4-proof-patterns`](skills/lean4-proof-patterns/SKILL.md) — prove
  properties of fuel-bounded, match-heavy definitions without Mathlib:
  the theorem shape for fuel independence, nested-match splitting, the
  large-Nat-literal trap that hangs `split`/`generalize`, `rename_i`
  order, `omega` after `List.length_cons`, timed per-theorem compiles to
  bisect a hang. Read when a Lean proof stalls or before dispatching a
  proof subagent.
- [`lean4-performance`](skills/lean4-performance/SKILL.md) — improve
  performance-sensitive Lean 4 code while preserving total semantics,
  observable order, and the executable proof boundaries: parsers, block
  ingestion, data structures, recursion, hot paths. Measure first; not for
  unmeasured micro-optimisation.
- [`lean4-wasm-export`](skills/lean4-wasm-export/SKILL.md) — compile the
  Lean 4 port to ONE wasm module for browser + Node + Deno (#466): the
  toolchain route and the three rejected, rebuilding Lean's runtime and
  core library for wasm32 GMP-free, the C ABI + memory ownership, how to
  add an export, and the traps (silent `leanir`, the `-DNDEBUG` abort).
- [`npm-release`](skills/npm-release/SKILL.md) — release
  `@factoidal/core`: which artifacts `Wasm/build-wasm.sh` and
  `build-ocaml.sh npm` produce, the four byte-identical wasm mirrors,
  the three `version.json` files and their writers, trusted publishing
  through the OIDC workflow (the owner's npm account is
  security-key-only, so token and one-time-password publishing always
  fail), the gates with their current numbers, and the packaging traps.
- [`crypto-policy`](skills/crypto-policy/SKILL.md) — never roll our
  own crypto; HACL\* adoption order for the hash/signature
  `assume val`s (#63), and the wasm compatibility gate.
- [`node-crypto-haclstar-vc-wasm-build`](skills/node-crypto-haclstar-vc-wasm-build/SKILL.md)
  — the concrete build: VC Data-Integrity crypto running off-native
  (Node + browser) via HACL\*'s official wasm (#286). Three realisation
  paths, the throw-on-uninit safety contract, build-ocaml.sh wiring, npm
  ABI, provenance/licence, and the land-from-off-main recipe.
- [`fstar-env`](skills/fstar-env/SKILL.md) — F\* / opam / z3
  setup and repair.
- [`build-and-test`](skills/build-and-test/SKILL.md) — build,
  extract, compile, run W3C tests.
- [`fast-verify-extract`](skills/fast-verify-extract/SKILL.md) — make
  the verify→extract→compile→test loop fast: .checked cache
  semantics, targeted single-module rebuilds, safe parallelism
  (make -j, never concurrent ad-hoc fstar.exe), CI cache proposals.
  The loop speed is what keeps us validation-guided instead of
  flying dark.
- [`test-suites`](skills/test-suites/SKILL.md) — every suite (W3C,
  OWL, RDFC-1.0, parity, Jena probes, external-suite policy) and the
  score-reporting discipline. **Testing drives everything.**
- [`perf-benchmarking`](skills/perf-benchmarking/SKILL.md) — timing
  harnesses, baselines, observability, profiling policy. Speed is
  measured separately from correctness, always.
- [`proof-factory`](skills/proof-factory/SKILL.md) — run the
  rule-by-rule F\* proof program at scale: the closure-identity law,
  the guard-depth ≤3 rule, brief anatomy for first-attempt passes,
  spray-and-verify economics per model tier, the harvest pattern for
  stalled proof agents, and the findings discipline (six ledger
  drifts + one engine completeness gap caught by proofs). Read
  before dispatching any proof subagent or proving engine rules
  against the W3C tables.
- [`measuring-inference`](skills/measuring-inference/SKILL.md) — how to
  measure what a reasoning engine actually does: which phase the time is
  in, why synthetic shapes lie about real vocabularies, negative tests
  that pass by deriving nothing, theorems with unsatisfiable
  hypotheses, and silent caps. Read **before** optimising any closure
  or entailment path, or before a plausible mechanism becomes a work
  order. Every rule carries the wrong claim that paid for it.
- [`site-and-dashboard`](skills/site-and-dashboard/SKILL.md) — the
  11ty site, test-results dashboard, demos, Fly.io endpoint, and the
  registry of progress tables + who updates each.
- [`disk-storage-format`](skills/disk-storage-format/SKILL.md) — how
  data lands on disk: the COTTAS/Parquet base + its 10 sidecars, the
  durable-UPDATE delta log (framing, crash-safety, epoch guard), the
  symlink-current compaction layout, and the exact import/query/
  compact/serve CLI invocations.
- [`fstar-module-style`](skills/fstar-module-style/SKILL.md) — module
  organization (semantic core vs pragmatics), stratification roadmap,
  .fsti policy, syntax traps in full, KaRaMeL-compatible style.
- [`ocaml-boundary`](skills/ocaml-boundary/SKILL.md) — rule #11 in
  depth: the glue taxonomy, patch lifecycle, companion-file byte
  rules, vendoring policy, extraction-target status.
- [`github-and-prs`](skills/github-and-prs/SKILL.md) — gh CLI
  with `--repo danbri/factoidal`, branch + PR conventions.
- [`github-coauthor-policy`](skills/github-coauthor-policy/SKILL.md)
  — no Claude attribution in commit messages (iron rule #13).
- [`repo-tour`](skills/repo-tour/SKILL.md) — directory layout,
  "where does X live?".
- [`using-factoidal`](skills/using-factoidal/SKILL.md) — drive
  Factoidal from any external LLM/agent system: both engine flavours
  (F\* CLI + npm, Lean wasm + native), the capability matrix with
  measured scores, runnable examples per spec area, and the l4_call
  dispatch ABI. Self-contained for readers outside this repo.
- [`fstar-mcp`](skills/fstar-mcp/SKILL.md) — F\* MCP server for
  interactive proof / typecheck queries (replaces batch `fstar.exe`
  reruns for diagnostic work).
- [`mcp-setup-readme`](skills/mcp-setup-readme/SKILL.md) — how the
  repo's MCP wiring is configured (`.mcp.json`, bootstrap script,
  daemon manager, port, transport). Read when adding/debugging the
  MCP plumbing rather than using F* MCP for proofs.
- [`markdown-style`](skills/markdown-style/SKILL.md) — clickable-link
  rules, the no-sycophantic-adjectives rewrite list, and the
  aphorism/metaphor ban with its rewrite table (anti-pattern #26).
- [`choosing-models`](skills/choosing-models/SKILL.md) — model/effort
  selection per subagent. Core rule: for all coding tasks, judge an
  appropriate lower-power model and run it in a subagent; Fable-class
  sessions orchestrate, gate, and design — they don't type the code.
- [`subagent-prompting`](skills/subagent-prompting/SKILL.md) —
  worktree path discipline + post-condition checks.
- [`workflow-gotchas-debugging`](skills/workflow-gotchas-debugging/SKILL.md)
  — diagnostic playbook for the dev-loop hazards we've actually hit.
- [`autonomous-time-discipline`](skills/autonomous-time-discipline/SKILL.md)
  — wall-clock + Monitor + lock-cleanup pattern for long autonomous
  sessions. Read when kicking long background builds, when "the
  job has been silent for a while," or before a multi-hour solo run.
- [`danbri-function-precrime-checkers`](skills/danbri-function-precrime-checkers/SKILL.md)
  — catch a function's resource-scaling defects (stack, memory, time that
  grow with input) by measurement during the test run, before they crash on
  a large input in production: the static IR scan, the small-budget canary
  run, and the n/2n/4n scaling assertion. Read before adding a parser,
  decoder, serialiser or fold, or a stress test.
- [`counting-coverage`](skills/counting-coverage/SKILL.md) — how to
  count what a port or migration has covered without the number lying.
  **Read before writing any coverage number, before adding an alias-table
  entry, and whenever a count moves and you cannot name the commit that
  moved it.** Core rule: a name is a hint, coverage is a decision.
- [`issue-management`](skills/issue-management/SKILL.md) — **read
  before any status report, plan, or issue reference.** GitHub issues
  are the only durable work record; every issue reference is a full
  clickable URL (bare `#NNN` is dead text in rendered markdown);
  session-local labels and code names are forbidden in anything a
  reader sees later; technical Simple English with a banned-filler
  table ("load-bearing", "smoke test", ...).
- [`issue-hygiene`](skills/issue-hygiene/SKILL.md) — keep GitHub
  issues + checklists in sync as PRs land.
- [`jsoo-debug-bundle`](skills/jsoo-debug-bundle/SKILL.md) — build a
  source-mapped JS bundle so browser-only crashes show real OCaml
  stacks.
- [`jsonld-context-cache`](skills/jsonld-context-cache/SKILL.md) —
  resolve remote JSON-LD `@context` IRIs offline from
  `third_party/jsonld-context-cache/` (URL-keyed, content-addressed,
  versioned). Read when a JSON-LD/DID/VC document will not parse
  because its context is remote, when adding or refreshing a cached
  context, or when wiring a documentLoader (#275). Carries the
  per-URL licence rule and why an empty-context fallback is banned.

## Expanded docs (full reference)

- [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md)
  — full anti-pattern text with war stories.
- [`docs/claude-rules/performance.md`](docs/claude-rules/performance.md)
  — perf status + history (current measured throughput; the 2026-04
  slow-Turtle root causes).
- [`docs/claude-rules/current-state.md`](docs/claude-rules/current-state.md)
  — F\* inventory, `assume val` table, W3C scores.
- [`docs/theorem-registry.md`](docs/theorem-registry.md) — the G1
  reviewable-core registry: every W3C rule id → spec predicate →
  engine function → proof status, plus the trust-surface enumeration.
  UPDATE WITH EVERY PROOF LANDING (hand-curated until generated).
- [`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](docs/designissues/2026-09-03-rdf-parsing-strategy.md)
  — how each RDF syntax is parsed: the reference parser, the streaming
  execution for the shard packer, the theorems between them, costs paid
  and open. Update it when a parser layer changes.
- [`docs/designissues/2026-09-05-shard-pack-profile-and-memory.md`](docs/designissues/2026-09-05-shard-pack-profile-and-memory.md)
  — where the shard packer's time goes and how its peak memory grows: the
  `/usr/bin/sample` method with its blind spots, the two accidental costs it
  found and their repairs, the measured curve (time AND memory both linear;
  memory is 3.76 bytes of peak footprint per source byte, which puts YAGO at
  about 534 GB), what stays live to the end of a pack, and why a memory
  curve fitted without a point an order of magnitude above the others read
  as sublinear and was wrong.
- [`docs/designissues/2026-09-16-npm-usability-and-bundle-profiles.md`](docs/designissues/2026-09-16-npm-usability-and-bundle-profiles.md)
  — the six npm usability defects reported by the DAW session and what
  landed for each: strict parsing with positions, dataset handles, prefixes
  both ways, the bundler entry, the lite bundle profile; the measured sizes
  and query costs; the answer to the bundle-granularity question; the Valis
  licence record. Update it when a profile or the parse contract changes.
- [`docs/w3c-glossary.md`](docs/w3c-glossary.md) — the cross-spec
  architectural vocabulary: lexical space / value space / lexical
  mapping, entailment and models, open-world and no-unique-name,
  OWL 2 class expressions, tableau terms, conformance-testing terms,
  and the local vocabulary that is NOT specification language. Use
  these terms; do not paraphrase them.
- [`docs/code-name-glossary.md`](docs/code-name-glossary.md) — Yod6 /
  Tet3 / Lamed3 / etc. decoder. **No new short-codes** — use
  descriptive names per the recovery plan.
- [`docs/claude-rules/README.md`](docs/claude-rules/README.md) — index
  and the relationship between this file and the expanded docs.
- [`docs/fable-notes-xyz-20260706.md`](docs/fable-notes-xyz-20260706.md)
  — strategy + workflow handoff notes from the 2026-07-06 sessions
  (state of the project, impact ranking, landing discipline, gaps,
  sequencing). Read early in a fresh autonomous session.

## Recovery + planning docs

- [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](docs/designissues/2026-05-07-query-planning-fstar-recovery.md)
  — F\*-only recovery roadmap; replaces the OCaml shadow logic
  (Yod6/Tet3/Lamed3/Mem5/Pe5/Bet7/Tav5/Heth3) with proper F\*
  modules.
- [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](docs/designissues/2026-05-07-io-verification-and-third-party.md)
  — hash-based round-trip verification pattern; HACL\* / EverParse
  vendoring policy; corrected boundary-audit taxonomy.
- [`docs/designissues/2026-05-07-c-build-and-roaring-plan.md`](docs/designissues/2026-05-07-c-build-and-roaring-plan.md)
  — KaRaMeL C-build pilot + Roaring continuation tracks.
