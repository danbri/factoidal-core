---
name: code-zones
description: Tag new Foafnaut source files with a primary zone, regenerate the static dependency report, inspect module crossings and propose cross-zone theorems without a Lean build.
---

# Code zones

Read [the taxonomy and measured report](../../docs/zones.md) and
[the mapping](../../zones/zones.json). The map describes responsibility; it does not move files or
restrict which features may be implemented. The earlier directory-based measurement is in
[issue 452, part 2](https://github.com/danbri/factoidal-core/issues/452).

## Tag new code

The five inventory roots are `formal/lean4/L4Factoidal/`, `labs/demos/foafnaut/`, `docs/web/hub/`, `npm/`
and `tools/`. Every tracked or non-ignored untracked file in those roots gets exactly one primary rule,
including fixtures, docs and binaries. Git-ignored build products are not source inventory. Symlinks
are counted without following their targets. A sparse checkout with missing tracked files fails.

Choose the zone by responsibility. `WasmVM/Hosts` is Browser integration, CSS under `Rendering` is Style,
and graph storage is RDF. Host transport code is Browser even when it transports GPU or network commands.
Shared XPath functions and regex are XML, JSON-LD and CSVW are JSON. Consult the definitions for the rest.

Edit a rule's `paths` or add a named rule in `zones/zones.json`. Patterns use Python `fnmatchcase` on
repository-relative POSIX paths: `*` crosses `/`. A rule matches the union of its patterns minus its
`exclude` patterns. Rules have no priority: two matching rules are an error even if their zone is the
same. Narrow an existing rule with an exclusion when splitting it. Do not add a catch-all for unknown
core Lean subtrees. Add optional `secondary_tags` for shared foundations, hosts, tooling or proof files;
these tags do not change the primary zone or totals.

`unmapped_files` is the explicit list of outstanding mapping decisions; currently it is empty. The tool
also computes the actual list, reports undeclared or stale entries and fails `--check` for any unmapped
file. Listing a file there does not excuse it from the coverage test.

## Regenerate and check

From the repository root, with Python 3.10 or newer and Git:

```sh
python3 tools/zones_test.py
python3 tools/zones.py --check --markdown docs/zones.md --json /tmp/zones.json
```

This starts no Lean compiler, engine, WPT run or network request. Keep the full JSON as a run artifact;
the committed Markdown is the review snapshot. `docs/zones.md` is generated: edit curated definitions,
review notes, candidate statements and structural probes in `zones/zones.json`, then regenerate it.
Run the test and regenerate after the final source edit because the tool and its test count themselves.
A timestamp is not used; HEAD and content hashes identify the inputs, including working edits.

The tool exits 1 on failed `--check` inventory coverage, and 2 on invalid configuration or I/O errors.
`--strict` additionally fails on every proposed-policy leak; the existing tree has such crossings, so
this is a review mode, not the normal passing gate. An empty inventory or root is an error. The tool
reads the current Git index and non-ignored files on every run; do not substitute a saved file list.

## Read the report

- Edges point from importer to imported file. Counts are import sites, including tests, repeated imports
  and TS type-only imports. The JSON retains every source path, line, target, kind and policy decision.
- Sizes distinguish all files/text lines from source files/lines. Lines include comments and blanks;
  binary files and symlinks contribute zero lines. Tests, fixtures and general tooling stay in totals.
- `allowed_dependencies` records expected zone pairs. `interfaces` narrows selected pairs to source or
  target paths. A matching interface admits that crossing; a miss is `interface-review`. A pair with no
  interface or allowed entry is `unexpected`. Review the actual modules before changing policy. Do not
  allow every current edge merely to clear the report.
- A cycle is a strongly connected zone group. Reciprocal pairs are also listed. A zone cycle can arise
  even when the module graph is acyclic. Structural probes traverse actual file imports and show the
  shortest witness; `no-resolved-path` only describes the scanned graph. `empty-selection` is not a pass.
- The scanner handles Lean import lines after removing nested comments, strings and character literals;
  JS/TS static imports, re-exports, literal `import()` and literal `require()`. External, missing,
  generated, computed and outside-inventory imports remain in JSON diagnostics. Lean module roots are
  declared in `tools/zones.py`; standalone scripts without an import namespace need no invented name.
- JS scanning is lexical, not a full language parser. It does not resolve package exports, aliases,
  template substitutions, HTML inline scripts or evaluated strings. FFI, operation-number protocols,
  callback effects and host fetches do not become import edges. Review these separately for a boundary
  claim. The counts are not call frequencies, effect analysis, proof coverage or conformance scores.

## Turn a crossing into a theorem candidate

Name the source operation, target operation, adapter, observation and hypotheses. Put the short proposal
and module links in `candidate_theorems`, then follow the
[theorem-pipeline skill](../theorem-pipeline/SKILL.md). JSON-LD's loader parameter and GRDDL's retrieval
function need a policy-carrying adapter before an end-to-end Fetch claim can be proved. An empty direct
Network column does not prove that callbacks or host effects enforce network policy.
