# FOAFNaut current-main refresh

The native graphics branch retains the live presentation admission changes from
`0367e7cc`, and now merges core main `48b8a34a`. The only conflict in the prior
HTML merge was the worknote index; both HTML and graphics records were retained.
The subsequent current-main merge was automatic. Upstream HTML corpus bytes
were preserved, including intentional whitespace and an author-file underline
which Git's whitespace checker reports as conflict-like text.

Validation after the merge: `bash labs/demos/foafnaut/test.sh --skip-build` passed
64 Deno tests and 12 C coordinate checks, with all specified entrypoints and
tests typechecked. `shasum -a 256 -c labs/demos/foafnaut/.build/source-SHA256SUMS`
confirmed every engine source and core dependency still matches the existing
warm build. Fixture integrity verified 75 pinned files and the complete
38-case SVG slice; all six runner tests passed. These are CPU/ABI/runner tests,
not desktop presentation or official visual matches. No new package build,
release or build dispatch occurred.

The [SVG secure-static roadmap](designissues/2026-10-30-svg2-static-roadmap.md)
records the unchanged 38-case denominator, first-error distribution, independent
image-oracle requirements and candidate implementation slices. The current
record remains zero official visual passes; artifact acceptance is not a pass.
