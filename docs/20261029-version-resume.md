# Version configuration continuation — 2026-10-29

Resumed WIP `4a8e6a242`. Wrote the done/remaining audit in `REPORT.md`
before continuing implementation. Retained both sides of the Regex4 conflict.

Added older grammar, function arity/type, typed binding, numeric comparison,
duration/QName comparison, map-key, and serialization branches. Repaired the
merged proof statements. Build scope is only `l4qt4`; source changes remain
uncommitted as the brief requires.

Design: [language version settings](designissues/2026-10-29-language-version-settings.md).
Final measurements and target outcomes: `../REPORT.md`.

The continuation also reuses the shared ordered regex matcher for legacy
zero-width anchors, and distinguishes XPath extension parsing from XQuery before
rejecting the namespace axis. Family comparison found that parser regression;
the final evidence must include the repaired source.

Schema import-interface checks now catch retained schema element/attribute types;
unknown named atomic schema types and namespace-sensitive copying remain gaps.
The no-options XML parsing bridge is now explicitly a v40 theorem because older
modes default to the existing external-resource resolver. This does not add HTTP
access. The proof and final-score limits are recorded in the root report.

Final verification: `lake build l4qt4` succeeded (357 jobs). All 150 target sets
and nine families were measured in both languages on the final binary. 709 of
749 targets have explicit passing traces; 40 remain with individual causes in
REPORT.md. None of the 18 family/mode totals loses passes against the stored
baseline. The two baseline stress timeouts remain counted as failures. A separate
map diagnostic run records target same-key-006 passing while counting skipped
non-target stress cases as failures. Final logs and outcomes are in
`docs/20261029-version-after/`. No commit or push was performed.
