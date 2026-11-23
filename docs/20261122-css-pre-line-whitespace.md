# Collapsing whitespace while preserving segment breaks

CSS Text 3 defines pre-line as preserving source line feeds while collapsing
spaces and tabs and permitting soft wraps. Foafnaut previously treated
pre-line and white-space-collapse: preserve-breaks as fully preformatted.
Its line breaker then held every word, and multiple spaces stayed visible.

The computed style now carries the preserve-breaks choice through the
cascade independently of soft wrapping. Inline tokenization emits a forced
line break for a source line feed and uses the ordinary collapsing path for
other spaces. A cascade reset clears the preservation choice, and copying the
collapse longhand leaves the wrapping value alone. Single-line controls
continue to use their own whitespace policy.

Lean 4.33.1 verified the extracted cascade and tokenizer code with warnings
treated as errors. The token guard checks that two consecutive source line
feeds produce two forced breaks and that a collapsed space run has one
token. It also checks the source offsets of the remaining words. Full
native compilation and pinned CSS tests are tracked in the PR.


The fixed-pin native comparison gained 19 assertions without a loss across
143 CSS Text tests. The paired visual run gained two passes of six. The
exact extracted tokenizer and `textItems_preLine_blankLine` compiled in Lean
4.33.1 with warnings as errors. The lemma shows that collapsing a space
between two preserved source line feeds retains both forced breaks.
