# 2026-11-25 CSS cascade property lookup

The native MDN turn profile showed CSS declaration dispatch beneath
`computedFrom`. The predicate scans five static property lists for every
ordinary name that reaches `applyOrKeep`. Its compiled implementation uses
one shared hash set, with the same three prefix rules.

Lean checks `appliedName_eq_fast` for every string. The compiler uses that
equality to replace calls to the original predicate. Its source definition
remains available to existing cascade proofs.

A standalone Lean 4.33.1 executable used the production property lists and
9,061 names extracted from archived GOV.UK and W3C Flexbox stylesheets.
Each fresh process tested 800 repetitions. The four arms in list/hash/hash/list
order returned 6,069,600 hits each and took 0.93/0.17/0.18/0.90 seconds of user
CPU. The sample uses CSS source declarations before selector matching. A
separate browser replay measures the effect on page load time and output.
