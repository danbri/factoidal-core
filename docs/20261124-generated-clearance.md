# Preserve generated boxes during CSS selector pruning

The GOV.UK homepage floats its search column and uses a generated `::after` block to clear the row. The installed November 22 engine returned a 0 px row with a 91.6 px float. Adding an ordinary clearing block restored the row and moved the next section below it. A reduced fixture reproduced the failure with one clearing rule and one unrelated rule containing `:has()`.

`pruneHas` filters ordinary selectors. Its empty-list check formerly discarded any rule without ordinary selectors when the pass ran. Keep rules with a `::before`, `::after` or `::first-letter` selector even when the remaining ordinary list is empty. The early exit for pages without an ordinary `:has()` is unchanged.

The Lean theorem states that the pruning phase retains each pseudo-only rule unchanged under arbitrary surrounding rules. A Lean guard exercises a real parsed stylesheet with a generated rule and an unsatisfiable `:has()` rule. The native geometry probe compares the generated clearing box with an ordinary clearing block and a float without clearance.
