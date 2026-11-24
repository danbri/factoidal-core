# Early selector rejection inside grouped rules

The rule index narrows the candidate rule list before matching an element.
A rule with multiple selectors can enter through one matching class or tag,
while the other selectors would still reach the full matcher. Check the
existing rightmost-compound bucket before calling that matcher for each
selector in a group. A rule with one selector keeps the existing direct path.

The proof equates the full resulting Match, including the original rule and
the surviving selectors in order. It uses the existing theorem that a matched
selector is admitted by its bucket. That preserves selector specificity and
visited-selector handling. Focused WPT and paired archived render timings
verify the integration and measure the cost.
