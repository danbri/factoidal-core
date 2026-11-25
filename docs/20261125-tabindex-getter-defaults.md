# Default tabIndex for anchors and disclosure summaries

The full Linux run [45639976657](https://github.com/danbri/factoidal-builds/actions/runs/45639976657)
passed 116 of 120 assertions in `tabindex-getter.html` at WPT
`056c528ccb5844b01628e0cd667520535dee16cc`. The remaining cases cover an HTML anchor
without a link, an SVG anchor without a link, an embed, and the second summary inside
a details element.

Follow the [HTML getter rules](https://html.spec.whatwg.org/multipage/interaction.html#dom-tabindex).
The reflected default and eligibility for sequential focus are separate decisions in HTML.
Use the namespace-aware element classifier and the existing first-summary rule.
Actual focus navigation still uses the existing eligibility checks.

Lean 4.33.1 elaborated the changed module, its existing MathML theorem and guards, and a
local fixture of all four failing default values. The fixture used retained dependency
artifacts and a freshly compiled Autofill module. The exact browser test runs in Linux CI.
