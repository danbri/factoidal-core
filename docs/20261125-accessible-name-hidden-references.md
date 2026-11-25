# CSS-hidden content in accessible names

The accessible name calculation uses the same visibility rules for the computed label
query and for names and descriptions in the laid-out accessibility tree. A visible
`aria-labelledby` or `aria-describedby` target contributes visible content. A target
that is itself hidden can contribute its hidden descendants. Display and ARIA hiding
on ancestors count when deciding whether a target is hidden. CSS visibility comes
from the cascade. Clipping a label for visual presentation does not by itself hide
its text from this calculation.

The Linux WPT baseline at engine commit `66d81dd54e1a4758135208d00fc358fa37d26b11` and
WPT commit `056c528ccb5844b01628e0cd667520535dee16cc` had 22 passing and 5 failing
subtests in `accname/name/comp_labelledby_hidden_nodes.html`. The five failures
included text hidden by CSS `display: none`, `visibility: hidden` or
`visibility: collapse` inside a visible reference.

A local Lean check elaborated the two accessibility modules, ran their embedded
checks, and confirmed all 27 expected names from the pinned WPT HTML using only
the fixture's inline CSS facts as inputs.

The Linux branch check with BubblePopJS built engine commit
`f4ddf680e41423b902ed82e3225d8b5a2ede4260` and ran all 23 selected files at WPT
commit `056c528ccb5844b01628e0cd667520535dee16cc`. It passed 446 of 520 Chrome
subtests, up from 440, with no files regressing. Hidden references went from
22 to 27 of 27. The display-contents case with a child that does not render
raised that file from 9 to 10 of 13. The HTML-AAM hidden-name check stayed at
5 of 5. The branch result covers the selected tests and the engine's WebDriver
label query. Platform screen-reader behavior is still to be measured.

- [Linux AccName branch check](https://github.com/danbri/factoidal-builds/actions/runs/45653158672)
- [AccName 1.2, Hidden Not Referenced](https://www.w3.org/TR/accname-1.2/#comp_hidden_not_referenced)
- [Linux WPT baseline](https://github.com/danbri/factoidal-builds/actions/runs/45639976657)
- [Accessibility plan](https://github.com/danbri/factoidal-core/issues/581)
