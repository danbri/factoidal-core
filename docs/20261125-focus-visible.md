# Distinguish visible focus from focus itself

The full Linux WPT run [45647054675](https://github.com/danbri/factoidal-builds/actions/runs/45647054675)
at `056c528ccb5844b01628e0cd667520535dee16cc` records failures around pointer focus
and the `focusVisible` option. The current matcher uses the same state for both
`:focus` and `:focus-visible`.

Keep a separate indicator state. A pointer can focus a generic element without
an indicator. Text controls and editing hosts show one when focused. Keyboard
interaction reveals it. Scripted focus inherits the previous focus indication
unless the target takes text input or the caller passes `focusVisible`. The
Lean selector reads both bits and applies its existing shadow-host behavior.

Lean 4.33.1 elaborated the selector module with retained dependencies. Six
source-extracted event checks pass on the local host model. The scoped WPT run
will check native events, computed styles, and adjacent focus behavior. Default
outline painting is separate.

[Selectors Level 4 focus-visible](https://www.w3.org/TR/selectors-4/#the-focus-visible-pseudo).
