# Paint edited text input values

The captured FrogFind homepage has a plain GET form. In the released Linux browser, typing produced form-state commands and Enter and the submit button sent the exact expected query. The text field stayed blank on both document engines.

The command replay already restores the live input value in the document arena. Read it through the existing DOM Forms getter when laying out text inputs. Keep password masking and placeholder behavior, including after the user clears the field. Button labels still use their content attribute.

The Lean guards cover the command-to-layout path for typing, clearing and resetting an input, plus masking an edited password. The paired X11 replay checks typing pixels and GET serialization independently.

[Baseline receipts](https://github.com/danbri/factoidal-builds/actions/runs/45534656207) · [Everyday-page acceptance](https://github.com/danbri/factoidal-core/issues/712)
