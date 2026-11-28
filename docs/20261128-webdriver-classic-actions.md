# WebDriver classic input actions

Tracking [Foafnaut developer tools](https://github.com/danbri/factoidal-core/issues/372).

## Measured starting point

Foafnaut 0.38.1 on Linux x86-64 and Apple Silicon, BubblePopJS, engine commit `bd0d78dd12ff` and WPT commit `67903cd58bad`: 889 of 10,573 WebDriver subtests passed. The whole WebDriver group includes BiDi. The classic-only run of `b45f02cbd` had 889 passes, 1,982 failures and 1,033 errors against 3,904 Chrome subtests, across all 254 wdspec files. Its `perform_actions` directory had 747 errors and zero passes. [Linux release run](https://github.com/danbri/factoidal-builds/actions/runs/46145420734) · [macOS release run](https://github.com/danbri/factoidal-builds/actions/runs/46142310707) · [Classic branch run](https://github.com/danbri/factoidal-builds/actions/runs/45934172247)

## Change

Both classic `POST /actions` and `DELETE /actions` used to reach the unsupported-command response. They now share the same Lean driver as `test_driver`. The HTTP route checks the input with the existing parser and resolves element origins using the current document's reference prefix. Release Actions runs the existing cancellation path and can clear an empty context. The result uses the existing classic error encoding.

`WebDriver.Page.classicActions_release` proves that Release Actions supplies no input from its request body. `WebDriver.Page.classicActions_perform_refused` proves that a parser refusal stays an error at the routing boundary. Existing `WebDriver.Page.refNode_other` covers earlier document prefixes. These proofs do not establish WPT conformance, timing of input dispatch, browser-window behaviour or the full browsing-context lifetime.

The classic runner still uses one active loaded document. A separate BiDi transport is needed before its pure engine commands can be measured by BiDi wdspec.
