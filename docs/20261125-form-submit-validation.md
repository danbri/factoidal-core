# Form submission arguments and validation

The full Linux BubblePopJS run
[45639976657](https://github.com/danbri/factoidal-builds/actions/runs/45639976657)
showed five failures in `form-requestsubmit.html` at WPT
`056c528ccb5844b01628e0cd667520535dee16cc`. The form prelude dispatched
submission for any argument and skipped the existing constraint checker.

Check the submitter's type and form owner before submission. Use the native
type and owner queries. Reuse the existing constraint checker for the
submission event path and guard against synchronous re-entry from an
`invalid` or `submit` event. Honor `novalidate` and `formnovalidate`.
Keep navigation planning in `HTML.FormSubmission`.

The
[HTML submission algorithm](https://html.spec.whatwg.org/multipage/form-control-infrastructure.html#form-submission-algorithm)
also defines interactive presentation for invalid controls. This change
blocks submission and dispatches `invalid` events using the current
validity checks. The browser's validation UI and CSS validity selectors
need separate checks. The scoped WPT run must establish the browser result.
