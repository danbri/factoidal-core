# Text control input and change events

The [full Linux WPT](https://github.com/danbri/factoidal-builds/actions/runs/45639976657)
passed two of eleven assertions in `input-change-event-properties.html` at
`056c528ccb5844b01628e0cd667520535dee16cc`. Six supported text controls reported
a non-composed `input` event. The keyboard edit path did not commit the changed
value when the control lost focus.

Compose the existing `InputEvent` and record whether the user edited the focused
control. On focus loss, compare against the value on entry and dispatch a trusted,
bubbling `change` event before blur when the value still differs. The change
event remains within the control's tree. Reuse the input value getters and the
existing focus transition. Only the keyboard host edit path marks a user edit.

The five local source-extracted checks cover ordering, event flags, reverting the
value, script-only assignments, focus changes from an input listener, and removing
a focused control. They use a mock host. The selected browser WPT checks are the
end-to-end verification. Email, number, and select editing use other paths.

[HTML input events](https://html.spec.whatwg.org/multipage/input.html#common-input-element-events)
and [focus update steps](https://html.spec.whatwg.org/multipage/interaction.html#focus-update-steps).
