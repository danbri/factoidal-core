# Sequential keyboard focus within a page

The native X11 office-style test delivered Tab and left the address field, but page focus stayed on the previous state. The key event code had defaults for edits, Enter and caret movement. Tab had no default.

The Lean focus module now orders a document's focusable nodes by positive tabindex and then tree order. Tab advances and Shift+Tab reverses. Disabled controls, negative tabindex and inert subtrees are excluded. When a script focused a negative-tabindex element, traversal continues from its tree position. The event handler skips controls whose current CSS prevents display or visibility. It then uses the usual focus and blur events. A canceled keydown prevents the move.

Lean compiled the complete changed Focus module and its theorem that every returned node is eligible for sequential focus before CSS filtering. Eight guards exercise positive order, ties, direction, disabled and inert controls, invalid tabindex and navigation from negative tabindex. Native transport and paint verification remain pending.

The current implementation covers a document's own focus stops in BubblePopJS. Shadow scope ordering, transitions across frame boundaries, and movement to the browser chrome are still tracked in the issue.

[Browser issue](https://github.com/danbri/factoidal-core/issues/1108) · [HTML sequential focus navigation](https://html.spec.whatwg.org/multipage/interaction.html#sequential-focus-navigation)
