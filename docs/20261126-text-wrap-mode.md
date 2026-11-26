# Apply CSS text-wrap-mode to line layout

Foafnaut accepted `text-wrap: nowrap` and `text-wrap-mode: nowrap`, but those declarations only affected balanced wrapping. Layout still broke text at ordinary soft wrap opportunities. Both forms now feed the same wrapping state as `white-space: nowrap`.

Cascade `white-space-collapse` and `text-wrap-mode` separately through the shared shorthand grammar. This lets author order and importance decide which declaration wins while preserving how spaces and segment breaks are handled. CSS-wide values copy the same wrapping state that layout uses.

On the pinned WPT fixture, the Lean renderer placed the text on six rows before the change and one after. The wrap control stayed at six rows, while legacy nowrap stayed at one. Lean guards cover the longhand, shorthand order, importance, custom property substitution and inherited modes. Native pixel comparison remains pending.

[CSS Text 4 wrap modes](https://drafts.csswg.org/css-text-4/#text-wrap-mode) · [Pinned WPT fixture](https://github.com/web-platform-tests/wpt/blob/94e2796a2aa59a232e4e43e8a218ae967e9fac77/css/css-text/white-space/text-wrap-nowrap-001.html)
