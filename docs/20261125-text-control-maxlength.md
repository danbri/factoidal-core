# Limit edits in text controls using maxlength

The emoji paste test uses `document.execCommand("insertHTML")` on a focused text input. The prelude converts it to a plain-text insertion and uses the same Lean edit operation as a native text-control key. That operation now reads the live `maxlength` attribute of the target and counts UTF-16 code units. An insertion keeps the unselected part of the value and stops before a character that would cross the remaining capacity. A length limit also applies to inserted line breaks in a textarea. Script assignments and the existing `setRangeText` path use their usual operations.

Chrome checks covered the family emoji at 10 units, a surrogate pair at one unit, replacement between retained text, an already overlong script value, and a selection replaced with identical text. They also checked the actual `input` event data and the lack of an event when a full field rejects an insertion at a collapsed caret. The length-limited operation returns the inserted data's UTF-16 start for the prelude to form that event payload.

`textEditWithLimit_ok` proves the result's selection stays in bounds when the original selection is in bounds. The guards exercise the UTF-16 cutoff and replacement behavior. The existing newline sanitation and the text-selection type coverage are separate compatibility questions.

[HTML maxlength](https://html.spec.whatwg.org/multipage/form-control-infrastructure.html#attr-fe-maxlength) · [Pinned emoji WPT](https://github.com/web-platform-tests/wpt/blob/94e2796a2aa59a232e4e43e8a218ae967e9fac77/html/semantics/forms/constraints/input-maxlength-emoji.html)
