# Keep a drop-down's options in its own control

The former DOM option list included every option descendant. A selected
option inside another select, an option, a horizontal rule, a datalist or
a nested optgroup could replace the outer select's value. The renderer
had a separate list that missed options inside ordinary wrappers.

Use a bounded tree-order walk that prunes the excluded subtrees. Keep the
option's owner query in Lean and use it for the option's selectedness,
index and form on the script side. Reuse the shared selected options for
the text on the collapsed control. The FormData path already uses the same
selection. The navigation submission path now reads it too.

Two Lean statements state the scan step at an excluded subtree and at an
already nested optgroup. Executable fixtures cover the excluded descendants,
valid wrappers, fallback selectedness, and disabled groups. Check the
published WPT nesting fixture and adjacent selection, validation and form
submission before merging. Clearing an option through its selected setter
asks Lean whether the dropdown must select a fallback. Explicitly clearing
the select through selectedIndex or value still leaves an empty selection.
The arena retains its existing combined selectedness and dirtiness
representation. Check the displayed label and posted value on an
actual native browser page.

[HTML select list of options](https://html.spec.whatwg.org/multipage/form-elements.html#concept-select-option-list)
