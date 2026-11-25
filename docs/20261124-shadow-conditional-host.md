# Conditional shadow host selectors in the MDN replay

The archived MDN CSS display reference shows its theme and language menus
over the article. Both menus are inside declarative shadow trees and use
the same rule to hide the named dropdown slot before hydration or focus.

```css
:host(:not([loaded], :focus-within)) slot[name=dropdown] {
  display: none;
}
```

The existing shadow cascade recognises simple host selectors and the DOM
selector matcher already handles attribute selectors, negation and focus
state. This change joins the two for descendant selectors that contain
a host compound. The full compound predicate retains its specificity.
The prefilter still controls bucket admission, and the existing scope
checks keep the rule inside its shadow tree.

The cascade tests cover the initial, loaded and focused states and a
slot outside the shadow tree. The replay still has separate colour
scheme, SVG mask and script latency differences to investigate.

Specification: [CSS Shadow Module Level 1](https://drafts.csswg.org/css-shadow-1/#host-selector).

The first exact native check reached the new cascade guard and showed
that matching alone was insufficient. The layout tree removed each slot
and spliced its assigned nodes directly into its parent. It now keeps the
slot as the parent and assigns `display: contents` through the user agent
sheet. This lets author `display` override it and lets assigned nodes
inherit from the slot, as CSS Shadow 1 §4.1 requires.
