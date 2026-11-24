# Disclosure markers for details and summary

The archived W3C Flexbox specification lost its disclosure triangle beside
“More details about this document”. The renderer produced markers only for
elements named li, and treated both disclosure counter styles as discs.

Keep the list-item flag in the computed display value and use the ordinary
list formatting path for markers. The user agent rules give the first summary
an inside disclosure marker and switch it when details is open. Author
display or list style can replace the default. The marker direction follows
writing mode and text direction.

The layout guards cover open and closed summaries and overriding the
marker. Lean also checks that list-style-type none suppresses the marker
for every writing mode.

Specification: [HTML rendering of details and summary](https://html.spec.whatwg.org/multipage/rendering.html#the-details-and-summary-elements).
