# SVG references across HTML SVG roots

`href-use-element.html` is an original pinned upstream test. A hidden SVG root
contains a red rectangle and an orange circle. A second SVG root uses href for
the rectangle and xlink:href for the circle. The browser paints the rectangle;
the old HTML adapter lost 10000 red pixels because it indexed IDs per SVG root.

The Lean HTML frontend converts its entire original DOM to one namespace tree.
It preserves every child position, including text/comments, and supplies the
selected SVG root's path in that tree. It builds `NativeSVG.ReferenceContext`
once per render. The context retains the source DOM, retrieval URL, effective
initial base, original-order reference index, and cached ID/style results.
Equality witnesses bind those caches to that source. The reconstruction theorem
covers every admitted context, including cached unsupported-style errors.

`parseRootInContext` selects the actual source root in Lean. No independent
root argument can disagree with the index. A closed path theorem connects
successful selection to the exact requested path. The reader uses absolute
source paths for cycle checks. Duplicate IDs still select the first original
document element; active source identity does not conflate duplicate strings.
Original parent xml:base values stay with targets during cloning. The effective
base is separate from retrieval identity for same-document URL checks.

The optional pure Lean root-attribute normalizer lets the HTML frontend remove
properties it has already computed. It can replace only the selected root's
attribute list. The original element name, children, index entries and source
path remain intact. The root's base is calculated from original attributes
before normalization. Referenced targets keep original attributes and styles.
External HTML CSS targeting SVG remains explicitly unsupported in the caller;
SVG stylesheets use the shared original document. The HTML frontend owns HTML
base-element processing and must supply its effective base or refuse that case.

Standalone `parseRoot` keeps the local document default. Its context is created
after zero-viewport suppression, so a disabled viewport does not divide by zero
or require hidden style interpretation. The existing 32-level index/path/instance
and whole-input bounds stay in force. External document fetching is unsupported.

Native tests cover hidden cross-root targets, href precedence, global first IDs,
text/comment indices, root-only normalization, original bases, explicit external
bases, cycles, sibling paint, SVG styles and paint-server refusal. They are
separate from the actual upstream HTML rendering measurement, which must run
through the Lean HTML conversion/caller and compiled engine. See the
[dated evidence record](../20261102-svg-standards-overnight.md).

The interpretation follows SVG2 [use](https://www.w3.org/TR/SVG2/struct.html#UseElement)
and [same-document references](https://www.w3.org/TR/SVG2/linking.html#processingIRI).
