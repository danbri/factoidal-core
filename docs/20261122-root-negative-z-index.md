# Viewport-positioned paint order

The layout pass for pending viewport-positioned boxes previously received just the pending boxes. It returned the negative and nonnegative groups together, which were appended after the normal document. The pass now receives the accumulated layout so it can compose negative boxes below normal content and nonnegative boxes above it. The canvas background is painted before the composed document.

In the separated-border-model-004b comparison, both test images retained all 9,900 red pixels where the reference is green. The table border adjustment exposed another 1,800 green pixels below the red box. The paint-order defect has a separate minimal comparison with a canvas background, a negative positioned box, in-flow content and positive positioned content.

[CSS 2.2 Appendix E](https://www.w3.org/TR/CSS22/zindex.html)
