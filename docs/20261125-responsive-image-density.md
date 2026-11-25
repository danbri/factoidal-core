# Keep the selected image density through the document request

`HTML.ImageSource.selected` chooses the source URL and density together. The document request now retains both and uses the existing generation check before storing natural dimensions. Changing a descriptor can therefore change the reported dimensions even when the URL stays the same. `currentSrc` keeps its original URL-only response.

Lean divides the resource dimensions by the selected rational density and converts the result to whole CSS pixels. In Chrome, a 101×51 image is 50×25 at 2x, 202×102 at 0.5x, and 0×0 at 1000x. A 0x or extremely small positive density caps both axes at 33,554,431px. The implementation uses that finite cap for the DOM getters. A successful resource remains decodable when its corrected size rounds to zero.

The Lean theorems establish the cap for every input and the unit-density result. Guards and a mocked bridge exercise the wire shape, fractional and extreme densities, same-URL reselection, and stale completion. This change covers the DOM sizes. The native rendering path still needs its own CSS intrinsic sizing correction for responsive sources.

[HTML image density](https://html.spec.whatwg.org/multipage/images.html#density-corrected-natural-width-and-height) · [Issue #1091](https://github.com/danbri/factoidal-core/issues/1091)
