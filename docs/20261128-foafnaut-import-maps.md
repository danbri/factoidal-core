# Foafnaut document import maps

The [Diddums studio](https://danbri.github.io/diddums/) uses an inline import map. Its bare `@factoidal/core` import selects a vendored browser module. Other entries attach a build query to relative imports. The previous Foafnaut resolver handled only URLs and refused the bare import before the studio could initialise.

The built-in engine implements [HTML import-map resolution](https://html.spec.whatwg.org/multipage/webappapis.html#import-maps). It normalises keys and addresses against the document base, then applies the most specific matching scope and key. A blocked address or a package suffix that escapes its target is refused. Late declarations keep old rules and discard additions that could change an earlier resolution. Mapped URLs use the existing module fetch, CORS and MIME checks. Integrity metadata uses the existing response-byte check. Inline maps pass the existing CSP filter.

The loader admits up to 16 inline maps, each up to 64 KiB and 512 JSON parser fuel steps. Late registration stops after 2,048 prior graph nodes or requests. A document with no module scripts follows the existing no-load path. External import maps, worker maps and maps registered by DOM mutation are later work. Diddums playback also depends on AudioWorklet, tracked in the [Web Audio plan](https://github.com/danbri/factoidal-core/issues/1169).

Theorems cover the empty-map path, exact null refusal, the parse byte cap and rejection of a response that fails its integrity check. Closed tests cover Diddums-style bare and versioned imports, package prefix precedence, scopes, escape paths, malformed input, duplicate declarations and CSP.
