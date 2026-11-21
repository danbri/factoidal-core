# Image responses with HTTP error status

The HTML image algorithm says to ignore the HTTP status when deciding whether the response body is a valid image. The native image path already follows that rule: `Net.Xhr.imageRaw` extracts natural dimensions from the response body and preserves the status. The QuickJS image loader then accidentally discarded those dimensions unless the status was 2xx.

The loader now consumes the dimensions supplied by `imageRaw` for any non-null response. A focused source-extracted regression models a 404 response whose body has already decoded to `19 11`; it checks the image reaches complete state, reports those dimensions, enters the document availability list and fires `load`.

Evidence: `node --check tools/wasmvm/quickjs/prelude.js`; `node --test tools/wasmvm/quickjs/image_size_tracking_test.mjs` (21 passed); `git diff --check`. These checks exercise the JavaScript loader with a mock host response. They do not prove the Lean network path or replace a browser WPT result. The exact-source WPT rerun remains pending.
