# Liberation Mono in the default address bar

The desktop browser already supplies Liberation Mono to the Lean renderer
for monospace text on web pages. Prepare the printable ASCII outlines once
when that face is held and use them to paint the default address field.
The character cells keep their existing width, so click and selection
geometry uses the same columns. Non-ASCII characters and an absent face
use the existing glyph fallback.

The full, layered and chrome-only requests all pass the held face to the
shell. The native host still moves font bytes and draws the scene.
Lean checks fallback equivalence and page clipping for any address face.
