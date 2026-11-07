# SVG images and text areas in the foafnaut Lean engine

Owner, 2026-11-07, verbatim: "let's get svg drawing basics nailed down".

This record says how `textArea` lowers to glyph paths, and how `image` goes from
bytes to the GPU. Source: `labs/demos/foafnaut/SVGForgiving.lean`,
`labs/demos/foafnaut/SVG.lean`, `labs/demos/foafnaut/ImagePNG.lean`,
`labs/demos/foafnaut/ImageJPEG.lean`, `labs/demos/foafnaut/ImageData.lean`,
`formal/lean4/L4Factoidal/Rendering/Scene.lean`. Tests:
`labs/demos/foafnaut/SVGForgivingTests.lean`, `labs/demos/foafnaut/ImageTests.lean`,
`labs/demos/foafnaut/SVGImageTests.lean`, `labs/demos/foafnaut/svg_test.ts`. Paint
table: `docs/designissues/2026-11-07-svg-gradients.md`.

## textArea

The forgiving pass lowers `textArea` as it lowers `text`, so the strict reader gets
paths. `areaCells` applies white space handling over all runs. `breakLines` makes
lines as ranges of cells: a `tbreak` ends a line, a word that does not fit goes to
the next line, and a word wider than the area breaks between characters. Each line
has at least one character, so an area narrower than one glyph still ends.

- `width` or `height` `auto` is infinite; zero disables rendering.
- A line that does not fit completely is not rendered (§10.11.7).
- `text-align` shifts a line. `display-align` shifts all lines; with `height="auto"`
  it has no effect.
- `xml:space="preserve"`: a space at a break goes to the next line.

Decisions from §10.11.4 and §10.11.7:

- `line-increment="auto"` is 1.1 times the largest font size on the line, which
  the specification recommends. A number is in user units; the largest value on the
  line wins. An empty line has the value of its `tbreak`.
- Rule 9 places the baseline with the font of the line at a size equal to the line
  increment: `top + increment*ascent/unitsPerEm`.

The W3C reference PNGs do not follow these two. In `text-area-201-t.svg`, font size
24, the lines are 24 apart, and the first baseline is at 24 below the top of the area
(rule 9 with an ascent of 800 gives 21.1). In `text-area-206-t.svg` each baseline is
on the bottom edge of its line. The file `images/SVGFreeSans.svg` says `ascent="800"`.
The references also draw text that inherits `font-size="18"` at about 12. This engine
does not copy these values. A trial with spacing 1.0 and the baseline at the bottom
of the line moved no text-area file out of the MISMATCH band (15 of 15 stayed; the
mean different share went from 0.193 to 0.143), so the choice costs no band.

Rectangles of `stroke-width="0.25"` around the areas of these tests draw nothing here:
https://github.com/danbri/factoidal/issues/1253.

Breaks are at spaces, which §10.11.7 allows as a simple implementation. UAX 14, soft
hyphens and bidirectional text: https://github.com/danbri/factoidal/issues/1259.

## image

1. `imageKey` gives the key of a reference: a `data:` URI as it stands, another
   reference resolved against the base in force, with `xml:base`.
2. `imageStore` decodes each key once, before the strict reader runs. The forgiving
   pass runs that reader many times, so the reader only looks up the store.
3. The reader makes a `rect` with `Paint.image`. `imagePlacement` gives the rectangle
   and the map from user space to pixels (`preserveAspectRatio`, default
   `xMidYMid meet`). With `meet` the rectangle is the image; with `slice` it is the
   viewport, so the geometry clips the image and no clip record is needed.
4. `opacity` is the element's. `fill-opacity` is set to 1, because it is not a property
   of an image. Transforms and clips are those of any primitive.

So an image adds no record kind: `Primitive.rowCount_eq_storageRows`,
`Scene.data_size_eq_record_cursor` and `shaderRowAdvance_eq_rowCount` keep their
statements.

### Wire form

The fill row is `[cursor, opacity, 0, -2]`: a fourth float below -1 marks an image.
The header in the paint table is nine words: map x row and width, map y row and
height, then the word offset of the pixels from the start of the table. Pixels follow
all records: one word for each pixel, red in the low byte, opacity in the high byte,
not premultiplied. `unpack4x8unorm` reads a word.

`ImageRecord.id` identifies a bitmap in a document, so `Scene.paintTableTail` stores
its pixels once, however many primitives use it.

`ImageRecord.colorAt` is the reference; `imageSample` in the shader states the same
steps: map, bilinear on premultiplied pixels, edge pixels beyond the edge.
`Scene.checks` runs on this reference, so each GPU run compares its pixels with it.

### Limits

Image bytes are hostile input, and this is a new surface in the sense of
https://github.com/danbri/factoidal/issues/1120. Invariants, and the test of each
(`ImageTests.lean`):

| Limit | Value | Refusal names | Test |
|---|---|---|---|
| `maxImageBytes` | 8,388,608 | the number | decoders check it first |
| `maxImagePixels` | 1,048,576 | the number | PNG and JPEG with huge declared size |
| `maxDocumentPixels` | 1,048,576 | the number | `Store.addBytes` guards |
| `maxJpegCoefficients` | 6,291,456 | the number | worst padded case, 1 by 65535 |
| `maxJpegScans` | 64 | the number | a scan visits each block once |
| `maxPaintTableWords` | 1,048,576 | the number | `Scene.json` |

- The size is checked from the header before any allocation.
- Inflate gets the exact size that IHDR gives (`inflateAt ... limit`), and stops there.
  So a small stream can not expand past the image.
- CRC of each PNG chunk and the Adler-32 are checked. An unknown critical chunk is a
  refusal.
- All loops are `for` loops over checked sizes or the input. No recursion grows with
  the input. No C codec and no host decoder: decoding is browser logic.
- Every prefix of two JPEG files, and a sample of one-byte changes, gives a refusal or
  an image of the right size.

The largest test image is 840 by 525 pixels (441,000 words), and the largest total
in one W3C file is 168,921 words, so the table limit stays. The largest JPEG store
is 6,291,456 coefficients at 8 bytes.

A document may hold 1,048,576 pixels in all. A later image past that is a refusal for
that image; the forgiving pass removes it and logs it.

### PNG and JPEG

PNG: all colour types and depths, all filters, Adam7, PLTE, tRNS and gAMA. A sample of
16 bits keeps its high byte. gAMA applies sample^(1/(gamma*2.2)), as the W3C files
`gam030.png` to `gam200.png` need; an sRGB chunk, or a gamma within 2 percent of
1/2.2, changes nothing. iCCP is ignored.

JPEG: baseline, extended sequential and progressive Huffman, 8-bit, one or three
components, any sampling to 4 by 4, restart intervals, Adobe APP14. Chroma upsampling
is repetition. An ICC profile is ignored. The inverse DCT is in binary64.

### Bytes from the host

Bytes come from the same place as a stylesheet. In the browser, `inspect` adds
`images` (key and URL) to the document snapshot, `document-client.mjs` fetches each
one through the resource broker, and `compile` gets `images` (key and base64). So the
broker's policy applies: HTTP and HTTPS only, no credentials, 1 MiB for each
resource, 4 MiB for each document. The host does not read the bytes.

The CLI reads files only with `--svg-resources ROOT`. A document under ROOT has a URL
under `http://svg-resources.invalid/`, so references resolve in Lean as for HTTP. Only
a key under that origin is read, and its real path must be under ROOT. So `file:`, the
network and a symbolic link out of ROOT are refused.

A reference with no bytes stays in the store as a refusal, `image resource not
supplied`.

An HTML document decodes its images for each render. A cache across frames is not
done yet.

## Open

- https://github.com/danbri/factoidal/issues/1258 (an `image` of an SVG document is
  refused)
- https://github.com/danbri/factoidal/issues/1259 (UAX 14, soft hyphens and
  bidirectional text in `textArea`)
- https://github.com/danbri/factoidal/issues/1253 (a stroke narrower than the sample
  grid draws nothing; the frames in the text-area tests)
