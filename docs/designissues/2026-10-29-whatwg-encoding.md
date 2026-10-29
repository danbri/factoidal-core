# WHATWG Encoding Standard in Lean (2026-10-29)

Milestone 2 of https://github.com/danbri/factoidal/issues/1167 (modular wasm and a
browser proof of concept with Lean at its heart). Status: complete for decoding
and encoding; the browser-only parts of the WPT suite are listed in
https://github.com/danbri/factoidal/issues/1184.

## Result

📊 `bash tests/whatwg-encoding/run.sh` (web-platform-tests `encoding/` at wpt
`ce5ca396`, Lean engine): 1,139,344 pass, 0 fail (out of 1,139,344); 1 excluded
(defective test data, https://github.com/danbri/factoidal/issues/1183). 139 test
files run, 19 not run (https://github.com/danbri/factoidal/issues/1184). The run
takes about 40 s.

Most of the count is the legacy multi-byte pages: one test per code point of
each index, for each label, for decoding (an iframe document in the encoding),
for `<a href>` query encoding and for GET form submission.

## Specification and data

- Encoding Standard, WHATWG Living Standard, whatwg/encoding commit `be17ac5c`
  (2026-10-19). Section names in the Lean comments are the names of that text.
- `encodings.json` and `indexes.json` of the same commit are vendored in
  `third_party/whatwg-encoding/` (provenance there). `tools/whatwg/gen-encoding-data.py`
  writes `formal/lean4/L4Factoidal/WHATWG/Encoding/Data.lean` (the `Encoding`
  type with 40 constructors, the 228 labels, the indexes as hexadecimal text);
  `--check` fails when the file is stale.

## Modules

| Module | Contents |
| --- | --- |
| `WHATWG/Encoding/Data.lean` | generated: encodings, labels, index text |
| `WHATWG/Encoding/Core.lean` | get an encoding, get an output encoding; every decoder and encoder as a handler; process a queue; the hooks of section 6 (UTF-8 decode and its variants, UTF-8 encode, decode, BOM sniff, encode, get an encoder, encode or fail); `TextDecoder`, `TextEncoder`, `TextDecoderStream` and `TextEncoderStream` state as values |
| `WHATWG/Encoding/Tests.lean` | build-time `#guard`s for statements the standard makes about its tables |
| `WHATWG/Encoding/Theorems.lean` | the UTF-8 encoder agrees with Lean core `String.utf8EncodeChar`; a character round-trips through the UTF-8 decoder handler |
| `WHATWG/URL/PercentEncode.lean` | URL Standard section 1.3: the percent-encode sets, percent-encode after encoding, percent-decode (the first part of milestone 3) |
| `Harness/WhatwgEncodingServe.lean` | `l4whatwg-encoding serve / selftest / bench` |

### How a decoder is written

The standard writes each decoder as a handler over an I/O queue: it reads one
byte (or end-of-queue), changes its state, and returns finished, items, error or
continue; some steps restore bytes to the front of the queue. In Lean each
decoder is one constructor of `Decoder` with that decoder's state variables, and
`Decoder.handle : Decoder → Option UInt8 → DStep` returns the next state, the
result and the bytes to restore. `none` is end-of-queue. The queue (`Queue`) is a
list of restored bytes followed by a byte array from a position. Encoders are the
same over code points (`Encoder.handle`, `CpQueue`).

`decodeLoop` and `encodeLoop` are "process a queue". They are tail calls with
fuel `8 × (queue length + 1) + 16`. A restore puts back only bytes already read,
and the decoder state changes so that the restored bytes are read in another
state; no byte is read more than four times. If the fuel ends the loop reports
`Outcome.fuel` and the hooks report an error. The self-test decodes 4,000,000
bytes that make the gb18030 decoder restore three bytes in every four, under a
1 MB stack.

### The API objects

`TextDecoder` holds every internal slot of section 7.1 (encoding, decoder
instance, I/O queue, ignore BOM, BOM seen, error mode, do not flush).
`TextDecoder.decode` follows section 7.2 step by step and returns the next
object state with the output or a TypeError. Streaming therefore needs no
replay: the test host keeps the Lean state in the server between calls.
`TextDecoderStream` uses the same record with "decode and enqueue a chunk" and
"flush and enqueue"; `TextEncoderStream` keeps its leading surrogate.

## The test host

`tests/whatwg-encoding/run.mjs` runs the WPT files in Node `vm` realms. It gives
them a testharness.js-compatible API and Web IDL bindings for `TextDecoder`,
`TextEncoder` and the two stream classes (argument conversion, BufferSource
copying, a `TransformStream` around the Lean stream algorithms). Each binding
call is one request line to `l4whatwg-encoding serve` through two FIFOs, so the
JavaScript calls stay synchronous. For the legacy pages it gives an iframe
document (decoded by Lean with the charset of its `.headers` file), `<a href>`
(the query is percent-encoded after encoding by Lean with the document's
encoding and the special-query set) and GET form submission (the
application/x-www-form-urlencoded set with space as `+`, in Lean), and
`XMLHttpRequest` for `data:` URLs (percent-decode and the final encoding in Lean).

Two steps are in JavaScript and are reported as such: reading the `<meta
charset>` of a test page and the `<span>` elements of an iframe document, both
with regular expressions. They move to Lean with the HTML tokenizer and tree
builder (milestone 5); https://github.com/danbri/factoidal/issues/1184.

## Findings

- WPT "fatal stream: utf-8" (`textdecoder-mistakes.any.js`) expects `''` from
  `decode()` after a fatal streaming error on `FD EF`. By section 7.2 the byte
  `EF` stays in the I/O queue and the next `decode()` throws. The same file's
  EUC-JP test relies on the queue keeping its bytes. Excluded as defective test
  data: https://github.com/danbri/factoidal/issues/1183.
- `encodeInto.any.js` constructs `Float16Array`; Node 22 needs
  `--js-float16array`, which `run.sh` passes.

## Speed

`lake exe l4whatwg-encoding bench`, 8 MB generated inputs, native, 2026-10-29:

| Input | Lean decoder | Reference on the same input |
| --- | --- | --- |
| UTF-8 ASCII | 602 ms (13 MB/s) | |
| UTF-8 3-byte | 449 ms (17 MB/s) | Lean core `String.fromUTF8?` 13 ms; Node 22 `TextDecoder` 44 ms |
| windows-1252 | 627 ms (12 MB/s) | |
| Shift_JIS 2-byte | 496 ms (16 MB/s) | Node 22 `TextDecoder` 38 ms |
| gb18030 4-byte | 879 ms (9 MB/s) | |

The handler loop allocates a step record and a list per byte. Fast paths, each
with a theorem or a differential run against the handler loop:
https://github.com/danbri/factoidal/issues/1185.

## Relation to the existing code

`XML/Encoding.lean` (XML 1.0 Appendix F) decodes UTF-8 with Lean core
`String.fromUTF8?` and implements UTF-16, ISO-8859-1 and US-ASCII itself. The
theorems of `WHATWG/Encoding/Theorems.lean` connect the WHATWG UTF-8 encoder to
Lean core `String.utf8EncodeChar`, which `String.toUTF8` uses. A later step can
let the XML decoder take its legacy encodings from this module (XML 1.0 leaves
the set of encodings open; the WHATWG labels are a superset of what it
implements now).
