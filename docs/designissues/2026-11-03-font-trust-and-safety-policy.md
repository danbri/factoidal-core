# Font trust and safety policy for the Lean browser

Status: approved direction (owner, 2026-11-03, decisions 1 to 4). No code yet.
Tracking: https://github.com/danbri/factoidal/issues/1233.

## 1. Problem

A font file is untrusted input, and it contains programs. The current browser
path (`docs/designissues/2026-11-03-dynamic-font-requests.md`) gives font
files to native HarfBuzz and FreeType in a separate process. Lean checks the
output (`Rendering/FontData.lean`, `Rendering/FontProvider.lean`) but does not
read the font. The default binding is the local macOS Arial file, which is not
open source. The WebGPU demonstration uses the lab 5x7 ASCII bitmap font
(`labs/demos/foafnaut/Font.lean`), with no shaping.

Owner, 2026-11-03, verbatim: "we should fix architecture so that opensource
fonts and font software can be brought into the lean world (transliterated?
verified? signed? unclear! fonts embed software see recent infamous tiny llm in
a font stunt:)". The reference is llama.ttf, which runs a small language model
through the experimental HarfBuzz WebAssembly shaper (the OpenType `Wasm`
table).

## 2. Font content by kind

| Content | Kind | Proposed default |
|---|---|---|
| sfnt directory, `head`, `maxp`, `cmap`, `hhea`, `hmtx`, `glyf`/`loca`, `name`, `OS/2`, `post` | data | parse in Lean |
| `fvar`, `avar`, `gvar`, `HVAR`, `MVAR` | data and arithmetic | parse in Lean |
| `CFF `, `CFF2` charstrings | stack language for outlines | interpret in Lean with fuel; the spec limits on stack and subroutine depth apply |
| `GSUB`, `GPOS`, `GDEF` | substitution and positioning lookups | interpret in Lean with fuel and an operation limit per run |
| `COLR` v0/v1, `CPAL` | layer list; v1 is a paint graph that can have cycles | check the graph has no cycle, then paint |
| `SVG ` | SVG documents | static SVG renderer only; no script, no external reference |
| `fpgm`, `prep`, `cvt `, glyph instructions | TrueType hinting virtual machine | not run; outlines are drawn without hinting |
| `morx`, `kerx` (AAT) | state machines | refused |
| Graphite (`Silf`, `Glat`, `Gloc`) | rule language | refused |
| `Wasm` | general WebAssembly program | refused |
| `DSIG` | signature over the font | not used for trust (section 5) |

## 3. Decision 1: refusals are understandable and configurable (approved)

Owner, 2026-11-03, verbatim, on "Font code policy: interpret CFF, GSUB/GPOS and
COLR in Lean with fuel; never run hinting; refuse AAT, Graphite and Wasm
tables": "Make refusals understandable, and configurable, with current safety
settings easily accessed. We can also have a \"safe\" mode that uses only a
baked in, no wasm etc. ascii font."

### 3.1 One policy value, in Lean

`Rendering.FontPolicy` is a Lean structure: one field for each row of the table
in section 2, and the numeric limits (font bytes, glyph count, charstring fuel,
lookup operations per run, COLR graph depth, outline commands). The renderer
reads font data only through this value. No host decides a font policy.

### 3.2 Three modes

- `safe`: only the baked-in Lean ASCII bitmap font. No font file is read, no
  external font data is accepted, and no font program is run. A character
  outside the font is drawn as a visible replacement glyph and reported once
  for each page, with its code point. The page still renders.
- `standard` (default): the rules of section 2.
- `custom`: `standard` with overrides, one for each setting.

### 3.3 Changing a setting

- A setting that reduces risk (refuse a table, lower a limit) needs no special
  name.
- A setting that allows a table that is refused by default has a name that
  starts with `--dangerously-allow-font-` (for example
  `--dangerously-allow-font-hinting`). The program writes a warning at start
  that names the setting. This follows the 2026-10-28 rule for login rate
  limits.
- A setting can allow only a table that has an implementation. For a table
  with no implementation, the refusal says so, and the gap has an open issue
  and an expected-failure test (rule of 2026-09-07). The `Wasm` table has no
  planned implementation. Its refusal gives the reason, not an issue.

### 3.4 What a refusal contains

Each refusal is a typed Lean value (`FontRefusal`), written as text by one
Lean function:

1. A stable code, for example `font.table.wasm`.
2. The font: family, file name, sha256.
3. The table tag, and one sentence on what the table does.
4. The risk, in one sentence.
5. The setting that controls it, its current value, and where that value came
   from (default, environment, option, page settings).
6. What the renderer did instead: drew the glyph without hinting, used the safe
   font, or did not render the text.
7. A link to the user documentation for that code.

Example text:

```
font.table.wasm: "Example Sans" (example.ttf, sha256 3f9a...) has a Wasm table.
A Wasm table is a program that the font asks the text shaper to run.
Risk: the program can do any computation and can change every glyph.
Setting: font.wasm = refuse (default). There is no option to run it.
Action: the text was shaped from GSUB/GPOS only.
More: <link to the documentation section for font.table.wasm>
```

### 3.5 Access to the current settings

- CLI: `factoidal font-policy` writes the effective settings, with the source
  of each value.
- Browser: a settings panel shows the mode, every setting, and the refusals for
  the current page. A small indicator shows the mode at all times.
- Evidence record: each render records the policy value and every refusal, so
  a result always states what font code was allowed.

## 4. Decision 2: shaper in Lean, HarfBuzz as oracle (approved, with a licence condition)

Owner, 2026-11-03, verbatim: "2 yes, if license good."

Port the function of HarfBuzz to Lean, not its code. Conformance target:
HarfBuzz's own shaping tests (each case is a font, an input text and the
expected glyphs, clusters and positions). The native HarfBuzz/FreeType adapter
stays only as a differential oracle. Order: Latin, Greek and Cyrillic with
`liga`, `kern` and GPOS; then Arabic; then Indic and the Universal Shaping
Engine. What can be proved: the parser is total; each glyph id is less than
`numGlyphs`; time and memory have a bound for each input size; source
clusters cover the input in order.

Licence condition, step 0, before any test data enters
`third_party/testing`: record the licence of the HarfBuzz source used as a
reference, and of each test font and expectation file, case by case. A case
whose font licence does not permit redistribution is not vendored; it is
counted apart as "not vendored (licence)", with its reason. The record goes
in `third_party/testing/<suite>/PROVENANCE.md`.

## 5. Decision 3: trust record; DSIG is checked and reported, not trusted (approved)

Owner, 2026-11-03, verbatim: "we should note dsig and exercise our
factoidal/core signature checking but not read too much into it."

- Trust comes from the total, bounded Lean parser and from the policy of
  section 3. Each font has an evidence entry: sha256 (the records already
  carry `fontSha256`), source URL, version, licence.
- A `DSIG` table is parsed and its signature checked with the Factoidal
  signature code. The result goes in the evidence entry as one of: no `DSIG`;
  `DSIG` present, signature matches the key of the enclosed certificate;
  does not match; not checked (with the reason). It never changes the
  policy, the mode or a refusal.
- The report says what a match means: the bytes match a key in a certificate
  inside the same file. With no certification path check it does not identify
  anyone. `XML/X509.lean` reads DER certificates but does not check a
  certification path.
- Gap: `DSIG` signature blocks are PKCS#7 (CMS SignedData). The Lean tree has
  X.509 DER reading, RSA, SHA-1 and SHA-2, but no CMS SignedData reader. That
  reader is a work item of the tracking issue. The exact bytes that the
  digest covers are taken from the OpenType `DSIG` chapter and checked against
  signed fonts before the check is reported as working.

## 6. Decision 4: pinned fonts fetched by a tool (approved)

Owner, 2026-11-03, verbatim: "our npm already huge so pinned i guess".

A pinned set of OFL fonts (candidates: Noto, Source, Inter, Liberation), each
with source URL, version, licence and sha256, fetched and checked by a tool in
the manner of `tools/fetch-builds.sh`. Fonts are not committed and not in the
npm package. The `safe` mode font is Lean source and needs no fetch. The
default binding stops being the local Arial file.
