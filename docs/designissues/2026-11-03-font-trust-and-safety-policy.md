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

## 7. Implementation, 2026-11-03 (branch `claude/lean-shaper`)

The Lean shaper of decision 2 runs in the browser, in a local instance on port
8104. It is not on `main`, and the frozen ports 8099 to 8103 do not use it.

Pipeline (`formal/lean4/L4Factoidal/Rendering/`):

| Stage | Module | Content |
|---|---|---|
| Font check | `FontPolicy` | sfnt/TTC table directory, table classes, modes, refusals |
| Tables | `SfntMetrics` | `head`, `hhea`, `maxp`, `hmtx`; `cmap` formats 4 and 12 |
| Normalization | `SfntNormalize` | HarfBuzz "composed" mode on the UAX #15 tables of `Unicode.Normalization` |
| Substitution | `SfntSubst` | GSUB `rvrn`, `ccmp`, `locl`, `rlig`, `liga`, `clig`, `calt`; types 1, 2, 4, 5, 6 (formats 1 to 3), 7 |
| Positioning | `SfntGpos` | GPOS `abvm`, `blwm`, `dist`, `kern`, `mark`, `mkmk`; types 1, 2, 4, 6, 9 |
| Run | `SfntShape` | clusters at HarfBuzz's monotone-grapheme level, as UTF-8 byte offsets |
| Adapter | `LeanFontShape` (`lake build l4font-shape`) | same arguments as `font-shape` |

`l4font-shape` shapes in Lean, then runs `font-shape FONT TEXT PX FACE
--glyphs SCRIPT SPEC`. In that mode HarfBuzz does not run: FreeType loads the
glyphs that Lean chose and adds outlines and rasters. The record says
`"harfbuzzVersion": "none (Lean shaper)"`. Without `--glyphs`, `font-shape`
gives output byte-identical to the frozen binary (4 of 4 records compared).

Refused with a message (`font.layout.unsupported`, naming the lookup or code
point): strong right-to-left text; GSUB types 3 and 8; GPOS types 3, 5, 7, 8;
mark filtering sets; a combining mark in a font with no GPOS table, where
HarfBuzz uses its own fallback mark positioning (a heuristic, not OpenType).

Measured:

- `labs/demos/foafnaut/tools/check-lean-shaper.py`, complete records against
  the HarfBuzz path at 20 px: 54 same, 0 different, 2 refused (out of 56), over
  Ahem, Arial, Lato (OFL), Liberation Sans Bold (OFL); Latin, Greek, Cyrillic,
  emoji, ligatures, kerning, combining marks. The 2 refusals are Ahem with
  combining marks (no GPOS).
- `check-document-fonts.mjs` with the Lean adapter: PASS, native and WASM
  engines give identical document results from Lean-shaped records.
- `check-document-browser.mjs` against port 8104 in Chrome with WebGPU: PASS
  (4 groups: external CSS and JS, QuickJS click, reflow, source edit).
- Time for one adapter call, `Hello` in Arial: 50 ms (Lean) against 10 ms
  (HarfBuzz path). Ahem: 30 ms. The FreeType child is 10 ms of each.

Not done: RTL and the Arabic, Indic and USE shapers; outlines in Lean (`glyf`,
CFF); the HarfBuzz test suite (licence record first); `safe` mode in `Layout`;
the policy reaching the broker for AAT (`morx` is not applied by the Lean
shaper, so on this path the AAT refusal holds).

## 8. HarfBuzz shaping suite, and its licence record

Runner: `labs/demos/foafnaut/tools/run-harfbuzz-suite.py`, over
`test/shape/data` of the HarfBuzz 15.0.0 source (the version of the local
`hb-shape`). A test passes when `hb-shape` gives the expected string and the
Lean adapter equals `hb-shape` in glyph-id form (ids, clusters, advances,
offsets). That transitive check needs no glyph-name table in Lean.

Result, 2026-11-03, commit after `3f12ccf04` on `claude/lean-shaper`:
2,682 pass, 571 fail, 1,532 refused by Lean (out of 4,785 applicable); 1,433
not applicable (the test sets an option the adapter does not take: most are
`--font-size` 746, `--features` 333, `--variations` 127); 2 oracle mismatch
(HarfBuzz 15.0.0 itself does not give the expected string); 243 lines are
directives.

Largest failing groups: USE, Khmer, Indic, Tibetan and Mongolian shaping
(complex-script shapers not implemented). Largest refused group: 1,284
emoji-cluster tests in a font with marks and no GPOS (HarfBuzz fallback mark
positioning, a heuristic, not implemented). RTL tests are refused.

Fixes that this suite found and that are now in Lean, ported from the
HarfBuzz 15.0.0 source: `cmap` format 13; continuation rules for clusters
(`hb_set_unicode_props`: marks, emoji modifiers, regional indicator pairs,
ZWJ with Extended_Pictographic, tags; ZWNJ is not a continuation); space
fallback widths (`_hb_ot_shape_fallback_spaces`); default ignorables
(`hb_ot_zero_width_default_ignorables`, `hb_ot_hide_default_ignorables`).

Licence record (condition of decision 2). Nothing is vendored yet.

| Directory | Lines | Licence | Vendoring |
|---|---|---|---|
| `aots` | 404 | Apache-2.0, Adobe (`aots/COPYING`) | permitted, with NOTICE |
| `text-rendering-tests` | 847 | Apache-2.0, Unicode Inc. (`text-rendering-tests/COPYING`) | permitted, with NOTICE |
| `in-house` | 5,212 | no own COPYING; HarfBuzz top-level "Old MIT" by its own rule, but the 221 fonts are subsets of third-party fonts named by hash, with no recorded origin | not cleared: run from a local download only |
