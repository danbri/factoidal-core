# BubblePopJS Intl (ECMA-402): plan

Status: plan, nothing implemented. Written 2026-11-16 against the full Test262 run
[20261116T0257Z](https://github.com/danbri/factoidal-builds/tree/wpt-scores/runs/20261116T0257Z-test262-linux-x86_64-gh43795241382a1)
(core commit 78f0256d1, BubblePopJS in the page realm): 46,389 of 53,795 files, 86.23%.

## Where the gap is

`Intl` is not defined in the page realm, and the global is what 2,474 runs (two modes per file) trip over. The
`intl402/` tree is 3,372 files of which 91 pass. Failing files per subdirectory, from
[directories.csv](https://github.com/danbri/factoidal-builds/blob/wpt-scores/runs/20261116T0257Z-test262-linux-x86_64-gh43795241382a1/directories.csv)
(files minus passed):

| Directory | Files | Failing |
|---|---:|---:|
| intl402/Temporal | 2,040 | 1,970 |
| intl402/NumberFormat | 251 | 251 |
| intl402/DateTimeFormat | 246 | 246 |
| intl402/Locale | 190 | 190 |
| intl402/DurationFormat | 110 | 110 |
| intl402/ListFormat | 81 | 81 |
| intl402/RelativeTimeFormat | 80 | 80 |
| intl402/Segmenter | 79 | 79 |
| intl402/Intl | 66 | 66 |
| intl402/Collator | 65 | 65 |
| intl402/DisplayNames | 57 | 57 |
| intl402/PluralRules | 53 | 53 |
| intl402/String | 19 | 13 |
| intl402/BigInt | 11 | 8 |
| intl402/Number | 7 | 5 |
| intl402/Date | 12 | 4 |
| intl402/FallbackSymbol | 2 | 2 |
| intl402/Array | 2 | 1 |
| intl402 (top level) | 22 | 22 |
| **Total** | **3,372** | **3,281** (3,303 with the top level) |

Two things shape the plan:

- 1,566 files carry the feature `Intl.Era-monthcode` (65 pass), nearly all in `intl402/Temporal`. They are non-ISO
  calendars, and the run lists the feature among the excluded ones
  ([features.csv](https://github.com/danbri/factoidal-builds/blob/wpt-scores/runs/20261116T0257Z-test262-linux-x86_64-gh43795241382a1/features.csv),
  `excluded=true`; 2,995 files are excluded in all, giving the 89.53% share without them). `Intl.Locale-info` (77) and
  `Intl.NumberFormat-v3` (99) are excluded too. So about 470 of the 1,970 Temporal files need only the ISO calendar and
  time zones; the rest need calendars.
- Outside `intl402/`, `built-ins/Temporal` fails 483 of 4,616 files. Part of that is time zones and calendars as well.

One file is 0.0019 of a percentage point. Passing all 3,303 failing intl402 files would take the score to 92.4%.

## What Intl needs

Spec-level pieces, in dependency order:

1. **Language tags**: BCP 47 / UTS 35 `unicode_locale_id` parsing, structural validity, canonicalisation (alias
   tables for language, script, region, variant; extension ordering), `Intl.getCanonicalLocales`.
2. **Locale negotiation**: `CanonicalizeLocaleList`, `LookupMatcher`/`BestFitMatcher` (best fit may be lookup),
   `ResolveLocale`, `SupportedLocales`, `supportedLocalesOf` on every constructor, the `-u-` keyword and
   `relevantExtensionKeys` handling, `Intl.supportedValuesOf`.
3. **Intl.Locale**: constructor options, accessors, `maximize`/`minimize` (CLDR likely subtags), `Intl.Locale-info`
   getters (week data, hour cycles, text direction, calendars, collations, numbering systems).
4. **NumberFormat**: digit options and rounding (the spec's exact rounding modes and increments), grouping, sign
   display, notation (compact, scientific, engineering), currency and unit styles, numbering systems, `formatToParts`,
   `formatRange`.
5. **PluralRules**: the CLDR plural operands and rule evaluator (cardinal and ordinal), `selectRange`.
6. **DateTimeFormat**: skeleton and pattern selection, field widths, calendars, hour cycles, time zones (IANA names,
   offsets, display names), `dateStyle`/`timeStyle`, `formatToParts`, `formatRange`, `dayPeriod`,
   `fractionalSecondDigits`.
7. **Collator**: UCA ordering with CLDR tailorings, strength, `numeric`, `caseFirst`, `ignorePunctuation`, `usage`.
8. **RelativeTimeFormat, ListFormat, DisplayNames, DurationFormat**: pattern lookup from CLDR plus the plural
   selector and NumberFormat; DurationFormat also uses `Intl.NumberFormat-v3` digit options.
9. **Segmenter**: grapheme, word and sentence segmenters with `containing`, `isWordLike`, and the iterator.
10. **Temporal's Intl parts**: IANA time zone identifiers and offsets, `ZonedDateTime` transitions and disambiguation,
    calendars (ISO, Gregorian, then the others) with eras and month codes, `toLocaleString` on Temporal types.
11. **`toLocale*` methods**: `String.prototype.localeCompare`, `toLocaleUpperCase`/`LowerCase` (language-sensitive
    case mapping for `tr`, `az`, `lt`), `Number`, `BigInt`, `Date`, `Array`, `TypedArray` `toLocaleString`.
12. **Structure Test262 checks everywhere**: property descriptors, `length`, `name`, `Symbol.toStringTag`, option
    read order, `resolvedOptions` key order, `FallbackSymbol`, `new.target` handling. These are a large share of each
    directory and cost little once a constructor exists.

## What already exists in the repo

Reuse these before writing anything:

- [Unicode/Segmentation.lean](../../formal/lean4/L4Factoidal/Unicode/Segmentation.lean): UAX #29 grapheme, word and
  sentence boundaries for Unicode 18.0.0, linear time, with
  [theorems](../../formal/lean4/L4Factoidal/Unicode/SegmentationTheorems.lean) and generated data tables. This is the
  whole algorithmic core of `Intl.Segmenter`; `Unicode/LineBreak.lean` is there for a later `granularity: "line"`.
- [Unicode/Normalization.lean](../../formal/lean4/L4Factoidal/Unicode/Normalization.lean): NFC, NFD, NFKC, NFKD, used by
  `String.prototype.normalize` and by the collator.
- [XPath4/Collation.lean](../../formal/lean4/L4Factoidal/XPath4/Collation.lean) with a 181 KB DUCET table
  (`XPath4/UcaData.lean`, UCA 16.0.0): longest match, implicit weights, variable weighting, strength, `alternate`,
  `backwards`, `caseFirst`, `caseLevel`, `numeric`. No tailorings. This is the collator for the root locale.
- [JS/NumFmt.lean](../../formal/lean4/L4Factoidal/JS/NumFmt.lean): exact decimal digit generation for `toFixed`,
  `toExponential` and `toPrecision` from the double's rational value. NumberFormat's rounding builds on this.
- [XPath4/Format.lean](../../formal/lean4/L4Factoidal/XPath4/Format.lean) and `XPath4/NumberWords.lean`:
  `format-number`, `format-integer` and `format-dateTime` with English, German, French and Italian names. Useful as a
  second oracle for the English slice; its picture-string model is not the ECMA-402 model, so it is not the base.
- [JS/Date.lean](../../formal/lean4/L4Factoidal/JS/Date.lean) (local time is UTC today) and
  [Temporal/Iso.lean](../../formal/lean4/L4Factoidal/Temporal/Iso.lean) / `Temporal/Parse.lean`: ISO calendar
  arithmetic and parsing. Time zones and non-ISO calendars are the missing layer.
- Not found: a BCP 47 parser and canonicaliser (the language-range matching in `CSVW` and `Fn/String` is matching
  only), any CLDR data, any tzdb reader, any plural evaluator, any language-sensitive case mapping beyond the
  default.

## Data sources, licences, sizes

| Source | Licence | Used for | Expected size, to be measured in slice 0 |
|---|---|---|---|
| [CLDR](https://cldr.unicode.org/) (JSON or XML from the Unicode release) | Unicode License v3 (permissive; notice must travel with the data) | likely subtags and aliases, plurals, number, date, unit, list, relative-time and display-name patterns, week data, collation tailorings | `en` pattern data should be in the low hundreds of KB as source and tens of KB packed; all locales are too big to ship, so locales are separate packs |
| [IANA tz database](https://www.iana.org/time-zones) | public domain | zone rules and transitions, link names | `tzdata.zi` is about 100 KB of text; a packed transition table is of that order |
| [ICU4X](https://github.com/unicode-org/icu4x) algorithms and data model | Unicode License v3 (check each crate's header when porting) | calendrical algorithms, data layout ideas, test vectors | read and port in Lean; nothing linked |
| Existing `third_party/unicode-18.0.0` | Unicode License | scripts, segmentation, normalisation (already vendored) | 8.5 MB of source text, already in tree |

Rules that follow from the licence policy:

- No ICU C++ and no ICU4X Rust is linked, built or called. Algorithms are re-written in Lean from the specifications
  (UTS 35, UTS 10, UAX 29, ECMA-402) with ICU4X as a reading aid and a test-vector source.
- Everything here is permissive, so data and ported algorithms may be mixed in. Any GPL or AGPL source is out of scope.
- CLDR and tzdb arrive under `third_party/cldr/` and `third_party/tzdb/` with a PROVENANCE file (release, source URL,
  hash) and the Unicode licence text, following the pattern of `third_party/unicode-18.0.0/PROVENANCE.md`.
  CLDR needs to be pinned to the release whose Unicode version matches the 18.0.0 tables already in tree.

## How it fits decisions in Lean

The core rule is that decisions are Lean and the host moves bytes.

- **Algorithms are Lean**: tag parsing and canonicalisation, negotiation, the rounding and digit-grouping engine, the
  plural evaluator, pattern selection and filling, UCA comparison with tailorings, UAX #29, time zone offset lookup,
  calendar arithmetic. None is written in JavaScript, and a missing locale pack turns that locale off (the
  negotiation reports it as unsupported) instead of falling back to a JS copy.
- **Data is Lean tables or verified packs.** Two forms, chosen by size and by how often the data is touched:
  - Small, always-needed data (alias tables, likely subtags, `en` and `und` root patterns, plural rules) is generated
    into Lean modules by a script in `tools/`, as the Unicode tables are today, and compiled in.
  - Per-locale and tz data is a packed binary: a header, a sorted string table, and fixed-width records. The host
    fetches the bytes (as it fetches any resource); Lean parses them with a loader that checks magic, version, length
    fields and a content hash before use, and refuses anything out of bounds. The loader has a proved bound on the
    work it does for a given input length, and a defined refusal at the bound.
  - The generators are in the tree and the packs are rebuilt from the vendored CLDR and tzdb in CI, so the pack is
    never a trusted binary.
- **No host-supplied locale facts.** The user's preferred languages and the system time zone reach Lean as data
  from the host, labelled as reported by the host, and negotiation is still done in Lean.
- **Privacy**: the default locale list is a fingerprinting surface. Lean owns the policy for what a page may see (for
  example, a coarse, user-controllable locale list), so the one place that exposes it is one place to audit.

### Size and speed budget for the Wasm build

- A page that never touches `Intl` pays nothing: the global is installed lazily (the object exists, constructors
  and their data are created on first use), and no data is parsed until a constructor needs it.
- Compiled-in data is limited to what negotiation needs: the alias and likely-subtags tables and the `en`/root
  patterns. Target for the first slice: under 150 KB added to the Wasm module, measured; if it is more, the English
  data moves into a pack as well.
- Every other locale is a pack of tens of KB, loaded when a constructor is called for it (or when
  `supportedLocalesOf` needs its name, answered from a small index that holds only the locale list). Parse is lazy
  per section: number patterns, date patterns and unit patterns are separate sections of one pack.
- tzdb: one pack for all zones, loaded on first time-zone use (a named zone, `Temporal.ZonedDateTime`, `timeZone`
  option). UTC and fixed offsets need no data.
- Hot paths get cost tests: `Number.prototype.toLocaleString` for a repeated locale reuses the resolved formatter
  (cache keyed by the canonical locale and options, as the specification invites), and a test fails if formatting
  1,000 numbers parses a pack more than once. Before and after timings go in every hand-back, including startup of a
  page with no `Intl` use.

## Algorithms: what is built, what is ported

| Piece | Source of truth | Plan |
|---|---|---|
| BCP 47 / UTS 35 tags | RFC 5646, UTS 35 part 1, CLDR alias and likely-subtag data | new, Lean |
| Number formatting | ECMA-402 `FormatNumericToString`, CLDR number patterns | extend `JS/NumFmt.lean` digit engine; new pattern layer |
| Plural rules | UTS 35 part 3 plural operands and rule grammar | new, Lean: parse the rule strings from CLDR into an AST, evaluate on operands; no code generation per locale |
| Collation | UTS 10, DUCET (present), CLDR root and tailorings | extend `XPath4/Collation.lean`; tailorings from CLDR rule text, `ignorePunctuation`, `numeric` exist |
| Segmentation | UAX 29 | present; wrap |
| Time zones | tzdb rules and links | new, Lean: transition table lookup in both directions (UTC to local, local to UTC with the spec's disambiguation) |
| Calendars | ICU4X and *Calendrical Calculations* algorithms | new, Lean, after ISO and Gregorian: Japanese, Buddhist, ROC, Persian, Indian, Ethiopic, Coptic, Hebrew, Islamic variants, Chinese and Dangi last |
| Date and time patterns | CLDR `availableFormats` skeletons and `dateTimeFormats` | new, Lean: skeleton matching per UTS 35 part 4 |

## Slices

Estimated Test262 gain is in files of the 7,406 now failing, and is an estimate until measured: each slice's hand-back
replaces it with the full-run number. Agent time is wall-clock for one agent, with build waits included (one Lean build
at a time under the shared lock; cloud runs about 1.5 h for builds and about 13 minutes for a full Test262 run).

| Slice | Content | Expected files gained | Agent time |
|---|---|---:|---|
| 0. Foundation | `Intl` object (lazy), `getCanonicalLocales`, `supportedValuesOf`, tag parser and canonicaliser, negotiation, `Intl.Locale` without likely-subtags data and without the info getters, vendoring `third_party/cldr` and `tzdb` with provenance and licence, pack format and verified loader, size and speed baseline | 230 (Intl 55, Locale about 100, structure checks in the other directories) | 4 to 6 hours |
| 1. Numbers, `en` | NumberFormat (digits, rounding, grouping, sign, percent, basic currency and unit, `formatToParts`), PluralRules cardinal and ordinal, `toLocaleString` for Number and BigInt, locale packs for `en` | 205 (NumberFormat about 150, PluralRules about 35, String/Number/BigInt about 20) | 5 to 7 hours |
| 2. Dates and zones | tzdb pack and offset lookup, `Date` local time from the host zone, DateTimeFormat (Gregorian, styles, skeletons, `hour12`/`hourCycle`, `timeZone`, `formatToParts`), `Date` `toLocale*`, Temporal `ZonedDateTime` and `Instant` zone behaviour, `toLocaleString` on Temporal types, likely-subtags for `Intl.Locale.maximize` | 270 (DateTimeFormat about 120, Temporal ISO and zone parts about 140, Date and Locale about 10) | 8 to 12 hours |
| 3. Order and segments | Collator with CLDR root and tailorings for the common languages, `localeCompare`, Segmenter over the existing UAX 29 code, ListFormat | 165 (Collator about 45, Segmenter about 60, ListFormat about 60) | 4 to 6 hours |
| 4. Words and durations | RelativeTimeFormat, DisplayNames, DurationFormat, NumberFormat v3 options (range, rounding priority, trailing zeros), `Intl.Locale-info` getters | 170 (RelativeTimeFormat about 55, DisplayNames about 35, DurationFormat about 80), plus the 99 and 77 excluded files of v3 and locale-info that do not count in the without-excluded share | 5 to 8 hours |
| 5. Calendars | Non-ISO calendars for Temporal and DateTimeFormat, eras and month codes, `Intl.Era-monthcode` | 900 to 1,400 of the 1,501 failing files of that feature (excluded from the share without excluded features, in the full denominator) | 12 to 20 hours, mostly Chinese, Dangi, Hebrew and Islamic |

Cumulative: slices 0 to 4 add about 1,040 files (88.2%, 47,429 of 53,795) and slice 5 takes the full-denominator
score to about 90% to 91%. Slices 0 to 2 (705 files, 87.5%) are the first stop: they cover the largest shares of
everyday site use (`toLocaleString`, `Intl.NumberFormat`, `Intl.DateTimeFormat`), which matters next to the number.

### Minimal first slice, as the brief put it

Slices 0 and 1 together are the minimal usable `Intl`: the object, `Locale`, `NumberFormat` and `PluralRules` for
`en`. Slice 2 adds `DateTimeFormat` basics and the time zones from tzdb. They are split so each can land and be
measured on its own, and so a full Test262 run (about 13 minutes) and the Wasm size check follow each one.

## Proof targets

What is proved is stated per theorem in the hand-back; what is only tested is said so.

- **Tags**: canonicalisation is idempotent; the output of canonicalisation parses and is structurally valid; parsing
  and printing a canonical tag round-trips; case folding is total and keeps the tag's length class. The alias
  application is a terminating rewrite (the alias table has a measure that falls, checked when the table is
  generated).
- **Negotiation**: `ResolveLocale` returns a locale from the available list, or the default; the result of
  lookup is a prefix of a requested tag (by removing subtags from the right); adding unsupported locales to the
  request never changes an earlier supported result.
- **Plural rules**: the evaluator is total over operands; the parsed rule AST re-prints to the CLDR rule text it came
  from; for every locale in the data, the sample integers and decimals listed in the CLDR rules (`@integer`,
  `@decimal`) fall in the category that lists them. The last one is a check over the data at build time, and is the
  statement that the evaluator matches the CLDR specification on its own examples.
- **Number formatting**: the digit engine's output reads back to the rounded value (digits round-trip: parsing the
  formatted digits gives the rational the rounding mode selected); rounding with increment 1 matches the existing
  `toFixed` theorems; grouping inserts separators without changing the digit sequence (removing them gives the
  original); the number of significant digits and fraction digits respects the min and max options.
- **Time zones**: for every zone, local-to-UTC then UTC-to-local is the identity outside gaps and folds, and inside them
  yields the disambiguation the Temporal specification names; offsets are within the bounds the loader checks;
  transitions are strictly increasing (checked in the generator and in the loader).
- **Calendars**: for each calendar, date-to-fixed-day and fixed-day-to-date are inverse over a bounded range; month
  lengths sum to year length; the round trip with ISO holds. The Test262 calendar files are the oracle beyond the
  bounded range.
- **Collation**: comparison is a total preorder (reflexive, transitive, antisymmetric up to canonical equivalence) at
  each strength; sort keys agree with comparison; the result is invariant under NFC and NFD of the input.
- **Segmentation**: the existing theorems; `Intl.Segmenter.segment` pieces concatenate to the input and
  `containing(i)` returns the piece whose range holds `i`.
- **Packs**: the loader terminates within a bound linear in the pack length, rejects any offset or length outside the
  pack, and a pack accepted by the loader decodes to the table the generator wrote (tested over all shipped packs, and
  proved for the length and offset checks).
- **Resource bounds**: option objects and locale lists are page-controlled, so list lengths, tag lengths, digit
  counts (the specification caps fraction digits at 100) and range sizes in `formatRange` have a proved bound and a
  defined refusal (a RangeError) at it. A long `Intl.Segmenter` input or a huge `maximumFractionDigits` must not be
  able to hang the engine.

## Risks and choices that stay open

- **CLDR size**: if `en` alone is larger than the budget, English also moves to a pack. The decision is measured in
  slice 0, not guessed.
- **Best fit matching** may stay equal to lookup: the specification allows it, and it is the smaller proof.
- **Locale reporting**: which locales count as supported is a choice between a short list (small, fast, fewer
  tests passing in other directories that loop over `supportedLocalesOf` results) and a long one. Slice 0 starts with
  the locales that have packs and grows by data, never by code.
- **Time zone data updates**: tzdb changes several times a year, and an old pack gives wrong offsets for new
  rules. The pack records its tzdb version, `resolvedOptions` and the about page report it, and CI rebuilds it.
- **Host time zone**: `Date` local time is UTC today. Slice 2 reads the host's zone name as data; a page with
  fingerprint protection on sees UTC.
- **Excluded features**: slice 5 and parts of slice 4 move the full-denominator score but not the share without the
  excluded features. Both numbers are reported.
