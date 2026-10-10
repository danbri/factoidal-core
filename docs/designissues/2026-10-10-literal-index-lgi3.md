# LGI3 and LGI4: new wire names for the literal gram index

Date: 2026-10-10. Case-mapping issue: <https://github.com/danbri/factoidal/issues/706>.
Case-mapping record: `docs/designissues/2026-10-10-unicode-case-mapping.md`
section 6. Index design: `docs/designissues/2026-09-04-literal-token-index.md`.
Code: `formal/lean4/L4Factoidal/Storage/LiteralGramIndexWire.lean`,
`ShardManifest.lean`, `GenerationVerify.lean`, `PackStream.lean`,
`Wasm/Ops/StoreHandles.lean`, `Harness/LiteralGate.lean`.

## 1. What changed and why

Merge 1107b396 changed the fold the literal gram index uses. Before it, the
index folded each lexical form with `String.toLower`, which changes `A` to `Z`
only. After it, the index folds with `Text.CaseMap.searchFold`, the Unicode
fold, because SPARQL `LCASE` is the Unicode default case mapping.

For ASCII text the grams, and so the bytes, are the same. For a non-ASCII
literal they are not. `CONTAINS(LCASE(?x), "école")` keeps the row
`École Normale`. The ASCII-folded index held the grams `Éco` and `Nor` for that
row and the needle `école` carried the gram `éco`, so the index listed no
candidate and the filter dropped a row that the scan keeps. A file written
before the merge is therefore not a superset of what the scan keeps. The LGI1
and LGI2 headers carry no fold identifier, so a reader could not tell.

Storage rule 2 (`skills/shardborough-storage/SKILL.md`, "Rules when changing a
format"): a byte change is a new wire version; bump the format name rather than
change bytes under a name. The standing rule "There are no users. Prefer the
right structure to the compatible one" (owner, 2026-08-26, CLAUDE.md) removes
any argument for keeping the old files readable.

## 2. Decisions

### 2.1 Two names

| Old | New | Layout | Magic | Version byte | Sidecar suffix | Manifest labels that name it |
| --- | --- | --- | --- | --- | --- | --- |
| LGI1 | LGI3 | fixed u32 gaps, no opaque list; IBK3 and IBK4 blocks | `LGI3`, `0x3349474C` | 3 | `.lgi3` | `quad-ibk4-ptd1-lgi3-merkle-v0` (wire version 8), `quad-ibk4-ptd1-lgi3-gbi1-merkle-v0` (wire version 9) |
| LGI2 | LGI4 | LEB128 gaps, opaque list; IBK5 blocks | `LGI4`, `0x3449474C` | 4 | `.lgi4` | `quad-ibk5-ptd2-lgi4-gbi1-merkle-v0` (wire version 10) |

The two layouts did not merge into one name. They differ in the gap encoding
and in the opaque list, and they serve different block codecs: an IBK4
dictionary holds no out-of-line literal, so its opaque list is always empty.
Merging them would give every IBK4 generation a second, unrelated byte change
(varint gaps and an extra count field) and would delete the fixed-width codec
with its `#guard`s. Neither is needed to fix the fold. A later merge is a
separate decision with its own size measurement.

The byte layouts did not change. LGI3 is the LGI1 layout and LGI4 is the LGI2
layout, with the magic and the version byte replaced. The CRC-32C covers the
payload after the version byte, so for ASCII text an LGI1 file with its magic
and version replaced is exactly the LGI3 file of the same index.
`LiteralGramIndexWire.lean` pins that with the bytes the old encoders wrote
(`legacyLgi1`, `legacyLgi2`, taken from the tree at commit 685326b2).

The Lean identifiers keep their shape: `magic`, `version`, `encode?`,
`decode?`, `supported` and `Prefix` are the first layout, and the same names
with the suffix `2` are the second. Only their values changed. A rename of
every identifier would touch every reader for no change in behaviour.

### 2.2 The old names are errors, with the cause

The encoders write only the new names. The decoders admit only the new names.
`supported` and `supported2` are unchanged, so encoder admission still equals
decoder admission (rule 1).

`retiredName?` recognises the magic of LGI1 and LGI2. `retiredMessage` says:

> literal index LGI1 was folded with the ASCII-only fold. It does not hold all
> the rows that the Unicode LCASE keeps. Re-pack the generation with the
> current packer. The packer writes LGI3 or LGI4.

Theorems in `LiteralGramIndexWire.lean`: `decode?_not_retired`,
`decode2?_not_retired` (neither decoder accepts bytes that start with a retired
magic) and `retired_refused`. `magics_distinct` pins that the four magics are
distinct.

### 2.3 The manifest: labels renamed, wire versions kept

The manifest names the index by its layout label. The labels that named LGI1
and LGI2 are replaced (table in 2.1) and `retiredLiteralIndexLayouts` lists the
three retired ones. `layoutConsistent` refuses a retired label at EVERY wire
version, including versions 0 to 2 whose labels are otherwise free. A manifest
packed before the rename is refused by `decode?`; `retiredLayoutNote?` reads the
label from the header and gives the message above, so the tools say why.

The manifest wire versions 8, 9 and 10 keep their numbers. Their field sets did
not change. The alternative was to retire 8, 9 and 10 and write the same content
as 11, 12 and 13. That is the stricter reading of rule 2: the label is a
statement of the sidecar contract, and "SBM9" now means two different byte
strings at two different dates. It was not chosen for three reasons.

1. Every wire-version literal in the manifest codec, its round-trip theorems,
   the packer, the activator, the wasm operations, the npm host, the smoke
   scripts and the specification would move, and a mistake in one of them
   (`version == 10` guards the blob table and the zone maps) would pass its own
   gate.
2. The old manifest is refused in both directions. A new reader refuses an old
   label, and an old reader refuses a new label, because `layoutConsistent` pins
   each version to exactly one label. No byte string is read under a meaning it
   does not have. The rule exists to prevent silent drift, and refusal is not
   silent.
3. The packer writes only version 9 for IBK4 and version 10 for IBK5. Version 8
   (IBK4 plus the literal index, no geometry index) has no writer.

This is a Claude-chosen default, not an owner ruling. If the owner prefers new
version numbers, the change is mechanical and the retired-label machinery stays.

### 2.4 Sidecar keys

The packer names the sidecars `<block>.lgi3` and `<block>.lgi4`. No reader
selects a decoder by suffix; the manifest role (`literalIndex`) and the layout
label select it. The suffix is for people.

## 3. What each reader does with a retired name

| Reader | Behaviour |
| --- | --- |
| `LiteralGramIndexWire.decode?`, `decode2?` | `none` (the magic and the version byte differ) |
| `ShardManifest.decode?` | `none` for a retired label |
| `l4block-shard-pack` (`PackStream`) | writes `.lgi3` and `.lgi4` and the new labels; guards pin that its labels pass `layoutConsistent` |
| `l4block-shard-activate`, `Wasm/Ops/Pack.activateVerify` | refuse with `retiredMessage` or `retiredLayoutNote?`; a sidecar with a retired magic under a current label is named before the generic quad failure |
| `GenerationVerify.verifyIndexSidecars` (wire versions 8 and 9) | `retiredMessage` in place of the generic literal-index failure |
| `Wasm/Ops/Store` (`storeManifestInspect`, `storeQueryPlan`, `storeQuery`, `storeOpen`) | the error carries `retiredLayoutNote?` |
| `Wasm/Ops/StoreHandles` (`storeOpen`) | a supplied literal sidecar that matches its committed SHA-256 and starts with a retired magic refuses the open. Every other sidecar problem still falls back to the scan, which is correct |
| `l4block-quad-query`, `l4block-quad-dump`, `l4block-id-v3-query` | print `retiredLayoutNote?` |
| `l4block-literal-gate` | see 4 |
| `l4block-literal-gram` (`LiteralGramProbe`) | writes the sizes of the `lgi3` and `lgi4` layouts; its filter is now the engine's `LCASE` (see 4) |

`LiteralIndexPlan` and `BlockV5Plan` decide nothing about names. Their comments
changed.

`Harness/ShardActivate.lean` held its own copies of the IBK4 and IBK5 label
strings. They are deleted; it uses `ShardManifest.isIbk4Layout` and
`isIbk5Layout`. A copy would have kept admitting the retired labels in the
activator's choice of block codec.

## 4. Two gates that could pass without testing anything

**The gate compared two scans.** `l4block-literal-gate` opens one handle with
the sidecars and one without, asks the same query of both and compares the
answer envelopes. A sidecar that fails to decode falls back to the scan, so a
broken sidecar made the gate compare two scans and pass. `storeOpen` and
`storeHandleList` now report `literalIndexes` and `geoIndexes`, the number of
retained blocks that hold a decoded index of each kind. The gate fails when the
plan names sidecars and the handle opened with them retained fewer literal
indexes than blocks, or when the handle opened without them retained any.

**The probe used the index's own fold.** `l4block-literal-gram` evaluated its
scan with `foldedOfTerm`, the function the index folds with, so the scan and
the index agreed by construction and the probe could not see a fold that had
drifted from `LCASE`. Its scan is now `Fn.String.lowerCase` followed by a
case-sensitive substring test, which is what `CONTAINS(LCASE(STR(?o)), ...)`
evaluates.

## 5. Tests

| Test | Where | What fails |
| --- | --- | --- |
| LGI3 and LGI4 bytes start with the new magic and version | `LiteralGramIndexWire.lean` `#guard` | an encoder that writes a retired name |
| Old encoder bytes are the new bytes with the header replaced | `legacyLgi1`, `legacyLgi2` `#guard` | a byte change other than the header |
| Retired bytes are refused by both decoders, with the cause | `#guard`, theorems | a decoder that admits a retired name |
| `école` reaches `École Normale` through an encoded and decoded index; so do `kelvin`, `straße` | `LiteralGramIndexWire.lean` `#guard` | an ASCII fold in the index |
| Retired labels refused at versions 0 to 10, on both sides | `ShardManifest.lean` `#guard`; `valid_layout_not_retired`, `encode?_layout_not_retired` | a label that is admitted |
| Bytes of a manifest with a retired label are refused and explained | `ShardManifest.lean` `oldV8Bytes`, `oldV9Bytes`, `oldV10Bytes` | a reader that says only "malformed" |
| The packer's labels are the manifest's labels | `PackStream.lean` `#guard` | one list edited without the other |
| A retired sidecar refuses `storeOpen`; current and absent ones do not | `StoreHandles.lean` `#guard` | a silent fallback |
| A retired sidecar fails activation with its cause | `GenerationVerify.lean` `#guard` | the generic failure |
| The index handle answers as the scan handle on a Unicode corpus, IBK4 and IBK5, with `literalIndexes` checked and the expected rows written out | `Wasm/native-smoke.sh`, `tests/local/data/unicode_label_sample.trig` | an ASCII fold in the index, or two scans compared |
| The packer writes `LGI3` and `LGI4` | `Wasm/native-smoke.sh` | a retired name written |
| `storeManifestInspect`, `storeQueryPlan` and `storeOpen` refuse a manifest with a retired label, with the cause | `Wasm/native-smoke.sh` | a generic refusal |

## 6. Results

Measured 2026-10-10 on this branch. The "before" column was measured with the
binaries of the neighbouring checkout at commit 39861602 (it has the Unicode
fold and not the rename); the suites that do not read the index do not move.

| Gate | Before | After |
| --- | --- | --- |
| `lake build`, all targets | exit 0 | exit 0 (1285 jobs) |
| `Wasm/native-smoke.sh` | 143 pass, 0 fail (out of 143) | 152 pass, 0 fail (out of 152); the 9 added cases are in section 5 |
| `l4block-literal-gate` on `tests/local/data/unicode_label_sample.trig`, IBK4 | not run: no Unicode corpus existed, and the gate could not tell an index path from a scan | 8 pass, 0 fail (out of 8) needles; every needle but `unmatched` returns 1 row |
| the same, IBK5 | not run | 8 pass, 0 fail (out of 8) |
| `tools/blockengine-ibk4-quad-smoke.sh`, `tools/blockengine-ibk5-quad-smoke.sh` | pass | pass |
| `tools/blockengine-ibk4-w3c-trig-smoke.sh`, `tools/blockengine-ibk5-w3c-trig-smoke.sh` | 242 pass, 0 fail (out of 242) each | 242 pass, 0 fail (out of 242) each |
| `tools/w3c-persisted-census.sh`, default graph (IBK3) | 551 executed, 551 matched, 0 differed (out of 555 eligible) | the same |
| the same, named graphs (IBK4) | 34 executed, 34 matched, 0 differed (out of 54 eligible) | the same |

Sabotage runs (a defect put in, the gate must fail, the defect taken out):

| Defect | What failed |
| --- | --- |
| the packer drops every gram that holds a non-ASCII character, in both formats (an index that lacks the grams the Unicode fold needs) | `l4block-literal-gate`: 5 pass, 3 fail (out of 8) on IBK4 and on IBK5 (`école`, `οδυσσευς`, `straße` differ; exit 1). `native-smoke`: 150 pass, 2 fail (out of 152), the two Unicode-fold cases |
| `storeOpen` ignores the literal sidecar bytes (every handle scans) | `l4block-literal-gate`: "retained 0 literal indexes for 1 blocks", exit 1, before any comparison |
| an encoder writes the magic of LGI1 | four `#guard`s in `LiteralGramIndexWire.lean`; the build fails |
| a decoder admits the magic and version of LGI1 | two `#guard`s; the build fails |
| `retiredName?` names LGI1 as another format | two `#guard`s; the build fails |
| the message of the `storeOpen` refusal loses its remedy | two `#guard`s in `StoreHandles.lean`; the build fails |

The census is not a conformance result: it compares the persisted path with the
in-memory engine over the same file.
