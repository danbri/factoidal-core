# The QLever index format, read for Factoidal/qlvr

Date: 2026-10-11. Tracking: https://github.com/danbri/factoidal/issues/778.

Owner, 2026-10-11, verbatim: "Can we build a medium sized qlever database
instance and work up enough Lean machinery (call it Factoidal/qlvr) to be able
to access its data on disk for query, or even create/edit? This may teach us
something about Lean." and "consider tail recursive approach".

This record is stage 2 of that issue: what each file of a QLever index holds,
byte by byte, with the source line that writes it. Stage 3 (the Lean reader)
starts from the plan at the end.

## Subject of the record

| Item | Value |
| --- | --- |
| QLever source | https://github.com/ad-freiburg/qlever commit `ceace86e093c434fa6ed14c6d5a1fde6f84c1d06` (label `org.opencontainers.image.revision` of the image) |
| Image | `docker.io/adfreiburg/qlever@sha256:b2087ec92254f0ee2fca68d4c886c538f492c7740885cee9c98ada219d90c810` |
| Index format version | `{"date": "2026-09-26", "pull-request-number": 3470}` (from `olympics.meta-data.json`) |
| FSST library | QLever pins https://github.com/cwida/fsst commit `b228af6356196095eaf9f8f5654b0635f969661e` (`CMakeLists.txt:703-709`). The `fsst.h` lines cited below were read at `master` = `e638d4cf8c26129d73c242a4127b42b975de5b63`; the decoder agrees with the instance (section 2), but the two commits were not compared. |
| Instance | the `olympics` dataset, 1,781,625 triples; manifest `tests/qlvr/instance.json`; rebuild with `tools/qlvr/build-instance.sh` |
| Probe | `tools/qlvr/probe_index.py` decodes every structure below in Python. It is a format probe for this record, not an implementation. |

Citations `path:line` are relative to `src/` of the QLever commit unless they
name another root. Each claim carries one of three marks:

- **[source]** read in the source at the commit above;
- **[instance]** also confirmed on the instance, with the file offset;
- **[not confirmed]** read in the source; the instance has no data that
  exercises it.

## The index directory

`qlever index` wrote these files for base name `olympics` (sizes in bytes):

| File | Bytes | Section |
| --- | ---: | --- |
| `olympics.index.pso` | 3,306,536 | 3 |
| `olympics.index.pso.meta` | 384 | 3 |
| `olympics.index.pos` | 3,483,038 | 3 |
| `olympics.index.pos.meta` | 384 | 3 |
| `olympics.index.spo` | 3,282,780 | 3 |
| `olympics.index.spo.meta` | 32 | 3 |
| `olympics.index.sop` | 3,284,034 | 3 |
| `olympics.index.sop.meta` | 32 | 3 |
| `olympics.index.osp` | 3,544,527 | 3 |
| `olympics.index.osp.meta` | 128 | 3 |
| `olympics.index.ops` | 3,544,121 | 3 |
| `olympics.index.ops.meta` | 128 | 3 |
| `olympics.internal.index.pso` | 942,675 | 3 |
| `olympics.internal.index.pso.meta` | 128 | 3 |
| `olympics.internal.index.pos` | 912,226 | 3 |
| `olympics.internal.index.pos.meta` | 128 | 3 |
| `olympics.index.patterns` | 672 | 4 |
| `olympics.vocabulary.codebooks` | 4,616 | 2 |
| `olympics.vocabulary.words.external` | 11,783,453 | 2 |
| `olympics.vocabulary.words.external.offsets` | 4,350,072 | 2 |
| `olympics.vocabulary.words.internal` | 16,525 | 2 |
| `olympics.vocabulary.words.internal.ids` | 4,416 | 2 |
| `olympics.meta-data.json` | 807 | 5 |
| `olympics.settings.json` | 66 | 5 |
| `olympics.index-log.txt` | 4,655 | 5 (written by the qlever control script) |
| `olympics.index.resource-usage-log.tsv` | 324 | 5 (written by the control script) |
| `olympics.update-triples` | absent | 6 (only with `--persist-updates`) |

The index is about 46 MB for a 338 MB N-Triples input.

**Reproducibility [instance].** A second `qlever index` of the same input in
`/home/user/qlvr-work/instance2` gave byte-identical vocabulary files, `.meta`
files and `olympics.index.patterns`, and different bytes in every permutation
file (same sizes, same start offset of the trailing metadata). Cause: the
writer compresses and writes the column frames of different blocks
concurrently and takes each file offset with `nextOffset_.fetch_add`
(`index/CompressedRelationWriter.cpp:66`), so the order of the frames in the
file depends on thread timing. A reader must take every frame offset from the
block metadata and must not assume file order. `meta-data.json` differs too
(build date). The manifest records the sha256 of one build only.

## Serialization primitives

All multi-byte integers are little-endian, in the native x86-64 layout.

- A "trivially serializable" type is written as its raw bytes
  (`util/Serializer/Serializer.h:205-263`). `Id`, `PermutedTriple` and
  `fsst_decoder_t` are of this kind. [source]
- `std::vector<T>` and `std::string`: a `u64` element count, then the elements
  (`util/Serializer/SerializeVector.h:25-38`,
  `util/Serializer/SerializeString.h:15-16`). [instance, below]
- `std::optional<T>`: one byte `0` or `1`, then the value if `1`
  (`util/Serializer/SerializeOptional.h:18-33`). [instance, below]
- `bool`: one byte. [instance]
- The "MmapVector trailer" (`util/MmapVector.h:29-47`): 32 bytes at the end
  of a file, `u64 size, u64 capacity, u64 bytesize, u32 magic = 7601577
  (0x0073FDA9), u32 version = 0`. [instance, below]

## 1. The `Id`: 64 bits, 4-bit datatype tag

`Id` is `foldedValueId::ValueId` (`global/Id.h:19`). Bits 63..60 hold the
datatype, bits 59..0 the payload (`global/FoldedValueId.h:36-37`,
`getDatatype` at `:234-236`, `addDatatypeBits` at `:583-586`). [instance]

Tag values (`global/Datatype.h:24-49`):

| Tag | Datatype | Payload (bits 59..0) | Where | Mark |
| ---: | --- | --- | --- | --- |
| 0 | `Undefined` | always 0; the only Undefined Id is 0 (`FoldedValueId.h:241`) | query results | [source] |
| 1 | `Bool` | bit 0 = value; bit 1 = the lexical form was `0`/`1`, not `false`/`true` (`FoldedValueId.h:285-312`) | literals | [not confirmed] |
| 2 | `Int` | 60-bit two's complement, range [-2^59, 2^59-1] (`FoldedValueId.h:270-282`, `util/NBitInteger.h:19-28`) | literals; also pattern ids | [instance] |
| 3 | `Double` | IEEE 754 bits shifted right by 4: the 4 lowest mantissa bits are dropped, 49 significant bits remain (`FoldedValueId.h:254-268`) | literals | [instance] |
| 4 | `VocabIndex` | index into the vocabulary (section 2) | IRIs, literals | [instance] |
| 5 | `LocalVocabIndex` | a runtime pointer shifted right by 4 (`FoldedValueId.h:329-335`, `:361-363`) | never in index files; keys in `.update-triples` | [instance, section 6] |
| 6 | `SecondaryVocabIndex` | index into a secondary vocabulary (`index/vocabulary/SecondaryVocabulary.h`) | none here | [not confirmed] |
| 7 | `TextRecordIndex` | text index record | text index only | [not confirmed] |
| 8 | `Date` | `DateYearOrDuration` bits: 2 type bits, then a `Date` bit field or a 55-bit year, or a `DayTimeDuration` (`util/DateYearDuration.h:18-25`, `:29-41`) | `xsd:date`, `xsd:dateTime`, `xsd:gYear`, `xsd:gYearMonth`, `xsd:dayTimeDuration` | [not confirmed] |
| 9 | `GeoPoint` | two 30-bit quantised coordinates, Z-order interleaved by default (`rdfTypes/GeoPoint.h:73-121`; `geo-point-encoding` in `meta-data.json`) | WKT `POINT` literals | [not confirmed] |
| 10 | `WordVocabIndex` | text-index word | text index only | [not confirmed] |
| 11 | `BlankNodeIndex` | blank node number; printed as `_:bn<n>` (`index/ExportIds.cpp:281-283`) | blank nodes | [not confirmed]: `num-blank-nodes-total` is 0 here |
| 12 | `EncodedVal` | an IRI encoded from a configured prefix (`index/vocabulary/EncodedIriManager.h`; `encoded-iri-prefixes` in `meta-data.json`) | IRIs | [not confirmed]: only the built-in graph prefix is configured |

Ids sort by their 64 bits for every tag except `LocalVocabIndex`
(`FoldedValueId.h:82-84`), so all permutations are sorted by the unsigned
value of the `u64`. [source]

Hexdumps [instance]:

- `olympics.index.pso`, offset 3,293,082 (first triple of block 0, column 0):
  `40 17 02 00 00 00 00 40` = `0x4000000000021740`, tag 4, payload 137,024 =
  `<http://dbpedia.org/ontology/ground>`.
- In a decoded PSO column of block 3: `0x20000000000000b8` = tag 2, `Int`
  184 (a `dbo:height` value).
- `olympics.update-triples` (section 6), offset 144:
  `ea 07 00 00 00 00 00 20` = tag 2, `Int` 2026.

### Literals that become `Int`, `Double`, `Bool` or `Date`

The parser folds these literals into a value Id instead of a vocabulary entry
(`parser/RdfParser.h:227-242`, `parser/RdfParser.cpp:676-721`):

- the 12 integer datatypes `xsd:int`, `xsd:integer`, `xsd:nonPositiveInteger`,
  `xsd:negativeInteger`, `xsd:long`, `xsd:short`, `xsd:byte`,
  `xsd:nonNegativeInteger`, `xsd:unsignedLong`, `xsd:unsignedInt`,
  `xsd:unsignedShort`, `xsd:positiveInteger` become `Int`;
- `xsd:decimal`, `xsd:double`, `xsd:float` become `Double`;
- `xsd:boolean` becomes `Bool`; the date and duration types become `Date`;
  a WKT `POINT` becomes `GeoPoint`.

The Id keeps the value and drops the datatype IRI. On output an `Int` is
printed as `xsd:int`, a `Double` as `xsd:decimal` (`xsd:double` only for NaN
and the infinities), formatted with `%.1f` if the value is integral and with
`%.13g` otherwise (`index/ExportIds.cpp:233-292`). [instance]: the input has
`"70"^^xsd:double` for weights and the oracle answer
`q10-orderby-limit-double` has `"214.0"^^xsd:decimal`; `COUNT` answers are
`xsd:int` (`q01`); `q15` matches `1936` (`xsd:integer`) against
`"1936"^^xsd:int` and returns two rows, where RDF term equality returns none.
Consequence for a reader: an `Int` or `Double` Id does not determine the
literal's datatype IRI. The original lexical form and datatype are not stored
anywhere in the index.

## 2. The vocabulary

`meta-data.json` says `"vocabulary-type": "on-disk-compressed"`, which is
`CompressedVocabulary<VocabularyInternalExternal>`
(`index/vocabulary/PolymorphicVocabulary.h:50-52`) with the default
compression `FsstSquaredCompressionWrapper` and one decoder per
`NumWordsPerBlock = 2^20` words
(`index/vocabulary/CompressedVocabulary.h:39-44`). [instance]

A `VocabIndex` payload `i` is the position of the word in one sorted list of
all words: 543,754 words here (`index-log`, and the offsets trailer below).

### How an Id maps to a string

1. Read offsets `o[i]` and `o[i+1]` from `.words.external.offsets` (16 bytes at
   byte `8*i`) (`index/vocabulary/VocabularyOnDisk.cpp:24-33`). [instance]
2. Read bytes `[o[i], o[i+1])` of `.words.external`
   (`VocabularyOnDisk.cpp:37-44`). [instance]
3. Pick decoder pair `k = i / 2^20` (`CompressedVocabulary.h:702-704`).
   [instance: one pair here]
4. FSST-decode with the second decoder of the pair, then FSST-decode the
   result with the first (`util/FsstCompressor.h:104-114`; the words were
   compressed with the first, then the second,
   `index/vocabulary/CompressionWrappers.h:110-115`). [instance]
5. The result is the stored form of the term (below).

The probe does exactly this; `word[137034]` is
`<http://dbpedia.org/property/year>` and its permutation scan matches the
oracle (section 3).

### `olympics.vocabulary.codebooks`

A serialized `std::vector<FsstRepeatedDecoder<2>>`
(`CompressedVocabulary.h:249-258`, writer `:333-335`): `u64` count, then per
2^20-word block two `fsst_decoder_t` structs, each 2,304 bytes
(`FsstCompressor.h:40-79`, `:85-121`, both marked trivially serializable).
`fsst_decoder_t` (`fsst.h:80-85` in the FSST repository):

| Offset | Size | Field |
| ---: | ---: | --- |
| 0 | 8 | `version`, set to 0 by QLever (`FsstCompressor.h:52-59`) |
| 8 | 1 | `zeroTerminated` |
| 9 | 255 | `len[255]`: byte length of symbol `c` |
| 264 | 2,040 | `symbol[255]`: `u64` each, the symbol bytes in little-endian order |

[instance] file size 4,616 = 8 + 2 × 2,304. Offset 0:
`01 00 00 00 00 00 00 00` (count 1); offsets 8-15 all zero (version 0);
offset 16 `00` (`zeroTerminated` = 0); offsets 17 on: `02 02 02 ...` (`len`).

FSST decoding of one word (`fsst.h:209-219`, the portable tail loop; the
unrolled loop at `:158-197` computes the same result): read a code byte `c`;
if `c < 255` emit the first `len[c]` bytes of `symbol[c]`; if `c = 255`
(`FSST_ESC`, `fsst.h:74`) emit the next input byte unchanged. One FSST pass
expands by at most 8 (`FsstCompressor.h:65-69`). [instance]

### `olympics.vocabulary.words.external` and `.offsets`

`.words.external` is the concatenation of all compressed words, with no header
(offset of word 0 is 0). `.offsets` is `u64 o[0..n]` (n+1 entries; entry n is
the end of the last word) followed by the MmapVector trailer
(`index/vocabulary/VocabularyOnDisk.h:33-38`). [instance] trailer at offset
4,350,040: `size = 543,755`, `capacity = 543,755`,
`bytesize = 4,350,040`, magic `a9 fd 73 00`, version `00 00 00 00`.

### `olympics.vocabulary.words.internal` and `.internal.ids`

A second copy of a subset of the compressed words, held in RAM by QLever to
speed up binary search (`index/vocabulary/VocabularyInternalExternal.h:22-38`).
The subset is every word the builder flags as internal plus at least every
1,000th word (`VocabularyInternalExternal.h:124-153`).

- `.internal`: a `CompactVectorOfStrings` written by
  `CompactStringVectorWriter` (`util/CompactStringVector.h:238-298`): `u64`
  data size, the data bytes, then `u64` count and `u64` offsets (count =
  words + 1). [instance] offset 0: data size 12,093; 551 words.
- `.internal.ids`: `u64` count, then the `VocabIndex` of each internal word
  (`index/vocabulary/VocabularyInMemoryBinSearch.h:39`,
  `VocabularyInMemoryBinSearch.cpp:101-116`). [instance] offset 0:
  `27 02 00 00 00 00 00 00` (551), then 0, 1000, 2000, ... The 6 QLever
  built-in IRIs at 137,035..137,040 are flagged internal, and the
  every-1,000th positions shift to ..040 after them.

A reader that only maps Ids to strings does not need these two files.

### The stored form of a word

IRIs are stored with angle brackets. Literals are stored in QLever's
"normalized" form: `"`, the content with no escaping, `"`, then `@lang` or
`^^<datatype>` (`rdfTypes/Literal.h:41-50`). [instance] `word[0]` is
`"  Gabrielle Marie "Gabby" Adcock (White-)"@en` (inner quotes not escaped).
To print N-Triples, escape the content between the outer quotes
(`rdfTypes/RdfEscaping.h:96-103`, `validRDFLiteralFromNormalized`).

The vocabulary also holds words that are not in the input [instance]:
`<http://qlever.cs.uni-freiburg.de/builtin-functions/@en>`, `.../default-graph`
(137,036), `.../has-pattern`, `.../has-predicate`, `.../internal-graph`,
`.../langtag` (137,035-137,040), and the language-filter predicate
`@en@<http://www.w3.org/2000/01/rdf-schema#label>` (the last word, 543,753).

### Sort order

Words are sorted by `TripleComponentComparatorImpl`
(`index/vocabulary/StringSortComparator.h:307-333`): first by the first byte
(so literals `"` < IRIs `<` < `@` words), then by ICU collation of the inner
value for the index locale (`en_US`, `meta-data.json` `locale`), then
byte-wise, then by language tag or datatype. [instance: the first-byte order
holds: 0..137,022 are literals, 137,023.. are IRIs, 543,753 is the `@en@`
word.] Consequence: a byte-wise binary search over the vocabulary is not
valid. Mapping a string to its `VocabIndex` needs ICU collation, a full scan,
or an index built by the reader.

## 3. The permutations

### Which files exist

`<base>.index.<p>` with `<p>` in `pso, pos, spo, sop, osp, ops`, each with a
`.meta` file (`global/FileSuffixConstants.h:18-28`), and the internal pair
`<base>.internal.index.pso` / `.pos` (`index/Permutation.cpp:54`). With
`has-all-permutations: false` only PSO and POS exist
(`index/IndexImpl.cpp:487-493`). [instance: all eight exist]

The internal permutations hold the triples QLever adds itself [instance]:
`ql:has-pattern` (406,700 triples, subject to pattern id), `ql:langtag`
(137,023) and `@en@rdfs:label` (137,026); total 680,749
(`meta-data.json` `num-triples.internal`). Their graph column holds
`.../internal-graph`.

### Layout of a permutation file

```
[ column frames, at the offsets the block metadata gives, in any order ]
[ IndexMetaData serialization ]
[ i64 start offset of the IndexMetaData serialization ]   (last 8 bytes)
```

(`index/IndexMetaData.cpp:40-53` writes; `:63-77` and `util/File.h:260-268`
read the last 8 bytes first.) [instance] `olympics.index.pso` offset
3,306,528: `f3 3e 32 00 00 00 00 00` = 3,292,915.

`IndexMetaData` (`index/IndexMetaData.h:137-172`):

| Field | Type | [instance] PSO value, offset |
| --- | --- | --- |
| magic | `u64` = 2^64 - 3 (`IndexMetaData.h:46-47`) | `fd ff ff ff ff ff ff ff` at 3,292,915 |
| version | `u64` = 2 (`:50`) | 2 at 3,292,923 |
| name | string | 23 bytes `no index name specified` at 3,292,931 |
| blocks | vector of block metadata | 67 at 3,292,962 |
| offsetAfter | `i64`, written and ignored (`:166-169`) | |
| totalElements | `u64` | 1,781,625 |
| numDistinctCol0 | `u64` | 16 |

Block metadata (`index/CompressedRelationMetadata.h:182-205`):

| Field | Type | [instance] PSO block 0 |
| --- | --- | --- |
| column offsets | vector of `{i64 offsetInFile, u64 compressedSize}`, one per column | 6 columns; column 0 at 0, 26 bytes; column 1 at 26, 369 bytes; column 2 at 435, 2,082 bytes; ... |
| numRows | `u64` | 1,231 |
| firstTriple | 4 Ids: col0, col1, col2, graph | col0 = `dbo:ground` (137,024), graph = default graph (137,036) |
| lastTriple | 4 Ids | |
| graphInfo | optional vector of Ids | present, 1 graph (137,036) |
| containsDuplicatesWithDifferentGraphs | `bool` | 0 |
| blockIndex | `u64` | 0 |

Rerun the field-by-field hexdump with
`python3 -I tools/qlvr/probe_index.py /home/user/qlvr-work/instance olympics --dump-block0 index.pso`.

[instance] In all eight files the block metadata is sorted by first triple and
`blockIndex` equals the position; the column frame offsets are not ascending.

### Columns in a block

Every column of the block is stored, column 0 (the permutation's first key)
included. The comment at `CompressedRelationMetadata.h:57-60` says the first
key is not stored in the blocks; that comment is out of date [instance:
column 0 of every PSO block decodes to the predicate Id].

| Columns | Meaning | Permutations [instance] |
| ---: | --- | --- |
| 4 | col0, col1, col2, graph (`global/Constants.h:328-331`) | SPO, SOP, internal PSO, internal POS |
| 6 | col0, col1, col2, graph, subject pattern, object pattern (`Constants.h:333-337`, `IndexImpl.cpp:514-522`) | PSO, POS, OSP, OPS |

The pattern columns hold `Int` Ids; `Int 2147483647` (`0x7fffffff`) appears
for an object that has no pattern [instance: PSO block 3 row 0 object
pattern `0x200000007fffffff`; meaning read from the value only, not from
source].

### Column frames

Each column of each block is one zstd frame of `numRows` little-endian 8-byte
Ids, written by `ZSTD_compress` at level 3
(`util/CompressionUsingZstd/ZstdWrapper.h:21-26`,
`index/CompressedRelationWriter.cpp:58-70`). [instance] `olympics.index.pso`
offset 0: `28 b5 2f fd` (zstd magic); every one of the 1,860 frames in the
eight files decompresses to exactly `8 * numRows` bytes.

zstd features used [instance, all 1,860 frames]: single-segment frames with
the content size in the header, no checksum, no dictionary. All 4,208 zstd
blocks are of type Compressed (none Raw or RLE). Their literal sections are
Raw (3,085), Huffman-compressed (795) and treeless (328). A reader therefore
needs the full RFC 8878 decoder: Huffman literals, FSE-coded sequences and
repeat offsets.

**Decoded in Lean (stage 3 step 1, 2026-10-11).**
`formal/lean4/L4Factoidal/Codec/Zstd.lean` is a pure-Lean RFC 8878 decoder:
frames (several per input, skippable frames skipped, a non-zero dictionary id
refused), Raw/RLE/Compressed blocks, the four literal section types with 1 or
4 Huffman streams, Huffman weights direct or FSE-coded, the four table modes
for the three sequence codes, repeat offsets, and the content checksum (XXH64
in Lean, checked when the frame has one). `lake exe l4qlvr-zstd-check blocks`
decodes every column frame of the instance and compares the sha256 with
libzstd's output (`probe_index.py --zstd-tsv` writes the list). Measured
2026-10-11, linux x86_64, 4 cores, Lean 4.33.1:

| What | Result |
| --- | --- |
| column frames | 1,860 pass, 0 fail (out of 1,860) |
| zstd blocks decoded | 4,208, all Compressed; literal sections Raw 3,085, Huffman 795, treeless 328 (the same counts as the probe above) |
| sequences executed | 17,581,843 |
| Lean decode time, all frames | 4,413 ms for 499,663,936 output bytes from 22,232,169 compressed bytes: 113 MB/s of output |
| libzstd 1.5.7 (`tools/qlvr/zstd_bench.py`, best of 5) | 280 ms: 1,785 MB/s, 16 times the Lean rate |
| peak RSS of `l4qlvr-zstd-check blocks` (VmHWM) | 21,444 kB (one permutation file in memory at a time, one frame decoded at a time) |
| one 9,600,000-byte frame (tests/stack `zstd-8mib`) | 213 ms, peak RSS 33,480 kB; ran under `LEAN_STACK_SIZE_KB=512` |

Committed vectors (`formal/lean4/Harness/TestData/zstd`, 32 KB, written by
`tools/qlvr/zstd_vectors.py` with libzstd 1.5.7 at levels 1, 3 and 19, with
and without checksum, empty, RLE, raw, 300 KiB multi-block, two frames with a
skippable frame): 14 pass, 0 fail (out of 14). Seven small ones are `#guard`s
in `L4Factoidal/Codec/ZstdTests.lean`, with the XXH64 reference values and
refusal cases (every truncation of one frame, a flipped checksum, wrong magic,
a dictionary id).

### Relations and the `.meta` files

A "relation" is the run of triples with one col0 value. A relation with at
least `index-rows-per-block` rows (31,250 here, `meta-data.json`) is large: it
gets blocks of its own and an entry in `.meta`. Smaller relations share blocks
and have no `.meta` entry
(`index/CompressedRelationPermutationWriterImpl.h:595`, `:763`).

`.meta` (`index/MetaDataHandler.cpp:28-53`): an array of 32-byte entries
sorted by col0 (`CompressedRelationMetadata.h:252-258`): `Id col0`,
`u64 numRows`, `f32 multiplicityCol1`, `f32 multiplicityCol2`,
`u64 offsetInBlock` (2^64 - 1 for a large relation), then the MmapVector
trailer. [instance] `olympics.index.pos.meta`: 11 entries + trailer = 384
bytes; entry 0 at offset 0 is col0 `0x4000000000021741` (137,025,
`dbo:height`), numRows `0x18d00` = 101,632; trailer at 352: size 11,
bytesize 352, magic 7,601,577. `spo.meta` and `sop.meta` have no entries:
no subject has 31,250 triples.

### A scan for one bound col0 value

Read the trailing metadata; select the blocks with
`firstTriple.col0 <= x <= lastTriple.col0`; decompress columns 0, 1, 2 (and 3
if graphs matter) of each; keep the rows with column 0 = `x`. [instance] the
probe's PSO scan for `dbp:year` (a small relation: 51 rows in shared block 14,
which holds 103 rows) gives the 51 rows of oracle `q03`; the scan for
`wso:medal` (a large relation: blocks 42 and 43, 31,250 + 8,518 rows) gives
13,293 Bronze, 13,369 Gold and 13,106 Silver, as oracle `q12`. The `.meta` entry is not needed for a scan; it gives the row count
without decompressing.

## 4. `olympics.index.patterns`

Written at `index/PatternCreator.cpp:103-116`, read at `:123-144`:
`PatternStatistics` (`index/PatternCreator.h:56-60`): `f64`
avgNumDistinctPredicatesPerSubject, `f64` avgNumDistinctSubjectsPerPredicate,
`u64` numDistinctSubjectPredicatePairs; then a `CompactVectorOfStrings<Id>`
(vector of Ids, then vector of `u64` offsets), one "string" of predicate Ids
per pattern, ordered by pattern id. [instance] offset 0: 4.2359, 107,671.875;
offset 16: 1,722,750; offset 24: 63 Ids; offset 536: 16 offsets (15 patterns
+ 1). A pattern id is the `Int` payload in the `ql:has-pattern` triples and in
the pattern columns.

## 5. JSON and log files

- `olympics.meta-data.json` [instance]: build date, `git-hash` `ceace86`,
  `index-format-version`, `index-rows-per-block` 31,250, `locale`,
  `vocabulary-type`, `has-all-permutations`, `encoded-iri-prefixes`,
  `geo-point-encoding`, `graphNameManager`, `num-blank-nodes-total`
  (`IndexImpl.cpp:72-73`, `:526-527`), and normal/internal counts of triples,
  subjects, predicates and objects (`IndexImpl.cpp:535-546`, `:2056-2130`).
  A reader checks `index-format-version` and `vocabulary-type` before it
  decodes anything else.
- `olympics.settings.json`: the `SETTINGS_JSON` of the Qleverfile
  (`FileSuffixConstants.h:30-31`).
- `olympics.index-log.txt` and `olympics.index.resource-usage-log.tsv`: logs
  from the control script (`FileSuffixConstants.h:45-49`). Not index data.

## 6. Updates: `olympics.update-triples`

SPARQL Update in QLever does not change the permutation files. The server
keeps inserted and deleted triples in memory ("delta triples") and, with
`--persist-updates`, rewrites `<base>.update-triples` after each update
(`index/DeltaTriples.cpp:654-677`; atomic via a `.tmp` file and rename). The
graph-name state goes to `<base>.allocated-graphs-state`
(`FileSuffixConstants.h:38-43`).

Layout (`util/Serializer/TripleSerializer.h:31-35`, `:48-53`, `:77-91`,
`:142-146`): magic `QLEVER.UPDATE` (13 bytes), `u16` format version 1; the
local vocabulary: a vector of blank-node blocks, `u64` word count, then per
word an `Id` (tag 5, used only as a key) and a string in the stored form of
section 2; then the Id ranges: deleted triples, then inserted triples, each a
vector of Ids, 4 Ids (s, p, o, graph) per triple. On load, every
`LocalVocabIndex` Id is remapped through the keys
(`TripleSerializer.h:159-176`). Only non-internal delta triples are written
(`DeltaTriples.cpp:658-661`).

[instance] An `INSERT DATA` of two triples into a copy of the index
(`instance2`, server started with `--persist-updates`) wrote 192 bytes:
offset 0 `51 4c 45 56 45 52 2e 55 50 44 41 54 45` (`QLEVER.UPDATE`); offset
13 `01 00`; offset 15: 0 blank-node blocks; offset 23: 2 words; offset 31: key
`0x500007fc3092131e`, string `"qlvr test"@en`; then key, string
`<http://example.org/qlvr/s>`; the deleted range has 0 Ids, the inserted range
8 Ids. Inserted triple 1 at offset 128: s = local key, p = `0x400000000002174a`
(137,034, `dbp:year`), o = `0x20000000000007ea` (`Int` 2026), g =
`0x400000000002174c` (default graph).

This file is the smallest write path into a QLever index: a writer that emits
it changes what the server answers after a restart, with no change to the
permutations or the vocabulary. [not confirmed: a file written by anything
other than QLever has not been loaded.]

## Read from Lean (stage 3 step 2, 2026-10-11)

`formal/lean4/L4Factoidal/Qlvr/` reads the instance far enough to answer a
bound-predicate scan and to print every triple. The native executable
`l4qlvr` (`formal/lean4/Harness/Qlvr.lean`) has four commands: `stats`,
`scan INDEXDIR PRED-IRI`, `dump INDEXDIR` and `words INDEXDIR`. The tests are
`tests/qlvr/run.sh` and the `qlvr-dump` case of `tests/stack/run.sh`.

| Module | Content |
| --- | --- |
| `Qlvr.Id` | the `Id`: tag and payload, `Int` sign extension, `Double` bits, `Bool` bits; `Value` for all 13 tags |
| `Qlvr.Format` | QLever's lexical forms: `%.1f` / `%.13g` for `Double` computed exactly from the binary64 bits with `Nat` arithmetic (round half to even on the exact value), `xsd:int` for `Int`, `true`/`false`/`1`/`0` for `Bool` |
| `Qlvr.Fsst` | the 2,304-byte `fsst_decoder_t` and the decode loop |
| `Qlvr.Vocab` | codebooks, offsets with the MmapVector trailer, `vocabWord`, `findWord` (string to `VocabIndex`) |
| `Qlvr.Perm` | the trailing `IndexMetaData`, block metadata, `.meta` relations, `decodeColumn` (zstd through `Codec.Zstd`) |
| `Qlvr.Term` | an `Id` as an N-Triples term with QLever's literal escaping |
| `Qlvr.Scan` | `scanCol0M` over a fetch function (positioned reads or memory), `scanPredicate`, block and scan rendering |

### What the Lean reader confirmed [instance]

- Section 1: `Int` (60-bit two's complement), `Double` (bits shifted right by
  4) and `VocabIndex` decode as stated; QLever's printing of `Double` is
  reproduced byte for byte (all 100,666 `dbo:weight` values; `q20` below).
- Section 2: every one of the 543,754 words decodes (FSST with the second
  decoder, then the first) to the same bytes as the Python probe; after the
  escaping of `validRDFLiteralFromNormalized`, sha256 of the listing
  `67e3669c...1859` is equal on both sides. The first-byte order holds for
  the whole vocabulary: a binary search on the first byte finds the IRI range
  137,023..543,752.
- Section 3: all eight permutation files parse; in each, the rows of the
  blocks add up to `totalElements` (1,781,625 normal, 680,749 internal);
  blocks are sorted by col0 and `blockIndex` equals the position. Columns per
  block: 6 for PSO, POS, OSP, OPS; 4 for SPO, SOP and the internal pair.
- The dump of SPO, as a set of lines, is equal to QLever's own
  `CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }` in N-Triples: 1,781,625 equal,
  0 different.

### Tests (2026-10-11, linux x86_64, 4 cores, Lean 4.33.1)

| Test | Result |
| --- | --- |
| (a) scan against the oracle, every single bound-predicate query (`q03`, and `q19`, `q20`, `q21` added for this step): rows as multisets of RDF terms, numbers by value | 4 pass, 0 fail (out of 4) |
| (b) dump against the input `olympics.nt` (1,781,625 lines, all distinct) | 1,680,959 equal byte for byte; 100,666 equal after normalisation, all of class `double` (`"70"^^xsd:double` printed as `"70.0"^^xsd:decimal`); 0 different |
| (c) every vocabulary word against the Python probe | equal (543,754 words) |
| (d) `stats` | runs; block rows equal `totalElements` in all eight files |
| (e) dump against QLever's CONSTRUCT | 1,781,625 equal, 0 different |
| `tests/stack` `qlvr-dump` under `LEAN_STACK_SIZE_KB=512` | ran (control passed) |
| `#guard`s | `Id` hexdumps of section 1; 18 `%.13g`/`%.1f` cases against C `printf`; FSST table; literal escaping; refusals |

The input has only `xsd:int` (282,287) and `xsd:double` (100,666) typed
literals, no blank nodes, no `Bool` and no `Date`: those parts of section 1
remain [not confirmed] by data. Printing a `Date`, `GeoPoint`, `EncodedVal`
or `LocalVocabIndex` Id is refused with an error; `#guard`s in
`Qlvr/Term.lean` assert the refusal, so they fail when printing is added.
Tracking: https://github.com/danbri/factoidal/issues/778.

### Measurements

Time is wall-clock inside `l4qlvr` (`IO.monoNanosNow`); peak RSS is VmHWM.

| Command | Time | Peak RSS |
| --- | ---: | ---: |
| `stats` (8 metadata trailers by `pread`, 8 `.meta` files, vocabulary load) | 9-77 ms | 27 MB |
| `scan dbp:year` (51 rows, 1 PSO block of 67) | 7 ms | 28 MB |
| `scan wso:medal` (39,768 rows, 2 blocks) | 200 ms | 46 MB |
| `scan rdfs:label` (137,026 rows, 5 blocks) | 0.9-1.0 s, of which 355-637 ms vocabulary lookup | 67 MB |
| `dump` (1,781,625 triples, 39 SPO blocks, 338 MB of N-Triples) | 4.4-5.2 s | 49 MB |
| `words` (543,754 words) | 755 ms | 47 MB |
| QLever `CONSTRUCT { ?s ?p ?o }` over HTTP, N-Triples, same machine | 3.3-3.9 s | (server) |

The peak RSS is the three vocabulary files (16 MB, read whole) plus one
block's columns and its rendered text. The dump writes one block at a time
and never holds the graph. Of the dump time, zstd is about 0.4 s (three
columns of 39 blocks at the 113 MB/s of section 3); the rest is FSST decode,
term rendering and output.

**Vocabulary lookup cost.** `findWord` uses only the first-byte order: a
binary search (20 decodes) finds the range of words with the target's first
byte, then a linear scan decodes each word of the range until a match. For
an IRI the range is 406,730 words. Measured: `dbp:year` (word 137,034) 12
decodes, under 1 ms; `rdfs:label` (543,747) 406,725 decodes, 355-637 ms;
`foaf:gender` (543,751) 420 ms. A side index removes the scan: a file
written once by the reader, holding the words' hashes (or the words) sorted
byte-wise with their `VocabIndex`, searched by binary search; it must be
rebuilt when the vocabulary changes, and it needs a format version of its
own. The other option is an implementation of the ICU collation subset that
the data needs (section 2, "Sort order"), which is also what a vocabulary
writer needs.

### What this taught about Lean

- **One scan, two I/O models.** `scanCol0M` is written once over a fetch
  function `Nat → Nat → m ByteArray` in `ExceptT String m`. With `m = IO` and
  `pread` it reads only the selected blocks' frames; with `m = Id` and
  `ByteArray.extract` it is the pure `scanPredicate`. The `for` loop over
  blocks runs in the monad (per block, not per row); every per-row loop is a
  pure tail call outside it.
- **Loop shape.** Every input-proportional loop (`Fsst.decodeLoop`,
  `escapeLoop`, `lastQuote`, `collectRows`, `renderLoop`, `renderPairs`,
  `renderWords`, `scanRange`, `findFirstByte`) has a fuel `Nat` first, all
  state as arguments, and the self-call last in an `if`/`match` chain whose
  other branches return `.ok`/`.error`. All compile to `goto _start`;
  `tools/lean-tail-recursion-audit.py` finds no recursive declaration in
  `L4Factoidal/Qlvr/*` or `Harness/Qlvr.lean`, and the dump runs under the
  512 KB canary stack. A `match` on two `Except` values before the self-call
  (`renderLoop`) does not stop the jump.
- **ByteArray sharing.** `renderLoop` keeps the rendered bytes of the
  previous subject and predicate as arguments, so a run of equal Ids in SPO
  order is decoded once. Those cached arrays are shared, but they are only
  ever the SOURCE of an append (`acc ++ sb`); the accumulator stays unique
  and grows in place. FSST appends a symbol with
  `syms.copySlice (8 * c) out out.size n false`: the decoder table and the
  output are different objects, so the output is not copied.
- **No C `printf` in Lean.** `toString (70.0 : Float)` is `70.000000`; no
  core function gives `%g`. `Format.fmtG` computes `%.13g` exactly from the
  bits with `Nat` (numerator, denominator, scaled by a power of 10, rounded
  half to even); a 1,074-bit subnormal is a few `Nat` multiplications.
- **Elaboration traps.** (1) A local `structure Id` shadows the `Id` monad
  inside the namespace: `(m := Id)` failed to type-check and needed
  `_root_.Id`. (2) `meta` is a keyword in Lean 4.33: a field named `meta`
  failed to parse. (3) `(4 <<< 60) ||| x` with `x : UInt64` failed: the
  literal is elaborated as `Nat` first; it needs `(4 : UInt64)`.
- **What was slow.** The vocabulary lookup by scan (above). The dump is
  1.3-1.6 times QLever's CONSTRUCT over HTTP, with no tuning.

### What remains

For BGP queries (stage 4): a side index or collation for string to `Id`;
folding a query's numeric constants into `Int`/`Double` Ids as the parser
does (`q15` matches `1936` against `"1936"^^xsd:int`); choosing among the six
permutations by the bound positions (bound subject: SPO, bound object: OSP or
OPS); joins over the sorted columns (merge join when the join variable is the
sort key, otherwise hash join); the graph column; the internal permutations
for the language-filter predicate (`@en@rdfs:label`); delta triples from
`.update-triples` merged into each scan; positioned reads for the vocabulary
files instead of reading them whole; `Date` and `GeoPoint` printing.

For writing (stage 5): a writer of `<base>.update-triples` (section 6): the
magic and version, the local vocabulary (a key `Id` with tag 5 and the stored
form of each new word), then the deleted and inserted triples as `Id`
vectors. Existing terms need their `VocabIndex` (the side index above), new
terms go into the local vocabulary, numeric literals are folded into value
Ids. The test is to start the server with `--persist-updates` on a copy of
the index with the written file and compare its answers.

## Plan for stage 3: a Lean reader (Factoidal/qlvr)

Goal of stage 3: from Lean, decode the PSO scan for one bound predicate of the
instance and print the triples as N-Triples, equal (as RDF terms, see
"Datatypes" below) to the probe's output and to the input file, for
`dbp:year` (small relation, shared block) and `wso:medal` (large relation,
two blocks).

### Modules (proposed under `formal/lean4/L4Factoidal/Qlvr/`)

| Module | Content | Input-proportional loop? |
| --- | --- | --- |
| `Bytes` | little-endian `u64`/`i64`/`f32` at an offset of a `ByteArray` | no |
| `Id` | tag and payload; `Int` (60-bit sign extension), `Double` (shift left 4), `Bool`; total, no I/O | no |
| `Meta` | the trailing `IndexMetaData` of a permutation file; the `.meta` array; the MmapVector trailer | yes: over blocks, over columns, over entries |
| `Zstd` | RFC 8878 frame decoder: frame header, block loop, literals section (raw, RLE, Huffman with 1 or 4 streams, treeless), Huffman table from FSE-coded weights, sequences section (predefined, RLE, FSE, repeat modes), sequence execution with repeat offsets and match copy | yes: blocks, the backward bit reader, literal decode, sequence decode, match copy |
| `Column` | a decompressed frame to `Array UInt64` | yes: over rows |
| `Fsst` | `fsst_decoder_t` parse (fixed 2,304 bytes) and the decode loop | yes: over code bytes |
| `Vocab` | codebooks file, the offsets lookup, word = FSST(d1, FSST(d2, bytes)) | yes: codebook count; the scan over all words for string-to-Id |
| `Scan` | block selection and row filter for one col0 | yes: over blocks and rows |
| `NTriples` | stored form to N-Triples: escape the literal content | yes: over characters |

Every loop over input-proportional data is a tail call with an accumulator or
a `for`/`while` loop (in `Id.run do` or `IO`), never one stack frame per item
(CLAUDE.md, 2026-10-11). Gates: `python3 tools/lean-tail-recursion-audit.py --gate` (read
the exit code), and a `tests/stack` case per loop at a size above any wasm
stack limit: a full 31,250-row column through `Zstd` and `Column`, a
synthetic 1 MB word through `Fsst`, and the 543,754-word scan through `Vocab`.

File access: native `pread` through the existing FFI shim
`formal/lean4/ffi/block_pread.c` (`l4_block_pread`), so a scan reads the
trailer, then only the frames of the selected blocks. Reading whole files
into memory works for this 46 MB instance but is not the target (CLAUDE.md,
2026-10-11, "As for all in memory ...").

### Tests and oracles

- Lean scan of `dbp:year` and `wso:medal` against
  `tools/qlvr/probe_index.py --scan` output and against oracle answers `q03`
  and `q12` in `/home/user/qlvr-work/oracle/` (manifest
  `tests/qlvr/instance.json`).
- Differential zstd test: Lean `Zstd` against the `zstandard` Python package
  over all 1,860 frames of the instance (sha256 equality). Landed 2026-10-11:
  1,860 pass, 0 fail (out of 1,860); see "Column frames".
- Negative tests: truncated frame, wrong magic, `blockIndex` out of order,
  `index-format-version` other than 2026-09-26/3470: each is an error with a
  message, never a crash.

### What is hard

1. **zstd.** Every frame uses Compressed blocks with FSE and Huffman, so a
   reader needs a complete RFC 8878 decoder. The repository has a pure-Lean
   DEFLATE decoder (`L4Factoidal/Codec/Inflate.lean`, 215 lines) and no zstd
   code (search of `formal/lean4` for `zstd`: no match). Options: (a) a
   pure-Lean RFC 8878 decoder, total, every loop bounded, several times the
   size of `Inflate.lean`; it runs in the wasm build with no new C; (b) a C
   shim to `libzstd` `ZSTD_decompress` in `formal/lean4/ffi/`, as for HACL\*
   (`hacl_*.c`) and `block_pread.c`: fast, native only unless libzstd is
   compiled into the wasm build, and a new trust-surface entry. Proposal: (a)
   as the reference decoder, (b) optional for speed, with the differential
   test above between them. Whether a pure-Lean zstd decoder exists outside
   this repository was not checked. **Done for (a), 2026-10-11:**
   `L4Factoidal/Codec/Zstd.lean` (723 lines), 113 MB/s of output
   against libzstd's 1,785 MB/s on this instance. (b) is not done.
2. **String to Id.** The vocabulary is in ICU collation order (section 2).
   Lean has no ICU. A bound term in a query needs its `VocabIndex`: stage 3
   uses a full scan (543,754 words); a later stage builds its own sorted or
   hashed side index, or implements the collation subset the data needs.
   Writing a vocabulary (create/edit) needs the same collation, so a full
   writer is harder than a reader; the `.update-triples` file (section 6)
   avoids it for small edits.
3. **Datatypes and number formatting.** `Int` and `Double` Ids do not keep
   the input datatype IRI, and QLever prints them as `xsd:int` and
   `xsd:decimal` with C `printf` formats `%.1f`/`%.13g`
   (`index/ExportIds.cpp:256-276`). The Lean reader cannot reproduce the input
   lexical form; it must choose a datatype (`xsd:int` for `Int`, `xsd:double`
   or `xsd:decimal` for `Double`) and compare by value with the input, and
   needs a `%.13g` formatter to equal QLever's SPARQL JSON answers byte for
   byte. The 4 dropped mantissa bits of `Double` also change values that have
   more than 49 significant bits.

FSST (a 255-entry table and a byte loop) and the fixed-layout metadata are
small by comparison.
