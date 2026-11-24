# Reuse fixed ASCII bitmap outlines

A bounded inspection of the pinned W3C Flexbox snapshot on 24 November used the November 22 Apple Silicon engine `4618bea0c1ac`. With no font held, four native hit-test calls at fresh viewport widths took 2.29, 2.62, 2.36 and 2.43 s. In the sample, 677 of 1185 layout stacks contained `bitmapOutline`. Holding Noto Sans Regular gave 2.04 s for the first request and 0.90, 0.88 and 0.87 s at the other widths. The probe supplied HTML and matched CSS, with page scripts and fetched images off. These are phase diagnostics on a local machine, with a subset of desktop inputs.

The bitmap font previously generated each character's outline for every occurrence of that character. It now shares a table of the 128 ASCII character outlines, evaluated only on the first bitmap lookup. The reference outline function still defines every entry and handles any index outside ASCII. The Lean theorem states equality of the whole ordered geometry list for each index.

This change targets Textnaut and uses of the bitmap profile. A matched before-and-after run and exact render comparisons are required before claiming a speed gain. The Noto desktop measurements identify separate cascade and layout work.

## Paired Linux results

Ubuntu hosted runner, fixed November 15 snapshots, scripts disabled, baseline 51f7ce6af97b and candidate ceee9ae7950c in ABBA order. Terminal output hashes matched across all four runs on each page. W3C Flexbox measured first layout 11.487/11.490 s on baseline, 9.785/9.753 s on candidate. First frame was 13.2/13.2 s and 11.5/11.4 s respectively. Mobile US Wikipedia first layout was 89.655/89.209 s and 86.778/87.880 s. Its first frame was 92.0/91.4 s and 89.0/90.1 s. The large page remains slow. These are Textnaut results with the bitmap font, with no regular desktop font speed claim.

The native Linux build compiled the ordered geometry theorem. Selected WPT was unchanged (1,598 passing subtests of 1,911). [Paired replay](https://github.com/danbri/factoidal-builds/actions/runs/45399229169) and [native CI](https://github.com/danbri/factoidal-builds/actions/runs/45398948890).
