# Reuse fixed ASCII bitmap outlines

A bounded inspection of the pinned W3C Flexbox snapshot on 24 November used the November 22 Apple Silicon engine `4618bea0c1ac`. With no font held, four native hit-test calls at fresh viewport widths took 2.29, 2.62, 2.36 and 2.43 s. In the sample, 677 of 1185 layout stacks contained `bitmapOutline`. Holding Noto Sans Regular gave 2.04 s for the first request and 0.90, 0.88 and 0.87 s at the other widths. The probe supplied HTML and matched CSS, with page scripts and fetched images off. These are phase diagnostics on a local machine, with a subset of desktop inputs.

The bitmap font previously generated each character's outline for every occurrence of that character. It now shares a table of the 128 ASCII character outlines, evaluated only on the first bitmap lookup. The reference outline function still defines every entry and handles any index outside ASCII. The Lean theorem states equality of the whole ordered geometry list for each index.

This change targets Textnaut and uses of the bitmap profile. A matched before-and-after run and exact render comparisons are required before claiming a speed gain. The Noto desktop measurements identify separate cascade and layout work.
