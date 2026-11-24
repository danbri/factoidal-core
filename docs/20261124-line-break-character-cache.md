# Avoid binary searches for common line-break characters

Fourteen-second native samples during the scripted BBC desktop scroll stall captured hundreds of main-engine leaf samples in Unicode range-table search, alongside the line-break loop. The engine looks up both line-break and general-category information for each character before applying the contextual UAX 14 rules.

Keep a lazy 256-entry array of the exact packed values for U+0000 through U+00FF from the same tables. A lookup outside that array still calls the existing pair of binary searches. Prove that every code point returns the same pair and that the complete sequence of units is equal to running the same loop over the original lookup function. This does not change the tables, tailoring or contextual break rules.

The matching-HTML BBC desktop replay and the frozen wiki replay can check timings independently of the equality proof. Native and web conformance results are separate evidence.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712).
