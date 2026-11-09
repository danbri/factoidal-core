import L4Factoidal.FrameCost.Band
import L4Factoidal.FrameCost.Lru
import L4Factoidal.FrameCost.Model
import L4Factoidal.FrameCost.Theorems
import L4Factoidal.FrameCost.Retained
import L4Factoidal.FrameCost.Cases
import L4Factoidal.FrameCost.Tests

/-! Frame scheduling in the Foafnaut hosts as a pure model with a cost semantics, and
its cost theorems (the section `Ratchet`). `Band` and `Lru` are the engine's own
definitions: `WebDocument` imports them. Only Lean core.
Record: `docs/designissues/2026-11-08-cost-theorems.md`. -/
