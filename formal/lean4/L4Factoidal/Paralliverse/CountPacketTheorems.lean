import L4Factoidal.Paralliverse.PackWireTheorems
import L4Factoidal.Paralliverse.CountTarget

namespace L4Factoidal.Paralliverse.CountTarget

/-- Kind: adapter refinement.
Says: acceptance by the actual byte decoder establishes all input facts needed by
the finite count target, including the header and each descriptor's row length.
Does not say: that a host uploaded the same packet to a physical device. -/
theorem accepted_sourceRows {src : ByteArray} {rows : StaticPack.Rows}
    (h : PackWire.decode src = .ok rows) : SourceRows (PackWire.wordView src) rows where
  limit := PackWire.decode_row_count_le h
  header := PackWire.decode_header_word h
  lengths := PackWire.decode_descriptor_length_word h

/-- Kind: finite target refinement.
Says: every accepted byte packet and valid padded lane order executes the lowered
count instructions without a buffer fault, preserving destination size and giving
the DSL's whole count memory, including the initially allocated tail.
Does not say: that WGSL text, a shader compiler, host bindings or hardware implement
these instruction semantics. -/
theorem decoded_count_eq_dsl {src : ByteArray} {rows : StaticPack.Rows}
    (h : PackWire.decode src = .ok rows) (prior : Array UInt32)
    (cap : rows.length ≤ prior.size) (lanes : List UInt32)
    (order : ValidGrid rows.length lanes) :
    ∃ out, dispatch (lowerCount .count) (PackWire.wordView src) lanes prior = .ok out ∧
      out.size = prior.size ∧ memory out = (DSL.countDispatch rows).runSeq (memory prior) :=
  count_grid_eq_dsl _ prior rows (accepted_sourceRows h) cap lanes order

#print axioms accepted_sourceRows
#print axioms decoded_count_eq_dsl

end L4Factoidal.Paralliverse.CountTarget
