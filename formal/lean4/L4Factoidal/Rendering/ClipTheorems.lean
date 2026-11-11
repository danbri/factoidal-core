import L4Factoidal.Rendering.Layout

/-! # What clips page ink

* `lower_clipped`: each primitive lowered from a clipped node carries that node's clip
  (moved into the frame of the lowering). The raster gives a primitive no coverage
  outside its clips (`NativeSVG.Primitive.coverageAt`: its clip pass comes first).
* `clipContent_clips`: with `overflow: hidden` or `clip`, every primitive of an
  element's content carries its padding box (`Layout.clipContent`).

That the backend's clip rows encode `ClipRect.contains` exactly is checked by pixel
tests, not proved here: `labs/demos/foafnaut/SVG.lean` holds the encoding. -/
namespace L4Factoidal.Rendering

/-- Every primitive of a clipped node carries the node's clip. -/
theorem lower_clipped (parent : Transform) (groups : List (Option String)) (id : Option String)
    (content : Transform) (clip : ClipRect) (children : List Node) (item : PaintItem)
    (h : item ∈ (Node.clipped id content clip children).lower parent groups) :
    clip.lowerUnder parent ∈ item.primitive.clips := by
  rw [Node.lower] at h
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
  simp [PaintItem.addClip, Primitive.addClip]

/-- `overflow: hidden` and `clip`: every primitive of the content carries the padding box. -/
theorem clipContent_clips (content : Array Node) (paddingBox : ClipRect)
    (parent : Transform) (groups : List (Option String)) (item : PaintItem)
    (h : item ∈ (Node.clipped none identity paddingBox content.toList).lower parent groups) :
    paddingBox.lowerUnder parent ∈ item.primitive.clips :=
  lower_clipped parent groups none identity paddingBox content.toList item h

/-- The clipped content is the last node `clipContent` gives, after the decorations. -/
theorem clipContent_true (decorations content : Array Node) (paddingBox : ClipRect) :
    Layout.clipContent true decorations content paddingBox =
      decorations.push (.clipped none identity paddingBox content.toList) := rfl

/-- With `overflow: visible` nothing is clipped. -/
theorem clipContent_false (decorations content : Array Node) (paddingBox : ClipRect) :
    Layout.clipContent false decorations content paddingBox = decorations ++ content := rfl

end L4Factoidal.Rendering
