import L4Factoidal.FrameCost.Cases

/-! Build-time tests of the frame cost model. A wrong answer fails the build. -/
namespace L4Factoidal.FrameCost.Tests
open L4Factoidal.FrameCost

def k : Key := ⟨0,800,600,80,100,0,0,0⟩
def first : Session := (step (Session.start k 3000) .tick).1

-- The first frame lays out; then scrolls of 100 rows are shifts until the keep range ends.
#guard (step (Session.start k 3000) .tick).2.1 == .layout
#guard decisions first [.scroll 100,.scroll 100,.scroll 100,.scroll 100] == [.shift,.shift,.shift,.shift]
#guard (decisions first ((List.range 12).map fun _ => .scroll 100)).count .render == 1
-- A big jump draws one band from the kept layout and lays nothing out.
#guard (run first [.scroll 2500]).2 == ⟨0,1,800*(520+1024)*4⟩
-- A prefetched band at the edge is shown with no Lean call.
#guard decisions first [.scroll 880,.prefetch 1280,.scroll 100] == [.shift,.render,.swap]
-- Zoom, a font and a visited change each lay out once; a tick costs nothing.
#guard (run first [.zoom 110,.fontLoad,.visit 3,.tick]).2.layouts == 3
#guard (run first [.tick,.tick]).2 == 0
-- A colour-only hover repaints: no layout, one render each way.
#guard (run first [.hover 3 false,.hover 0 false]).2.layouts == 0
#guard decisions first [.hover 3 false,.hover 0 false] == [.render,.render]
-- A hover that changes geometry lays out once; on, off and on again stays at one.
#guard (run first [.hover 2 true,.hover 0 false,.hover 2 true,.hover 0 false]).2.layouts == 1
-- Zoom 110 and back: one layout. Five distinct keys in a row overflow the four slots.
#guard (run first [.zoom 110,.zoom 100,.zoom 110]).2.layouts == 1
#guard (run first [.zoom 101,.zoom 102,.zoom 103,.zoom 104,.zoom 100]).2.layouts == 5
-- The prefetch rule: the next band down starts its keep range where this one ends.
#guard prefetchTarget (band 1000 520) 520 1300 9000 true == some 1768
#guard prefetchTarget (band 1000 520) 520 1100 9000 true == none
#guard (band 1768 520).keepFrom == (band 1000 520).keepTo 520
#guard prefetchTarget (band 1000 520) 520 700 9000 false == some 232
-- The fixture has 80 cases.
#guard (Cases.output.splitOn "\n").length == 81

-- Axiom audit: each may use only propext, Classical.choice and Quot.sound.
#print axioms L4Factoidal.FrameCost.scroll_in_band_free
#print axioms L4Factoidal.FrameCost.scroll_never_layouts
#print axioms L4Factoidal.FrameCost.run_scrolls_never_layout
#print axioms L4Factoidal.FrameCost.hover_never_layouts
#print axioms L4Factoidal.FrameCost.hover_geometry_layouts
#print axioms L4Factoidal.FrameCost.layout_once_per_key
#print axioms L4Factoidal.FrameCost.layout_once_per_key_from_start
#print axioms L4Factoidal.FrameCost.layout_once_per_distinct_key
#print axioms L4Factoidal.FrameCost.band_render_bound
#print axioms L4Factoidal.FrameCost.prefetch_band_spacing
#print axioms L4Factoidal.FrameCost.prefetch_chain
#print axioms L4Factoidal.FrameCost.composite_correct
#print axioms L4Factoidal.FrameCost.tick_free
#print axioms L4Factoidal.FrameCost.prefetch_never_layouts
#print axioms L4Factoidal.FrameCost.hover_on_off_paint
#print axioms L4Factoidal.FrameCost.hover_on_off_geometry
#print axioms L4Factoidal.FrameCost.Lru.lookup_eq
#print axioms L4Factoidal.FrameCost.Lru.put_valid
#print axioms L4Factoidal.FrameCost.Lru.erase_put

end L4Factoidal.FrameCost.Tests
