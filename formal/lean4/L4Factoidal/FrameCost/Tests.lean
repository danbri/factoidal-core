import L4Factoidal.FrameCost.Cases

/-! Build-time tests of the frame cost model. A wrong answer fails the build. -/
namespace L4Factoidal.FrameCost.Tests
open L4Factoidal.FrameCost

def k : Key := ⟨0,800,600,80,100,0,0⟩
def first : Session := (step (Session.start k 3000) .tick).1

-- The first frame lays out; then scrolls of 100 rows are shifts until the keep range ends.
#guard (step (Session.start k 3000) .tick).2.1 == .layout
#guard decisions first [.scroll 100,.scroll 100,.scroll 100,.scroll 100] == [.shift,.shift,.shift,.shift]
#guard (decisions first ((List.range 12).map fun _ => .scroll 100)).count .render == 1
-- A big jump draws one band from the kept layout and lays nothing out.
#guard (run first [.scroll 2500]).2 == ⟨0,1,800*(520+1024)*4⟩
-- A prefetched band at the edge is shown with no Lean call.
#guard decisions first [.scroll 880,.prefetch 1280,.scroll 100] == [.shift,.render,.swap]
-- Zoom, a font and a hover change each lay out once; a tick costs nothing.
#guard (run first [.zoom 110,.fontLoad,.element 3,.tick]).2.layouts == 3
#guard (run first [.tick,.tick]).2 == 0
-- The fixture has 80 cases.
#guard (Cases.output.splitOn "\n").length == 81

-- Axiom audit: each may use only propext, Classical.choice and Quot.sound.
#print axioms L4Factoidal.FrameCost.scroll_in_band_free
#print axioms L4Factoidal.FrameCost.scroll_never_layouts
#print axioms L4Factoidal.FrameCost.run_scrolls_never_layout
#print axioms L4Factoidal.FrameCost.layout_once_per_key
#print axioms L4Factoidal.FrameCost.layout_once_per_key_from_start
#print axioms L4Factoidal.FrameCost.band_render_bound
#print axioms L4Factoidal.FrameCost.composite_correct
#print axioms L4Factoidal.FrameCost.tick_free
#print axioms L4Factoidal.FrameCost.prefetch_never_layouts
#print axioms L4Factoidal.FrameCost.element_change_lays_out
#print axioms L4Factoidal.FrameCost.one_entry_relayouts

end L4Factoidal.FrameCost.Tests
