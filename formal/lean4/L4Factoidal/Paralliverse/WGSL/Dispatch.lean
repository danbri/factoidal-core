import L4Factoidal.Paralliverse.WGSL.ScanSurface

/-! Finite lane dispatch shared by the packing shaders and typed word maps. -/

namespace L4Factoidal.Paralliverse.WGSL

/-- Both the binding and word write of an actual event. -/
def scatterEvent (w : Surface.Write) : (Nat × Nat) × (Nat × UInt32) :=
  ((w.group, w.slot), (w.address.toNat, w.value))

namespace TextPipeline

structure LaneTrace where
  gid : UInt32
  returnedEarly : Bool
  stores : List ((Nat × Nat) × (Nat × UInt32))

def observed (gid : UInt32) (r : ScanSurface.Outcome) : LaneTrace :=
  ⟨gid, r.returnedEarly, r.writes.map scatterEvent⟩

structure GridState where
  dst : Array UInt32
  reversed : List LaneTrace

def GridState.trace (s : GridState) : List LaneTrace := s.reversed.reverse

def GridState.record (s : GridState) (gid : UInt32) (r : ScanSurface.Outcome) : GridState :=
  ⟨r.dst, observed gid r :: s.reversed⟩

/-- Stop as soon as a lane fails or the caller supplies more IDs than the budget. -/
def dispatch (step : Array UInt32 → UInt32 → Option ScanSurface.Outcome) :
    List UInt32 → Nat → GridState → Option GridState
  | [], _, s => some s
  | gid :: rest, fuel, s =>
    match fuel with
    | 0 => none
    | k + 1 => do
      let r ← step s.dst gid
      dispatch step rest k (s.record gid r)

end TextPipeline
end L4Factoidal.Paralliverse.WGSL
