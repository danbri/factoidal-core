import L4Factoidal.GpuDomainSpecificLanguage.MapZipSurface
import L4Factoidal.GpuDomainSpecificLanguage.MapZipKind

/-! Source-bound refinement of the five production PVGraph map/zip branches.
Issue: https://github.com/danbri/factoidal-core/issues/802.
WGSL edition: https://www.w3.org/TR/2026/CRD-WGSL-20261021/.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.MapZipRefinement

open L4Factoidal.Paralliverse.WGSL
open MapZipSurface MapZipKind

private def config (i : UInt32) : Expr := .load .config (.literal i)
private def a : Expr := .load .a .gidX
private def b : Expr := .load .b .gidX

def shaderModule : MapZipSurface.Module where
  bindings := [⟨0,0,false,.a⟩,⟨0,1,false,.b⟩,
    ⟨0,2,true,.outWords⟩,⟨0,3,false,.config⟩]
  sizeX := 64
  sizeY := 1
  sizeZ := 1
  left := .gidX
  right := config 1
  arms := [
    ⟨config 0,.literal 1,.outWords,.gidX,.add a (config 2)⟩,
    ⟨config 0,.literal 2,.outWords,.gidX,.mul a (config 2)⟩,
    ⟨config 0,.literal 3,.outWords,.gidX,.xor a (config 2)⟩,
    ⟨config 0,.literal 4,.outWords,.gidX,.add a b⟩,
    ⟨config 0,.literal 5,.outWords,.gidX,.xor a b⟩]

set_option maxRecDepth 16384 in
/-- Kind: concrete syntax.
Says: the complete production shader bytes parse to these bindings, dimensions,
guard, conditions, loads, stores and arithmetic expressions.
Does not say: a platform WGSL compiler follows this parser or semantics. -/
theorem parse_source :
    MapZipSurface.parseShader MapZipShader.source.toUTF8 = some shaderModule := by
  rfl

def inputs (kind : Kind) (xs ys : Array UInt32) (n k : UInt32) : Inputs :=
  ⟨xs,ys,#[UInt32.ofNat kind.code,n,k,n,n]⟩

private def writeAt (prior : Array UInt32) (gid value : UInt32) : Option Surface.Outcome :=
  if h : gid.toNat < prior.size then
    some ⟨prior.set gid.toNat value h,[⟨0,2,gid,value⟩]⟩
  else none

private def readValue (kind : Kind) (xs ys : Array UInt32) (gid k : UInt32) : Option UInt32 := do
  let x ← xs[gid.toNat]?
  if kind.isZip then return kind.apply x (← ys[gid.toNat]?) k
  else return kind.apply x 0 k

private theorem run_header (kind : Kind) (xs ys prior : Array UInt32) (n k gid : UInt32) :
    MapZipSurface.run shaderModule (inputs kind xs ys n k) prior gid =
      if gid < n then (readValue kind xs ys gid k).bind (writeAt prior gid)
      else some ⟨prior,[]⟩ := by
  cases kind <;> rfl

/-- One active lane changes its own output word and logs that store; padded
lanes retain the entire destination and have an empty store log. -/
def laneEffect (result : List UInt32) (prior : Array UInt32) (gid : UInt32) : Surface.Outcome :=
  if h : gid.toNat < result.length then
    ⟨prior.setIfInBounds gid.toNat result[gid.toNat],
      [⟨0,2,gid,result[gid.toNat]⟩]⟩
  else ⟨prior,[]⟩

/-- Kind: source-to-reference invocation refinement.
Says: parsing and executing the actual shader performs the GraphWords result's
one store at every active lane, with no reads of data or writes on padded lanes.
Does not say: a GPU driver used the stated immutable inputs/distinct destination. -/
theorem run_source_lane (kind : Kind) (xs ys : Array UInt32) (k : UInt32)
    (small : xs.size ≤ 4194240) (lengths : xs.size = ys.size)
    (prior : Array UInt32) (room : xs.size ≤ prior.size) (gid : UInt32) :
    MapZipSurface.runText MapZipShader.source.toUTF8
      (inputs kind xs ys (UInt32.ofNat xs.size) k) prior gid =
      some (laneEffect (kind.result xs.toList ys.toList k) prior gid) := by
  have resultLength : (kind.result xs.toList ys.toList k).length = xs.size := by
    simpa using result_length kind xs.toList ys.toList k (by simpa using lengths)
  have nWord : (UInt32.ofNat xs.size).toNat = xs.size := by
    apply UInt32.toNat_ofNat_of_lt'
    change xs.size < 4294967296
    omega
  have branch : gid < UInt32.ofNat xs.size ↔ gid.toNat < xs.size := by
    rw [UInt32.lt_iff_toNat_lt,nWord]
  unfold MapZipSurface.runText
  rw [parse_source]
  dsimp only [Bind.bind, Option.bind]
  rw [run_header]
  by_cases active : gid.toNat < xs.size
  · have aRead := Array.getElem?_eq_getElem active
    have bActive : gid.toNat < ys.size := by omega
    have bRead := Array.getElem?_eq_getElem bActive
    have value : readValue kind xs ys gid k =
        some ((kind.result xs.toList ys.toList k)[gid.toNat]'(by omega)) := by
      rw [result_at kind xs.toList ys.toList k (by simpa using lengths)
        gid.toNat (by simpa using active)]
      cases kind <;> simp [readValue,Kind.isZip,Kind.apply,aRead,bRead]
    have fits : gid.toNat < prior.size := by omega
    rw [if_pos (branch.mpr active),value]
    simp only [Option.bind_some,writeAt,dif_pos fits,laneEffect,
      show gid.toNat < (kind.result xs.toList ys.toList k).length by omega,
      dif_pos,Array.setIfInBounds_def]
  · rw [if_neg (fun h => active (branch.mp h)),laneEffect]
    rw [dif_neg (by omega)]

/-- Kind: empty logical input with physical dummy storage.
Says: a zero count reads no data and writes nothing, whatever the physical input
or destination allocation contains. This covers the host's one-word empty-input
dummies without identifying their physical length with the logical zero length.
Does not say: a nonempty invocation may read outside its logical input prefix. -/
theorem run_empty_lane (kind : Kind) (physicalA physicalB prior : Array UInt32)
    (k gid : UInt32) :
    MapZipSurface.runText MapZipShader.source.toUTF8
      (inputs kind physicalA physicalB 0 k) prior gid = some ⟨prior,[]⟩ := by
  unfold MapZipSurface.runText
  rw [parse_source]
  dsimp only [Bind.bind,Option.bind]
  rw [run_header]
  simp [UInt32.lt_iff_toNat_lt]

#print axioms parse_source
#print axioms run_source_lane
#print axioms run_empty_lane

end L4Factoidal.GpuDomainSpecificLanguage.MapZipRefinement
