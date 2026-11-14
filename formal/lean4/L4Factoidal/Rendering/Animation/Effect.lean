/-
L4Factoidal.Rendering.Animation.Effect: keyframes and the effect value of a keyframe
effect (Web Animations 1 §5.3 "keyframe effects", §5.3.3 "computing missing keyframe
offsets", §5.3.4 "the effect value of a keyframe effect").

A keyframe holds specified values as CSS text. The effect value of one property at an
iteration progress is found from the keyframes that give the property, with the
property's computed values supplied by the caller (`compute`: specified text to computed
tokens, in the context of the target element) and the underlying value for neutral
keyframes and for the `add` and `accumulate` composite operations.

Theorems: with the two keyframes `from` and `to`, the effect value at progress 0 is the
interpolation of the two values at 0 and at 1 that at 1 (`fromTo_zero`, `fromTo_one`),
whose components are those of `from` and of `to` (`Value.lerpTok_zero`, `lerpTok_one`); offsets computed for
keyframes with none are in [0, 1] when the given ones are (`spread` tests).
-/
import L4Factoidal.Rendering.Animation.Value
import L4Factoidal.Rendering.Animation.Easing

namespace L4Factoidal.Rendering.Animation
open Fix (one)

/-- Web Animations 1 §5.3.5 composite operations. -/
inductive Composite where
  | replace | add | accumulate
  deriving DecidableEq, Repr, Inhabited

def Composite.toText : Composite → String
  | .replace => "replace" | .add => "add" | .accumulate => "accumulate"

def Composite.parse : String → Option Composite
  | "replace" => some .replace
  | "add" => some .add
  | "accumulate" => some .accumulate
  | _ => none

structure Keyframe where
  /-- The offset given, in [0, 1]; none when the keyframe gives none. -/
  offset : Option Int := none
  /-- §5.3.3: the offset in use. -/
  computedOffset : Int := 0
  easing : Easing := .linear
  /-- none: `auto`, the composite operation of the effect. -/
  composite : Option Composite := none
  /-- CSS property name (lower case, or a custom property) and specified value text. -/
  props : List (String × String) := []
  deriving DecidableEq, Repr, Inhabited

namespace Effect

/-- The computed offsets of keyframes with the given offsets (§5.3.3): the first is 0 and
the last 1 when they give none (a single keyframe is 1); a run of keyframes with no
offset between two that have one is spaced evenly between them. One pass, no recursion. -/
def spread (offsets : List (Option Int)) : List Int := Id.run do
  let n := offsets.length
  match offsets with
  | [] => return []
  | [o] => return [o.getD one]
  | _ =>
    let arr := offsets.toArray
    let arr := arr.set! 0 (some ((arr[0]?.getD none).getD 0))
    let arr := arr.set! (n - 1) (some ((arr[n - 1]?.getD none).getD one))
    let mut out : Array Int := #[]
    let mut prev : Int := 0
    for idx in [0:n] do
      match arr[idx]?.getD none with
      | some o =>
        -- the keyframes with no offset since `prev` sit between `prev` and `o`
        let run := idx - out.size
        for j in [0:run] do
          out := out.push (prev + (o - prev) * (Int.ofNat (j + 1)) / (Int.ofNat (run + 1)))
        out := out.push o
        prev := o
      | none => pure ()
    return out.toList

/-- The keyframes with their computed offsets (§5.3.3). -/
def withOffsets (kfs : List Keyframe) : List Keyframe :=
  (kfs.zip (spread (kfs.map (·.offset)))).map fun (k, o) => { k with computedOffset := o }

/-- A keyframe of one property (§5.3.4 "property-specific keyframes"): its computed
value, or none for a neutral keyframe (the underlying value). -/
structure PK where
  offset : Int
  easing : Easing := .linear
  composite : Composite := .replace
  value : Option Value := none
  deriving Repr, Inhabited

/-- §5.3.4 steps 3 to 7: the keyframes of `prop` whose value computes, in offset order
(the keyframes are in offset order already), with a neutral keyframe at 0 and at 1 when
none is there. `neutralEasing` is the easing of a neutral keyframe at 0: `linear`, or the
element's timing function for a CSS animation (CSS Animations 2 §4.3). -/
def propertyKeyframes (kfs : List Keyframe) (effectComposite : Composite) (prop : String)
    (compute : String → Option Value) (neutralEasing : Easing := .linear) : List PK :=
  let own : List PK := kfs.filterMap fun k =>
    match k.props.lookup prop with
    | none => none
    | some text => (compute text).map fun v =>
        { offset := k.computedOffset, easing := k.easing, composite := k.composite.getD effectComposite, value := some v }
  let own := if own.head?.map (·.offset) == some 0 then own else { offset := 0, easing := neutralEasing, composite := .add } :: own
  if own.getLast?.map (·.offset) == some one then own else own ++ [{ offset := one, composite := .add }]

/-- §5.3.4 step 9: a keyframe's value on the underlying value. -/
def resolved (kind : Value.Kind) (underlying : Value) (k : PK) : Value :=
  match k.value with
  | none => underlying
  | some v => match k.composite with
    | .replace => v
    | .add => Value.add kind underlying v
    | .accumulate => Value.accumulate kind underlying v

/-- The last keyframe at or before `p` (and before 1) with the one after it; the first
pair when none is. A loop: the recursive call is a tail call. -/
def interval (p : Int) : List PK → Option (PK × PK)
  | a :: b :: rest =>
    if b.offset ≤ p && b.offset < one && !rest.isEmpty then interval p (b :: rest) else some (a, b)
  | _ => none

/-- §5.3.4: the effect value of `prop` at iteration progress `p`; none when the effect
gives the property no value. -/
def value (kfs : List Keyframe) (effectComposite : Composite) (prop : String) (kind : Value.Kind)
    (p : Int) (underlying : Value) (compute : String → Option Value) (neutralEasing : Easing := .linear) :
    Option Value :=
  if !kfs.any (fun k => (k.props.lookup prop).isSome) then none else
  let pks := propertyKeyframes kfs effectComposite prop compute neutralEasing
  let zeros := pks.filter (·.offset == 0)
  let ones := pks.filter (·.offset == one)
  if p < 0 && zeros.length > 1 then zeros.head?.map (resolved kind underlying)
  else if p ≥ one && ones.length > 1 then ones.getLast?.map (resolved kind underlying)
  else match interval p pks with
    | none => pks.head?.map (resolved kind underlying)
    | some (a, b) =>
      let distance := (Fix.div (p - a.offset) (b.offset - a.offset)).getD 0
      some (Value.interpolate kind (resolved kind underlying a) (resolved kind underlying b) (a.easing.eval distance))

/-- The properties an effect animates, each once, in keyframe order. -/
def properties (kfs : List Keyframe) : List String :=
  (kfs.flatMap (·.props.map (·.1))).eraseDups

/-- The two keyframes `from` and `to` of one property, as the interpolation tests and a
CSS transition make them. -/
def fromTo (prop a b : String) (easing : Easing := .linear) : List Keyframe :=
  [{ offset := some 0, computedOffset := 0, easing, props := [(prop, a)] },
   { offset := some one, computedOffset := one, props := [(prop, b)] }]

/-! ## Theorems -/

/-- The property-specific keyframes of `fromTo` when both values compute: the two
keyframes, with no neutral keyframe added. -/
theorem fromTo_pks (prop a b : String) (e : Easing) (va vb : Value)
    (compute : String → Option Value) (ha : compute a = some va) (hb : compute b = some vb) :
    propertyKeyframes (fromTo prop a b e) .replace prop compute =
      [{ offset := 0, easing := e, composite := .replace, value := some va },
       { offset := 1000000000, easing := .linear, composite := .replace, value := some vb }] := by
  simp [propertyKeyframes, fromTo, ha, hb, one, Fix.scale]

/-- Kind: effect value end point (Web Animations 1 §5.3.4). Says: for the keyframes
`from` and `to` of a property whose values compute, with any keyframe easing that maps 0
to 0 (every easing but a step function with a jump at the start), the effect value at
iteration progress 0 is the interpolation of the computed `from` and `to` values at 0
(`Value.lerpTok_zero`: the `from` components), for every kind and underlying value.
Does not say: anything of keyframes with `add` or `accumulate`. -/
theorem fromTo_zero (prop a b : String) (e : Easing) (kind : Value.Kind) (underlying va vb : Value)
    (compute : String → Option Value) (ha : compute a = some va) (hb : compute b = some vb)
    (he : e.eval 0 = 0) :
    value (fromTo prop a b e) .replace prop kind 0 underlying compute = some (Value.interpolate kind va vb 0) := by
  have h0 : (Fix.div 0 1000000000).getD 0 = 0 := by decide
  unfold value
  rw [fromTo_pks prop a b e va vb compute ha hb]
  simp [fromTo, interval, resolved, h0, he, one, Fix.scale]

/-- Kind: effect value end point. Says: for the keyframes `from` and `to` of a property
whose values compute, with any keyframe easing that maps 1 to 1, the effect value at
iteration progress 1 is the interpolation of the computed values at 1
(`Value.lerpTok_one`: the `to` components). Does not say: anything of other keyframe
lists. -/
theorem fromTo_one (prop a b : String) (e : Easing) (kind : Value.Kind) (underlying va vb : Value)
    (compute : String → Option Value) (ha : compute a = some va) (hb : compute b = some vb)
    (he : e.eval one = one) :
    value (fromTo prop a b e) .replace prop kind one underlying compute = some (Value.interpolate kind va vb one) := by
  have he' : e.eval 1000000000 = 1000000000 := he
  have h1 : (Fix.div 1000000000 1000000000).getD 0 = 1000000000 := by decide
  unfold value
  rw [fromTo_pks prop a b e va vb compute ha hb]
  simp [fromTo, interval, resolved, h1, he', one, Fix.scale]

/-! ## Tests -/

#guard spread [none, none] == [0, one]
#guard spread [none] == [one]
#guard spread [some 0, none, none, none, some one] == [0, 250000000, 500000000, 750000000, one]
#guard spread [none, some 500000000, none] == [0, 500000000, one]
#guard spread [none, none, some 600000000, none, none] == [0, 300000000, 600000000, 800000000, one]
#guard spread [some 200000000, none] == [200000000, one]

private def px (s : String) : Option Value := some (Value.parse s)
private def show_ (v : Option Value) : String := (v.map Value.toText).getD "-"

#guard show_ (value (fromTo "width" "10px" "20px") .replace "width" .generic 300000000 [] px) == "13px"
#guard show_ (value (fromTo "width" "10px" "20px") .replace "width" .generic (-300000000) [] px) == "7px"
#guard show_ (value (fromTo "width" "10px" "20px") .replace "width" .generic (one + Fix.half) [] px) == "25px"
#guard show_ (value (fromTo "width" "10px" "20px") .replace "height" .generic Fix.half [] px) == "-"
-- a neutral start keyframe: the underlying value
#guard show_ (value [{ offset := some one, computedOffset := one, props := [("width", "20px")] }] .replace "width"
  .generic Fix.half (Value.parse "10px") px) == "15px"
-- composite add on both keyframes
#guard show_ (value [{ computedOffset := 0, composite := some .add, props := [("width", "10px")] },
  { computedOffset := one, composite := some .add, props := [("width", "20px")] }] .replace "width"
  .generic Fix.half (Value.parse "100px") px) == "115px"
-- three keyframes, with the easing of the first interval
#guard show_ (value [{ computedOffset := 0, props := [("width", "0px")] },
  { computedOffset := Fix.half, props := [("width", "100px")] },
  { computedOffset := one, props := [("width", "0px")] }] .replace "width" .generic 750000000 [] px) == "50px"
#guard show_ (value [{ computedOffset := 0, easing := .steps 1 .end_, props := [("width", "0px")] },
  { computedOffset := Fix.half, props := [("width", "100px")] },
  { computedOffset := one, props := [("width", "0px")] }] .replace "width" .generic 250000000 [] px) == "0px"
#guard properties (fromTo "width" "1px" "2px") == ["width"]

end Effect
end L4Factoidal.Rendering.Animation
