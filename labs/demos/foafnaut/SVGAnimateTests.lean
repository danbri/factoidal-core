import SVGAnimate

/- SVG Tiny 1.2 chapter 16 at a document time: each check reads an attribute of the
   snapshot (`NativeSVGAnimate.snapshot`). The expected values follow the rules of §16.2
   (SMIL 2.1 timing and the animation function); the comment on each names the rule. -/
open NativeSVGAnimate L4Factoidal.XML

private def doc (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' viewBox='0 0 100 100'>" ++
    body ++ "</svg>"

private def findIn (id : String) : Nat → NamespaceNode → Option (List NamespaceAttribute)
  | 0, _ => none
  | _, .other _ => none
  | fuel+1, .element _ attrs children =>
    if attrs.any (fun a => a.name.localPart == "id" && a.value == id) then some attrs
    else children.findSome? (findIn id fuel)
private def find (id : String) := findIn id 64

/-- Attribute `key` of the element `id` at time `t` ms; `"error: …"` on a refusal; `"gone"`
when the element is not in the snapshot. -/
private def at_ (body : String) (t : Int) (id key : String) : String :=
  match parseNamespaceView (doc body) >>= snapshot t with
  | .error e => "error: " ++ e
  | .ok root => match find id root with
    | none => "gone"
    | some attrs => ((attrs.find? fun a => a.name.localPart == key).map (·.value)).getD "absent"

private def r (anim : String) (base : String := "") : String :=
  s!"<rect id='r' width='10' height='10' {base}>{anim}</rect>"

-- A colour value is written as #rrggbb (red is #ff0000, CSS Color 3 §4.1).
-- §16.2.8: before the begin the base value; from the begin on the `set` value (dur indefinite).
#guard at_ (r "<set attributeName='fill' to='red' begin='1s'/>" "fill='blue'") 999 "r" "fill" == "blue"
#guard at_ (r "<set attributeName='fill' to='red' begin='1s'/>" "fill='blue'") 1000 "r" "fill" == "#ff0000"
#guard at_ (r "<set attributeName='fill' to='red' begin='1s'/>" "fill='blue'") 60000 "r" "fill" == "#ff0000"
-- §16.2.10 linear from/to; `fill="remove"` (the lacuna value) ends the effect at the end.
#guard at_ (r "<animate attributeName='x' from='0' to='100' dur='2s'/>") 500 "r" "x" == "25"
#guard at_ (r "<animate attributeName='x' from='0' to='100' dur='2s'/>" "x='7'") 2000 "r" "x" == "7"
#guard at_ (r "<animate attributeName='x' from='0' to='100' dur='2s' fill='freeze'/>") 3000 "r" "x" == "100"
-- §16.2.13 accumulate: each repetition adds the last value of the one before.
#guard at_ (r "<animate attributeName='x' from='0' to='10' dur='1s' repeatCount='2' accumulate='sum' fill='freeze'/>") 1500 "r" "x" == "15"
#guard at_ (r "<animate attributeName='x' from='0' to='10' dur='1s' repeatCount='2' accumulate='sum' fill='freeze'/>") 2500 "r" "x" == "20"
-- A fractional repeatCount freezes in the middle of the simple duration.
#guard at_ (r "<animate attributeName='x' from='0' to='10' dur='1s' repeatCount='1.5' fill='freeze'/>") 5000 "r" "x" == "5"
-- §16.2.12 additive sum adds to the base value; a to-animation goes from the base value.
#guard at_ (r "<animate attributeName='x' from='0' to='10' dur='1s' additive='sum'/>" "x='5'") 500 "r" "x" == "10"
#guard at_ (r "<animate attributeName='x' to='20' dur='1s'/>" "x='10'") 500 "r" "x" == "15"
-- by-animation is additive.
#guard at_ (r "<animate attributeName='x' by='10' dur='1s'/>" "x='5'") 500 "r" "x" == "10"
-- §16.2.11 discrete: each value for its share of the simple duration.
#guard at_ (r "<animate attributeName='visibility' values='visible;hidden' dur='2s'/>") 999 "r" "visibility" == "visible"
#guard at_ (r "<animate attributeName='visibility' values='visible;hidden' dur='2s'/>") 1000 "r" "visibility" == "hidden"
-- A value that is not interpolated steps as discrete even with calcMode linear.
#guard at_ (r "<animate attributeName='fill' values='red;none' dur='2s'/>") 1500 "r" "fill" == "none"
-- keyTimes move the values in time.
#guard at_ (r "<animate attributeName='x' values='0;10;20' keyTimes='0;0.8;1' dur='1s'/>") 400 "r" "x" == "5"
-- paced: equal speed over the distance (10 then 20).
#guard at_ (r "<animate attributeName='x' values='0;10;30' calcMode='paced' dur='3s'/>") 1000 "r" "x" == "10"
#guard at_ (r "<animate attributeName='x' values='0;10;30' calcMode='paced' dur='3s'/>") 2000 "r" "x" == "20"
-- spline: keySplines 0 0 1 1 is the straight line; 0.5 0 0.5 1 is slow at both ends.
#guard at_ (r "<animate attributeName='x' values='0;10' calcMode='spline' keySplines='0 0 1 1' dur='1s'/>") 500 "r" "x" == "5"
#guard at_ (r "<animate attributeName='x' values='0;100' calcMode='spline' keySplines='0.5 0 0.5 1' dur='1s'/>") 250 "r" "x" != "25"
-- Syncbase: b begins when a ends.
#guard at_ (r "<animate id='a' attributeName='y' from='0' to='1' dur='1s'/><animate attributeName='x' from='0' to='100' begin='a.end' dur='1s'/>") 1500 "r" "x" == "50"
#guard at_ (r "<animate id='a' attributeName='y' from='0' to='1' dur='1s'/><animate attributeName='x' from='0' to='100' begin='a.begin+0.5s' dur='1s'/>") 1000 "r" "x" == "50"
-- end cuts the active duration; freeze keeps the value at the cut.
#guard at_ (r "<animate attributeName='x' from='0' to='100' dur='10s' end='1s' fill='freeze'/>") 2000 "r" "x" == "10"
-- restart="always": a second begin starts a new interval; "never": it does not.
#guard at_ (r "<animate attributeName='x' from='0' to='100' begin='0s;0.5s' dur='1s'/>") 700 "r" "x" == "20"
#guard at_ (r "<animate attributeName='x' from='0' to='100' begin='0s;0.5s' dur='1s' restart='never'/>") 700 "r" "x" == "70"
-- An event that does not occur gives no interval.
#guard at_ (r "<set attributeName='fill' to='red' begin='click'/>" "fill='blue'") 5000 "r" "fill" == "blue"
#guard at_ (r "<set attributeName='fill' to='red' begin='load+1s'/>" "fill='blue'") 1000 "r" "fill" == "#ff0000"
-- Colours interpolate in RGB.
#guard at_ (r "<animateColor attributeName='fill' from='#000000' to='#ff0000' dur='1s'/>") 500 "r" "fill" == "#800000"
-- The sandwich: the later begin is on top; sum adds to what is below.
#guard at_ (r "<set attributeName='x' to='5'/><animate attributeName='x' from='0' to='10' begin='1s' dur='1s' additive='sum'/>") 1500 "r" "x" == "10"
-- An inherited property: to-animation from the parent's value.
#guard at_ ("<g fill='#000000'>" ++ r "<animateColor attributeName='fill' to='#ff0000' dur='1s'/>" ++ "</g>") 500 "r" "fill" == "#800000"
-- animateTransform: replace, and sum appended to the transform list.
#guard at_ (r "<animateTransform attributeName='transform' type='rotate' from='0' to='90' dur='1s'/>") 500 "r" "transform" == "rotate(45)"
#guard at_ (r "<animateTransform attributeName='transform' type='rotate' from='0' to='90' dur='1s' additive='sum'/>" "transform='translate(10 0)'") 500 "r" "transform" == "translate(10 0) rotate(45)"
-- Target by xlink:href; the animation element is not in the snapshot.
#guard at_ ("<rect id='t' width='1' height='1'/><set id='s' xlink:href='#t' attributeName='x' to='3'/>") 0 "t" "x" == "3"
#guard at_ ("<rect id='t' width='1' height='1'/><set id='s' xlink:href='#t' attributeName='x' to='3'/>") 0 "s" "x" == "gone"
-- discard (§16.2.19): the target is not in the document from the begin on.
#guard at_ (r "<discard begin='1s'/>") 999 "r" "width" == "10"
#guard at_ (r "<discard begin='1s'/>") 1000 "r" "width" == "gone"
-- Refusals name the feature.
-- animateMotion (§16.2.17): paced along the path; the motion is to the left of `transform`.
#guard at_ (r "<animateMotion path='M0 0 L10 0 L10 10' dur='2s'/>") 500 "r" "transform" == "translate(5 0)"
#guard at_ (r "<animateMotion path='M0 0 L10 0 L10 10' dur='2s'/>") 1500 "r" "transform" == "translate(10 5)"
#guard at_ (r "<animateMotion path='M0 0 L10 0 L10 10' dur='2s' rotate='auto'/>") 1500 "r" "transform" == "translate(10 5) rotate(90)"
#guard at_ (r "<animateMotion path='M0 0 L10 0' dur='1s'/>" "transform='scale(2)'") 500 "r" "transform" == "translate(5 0) scale(2)"
-- values with calcMode linear: equal time for each segment (0 to 10 is short, 10 to 40 long).
#guard at_ (r "<animateMotion values='0,0;10,0;40,0' calcMode='linear' dur='2s'/>") 1500 "r" "transform" == "translate(25 0)"
-- keyPoints: the distance along the path at each keyTime.
#guard at_ (r "<animateMotion path='M0 0 L100 0' keyPoints='0;0.8;1' keyTimes='0;0.5;1' calcMode='linear' dur='1s'/>") 250 "r" "transform" == "translate(40 0)"
-- mpath: the path of another element.
#guard at_ ("<path id='p' d='M0 0 L0 20'/>" ++ r "<animateMotion dur='1s'><mpath xlink:href='#p'/></animateMotion>") 500 "r" "transform" == "translate(0 10)"
-- Frozen at the end of the path.
#guard at_ (r "<animateMotion path='M0 0 L10 0' dur='1s' fill='freeze'/>") 5000 "r" "transform" == "translate(10 0)"
#guard (at_ (r "<animate attributeName='d' from='M0 0' to='M1 1' dur='1s'/>") 0 "r" "x").startsWith "error: animation: interpolation of d"
#guard (at_ (r "<animate attributeName='x' from='0px' to='1px' dur='1s'/>") 0 "r" "x").startsWith "error: animation: value with a unit"
#guard (at_ (r "<animate attributeName='x' from='0' to='1' begin='a.repeat(1)' dur='1s'/><animate id='a' attributeName='y' to='1' dur='1s'/>") 0 "r" "x").startsWith "error: animation: repeat event"
-- The snapshot of a shape with an animation child is drawn by the strict reader.
#guard match parseNamespaceView (doc (r "<set attributeName='fill' to='red'/>")) >>= snapshot 0 >>= (NativeSVG.parseRoot · 100 100) with
  | .ok _ => true | .error _ => false
