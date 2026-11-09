import L4Factoidal.Rendering.Smil

/-! Checks of SMIL Animation timing and values. -/
namespace L4Factoidal.Rendering.SmilTests
open L4Factoidal.Rendering Smil

#guard clockValue "2s" == some 2000
#guard clockValue "0.5s" == some 500
#guard clockValue "250ms" == some 250
#guard clockValue "1.5min" == some 90000
#guard clockValue "01:02" == some 62000
#guard clockValue "1:00:00" == some 3600000
#guard clockValue "3" == some 3000
#guard clockValue "x" == none
#guard beginList "0s" == [.offset 0]
#guard beginList "click" == [.click none 0]
#guard beginList "tap.click+1s; 2s" == [.click (some "tap") 1000,.offset 2000]
#guard beginList "indefinite" == []
-- The latest instance at or before now.
#guard beginAt [.offset 0,.click none 0] (fun _ => [5000]) 3000 == some 0
#guard beginAt [.offset 0,.click none 0] (fun _ => [5000]) 6000 == some 5000
#guard beginAt [.click none 0] (fun _ => []) 6000 == none
-- Phases: dur 1000, repeatCount 2.
#guard phase 0 1000 (some 2000) false 500 == .active 0 500
#guard phase 0 1000 (some 2000) false 1500 == .active 1 500
#guard phase 0 1000 (some 2000) false 2000 == .removed
#guard phase 0 1000 (some 2000) true 2500 == .frozen 1 1000
#guard phase 0 1000 (some 2500) true 9000 == .frozen 2 500
#guard phase 100 1000 none true 50 == .before
#guard activeDuration 1000 none none == some 1000
#guard activeDuration 1000 (some (some 2500)) none == some 2500
#guard activeDuration 1000 (some none) none == none
#guard activeDuration 1000 (some none) (some (some 3000)) == some 3000
-- Values.
#guard valueAt #[#[1],#[40],#[1]] none false 0.25 == some #[20.5]
#guard valueAt #[#[1],#[40],#[1]] none false 1 == some #[1]
#guard valueAt #[#[0],#[10]] (some #[0,0.5]) false 0.25 == some #[5]
#guard valueAt #[#[1],#[2],#[3]] none true 0.5 == some #[2]
#guard valueList (some "1; 40; 1") none none none #[] == some #[#[1],#[40],#[1]]
#guard valueList none (some "0") (some "1") none #[] == some #[#[0],#[1]]
#guard valueList none none none (some "5") #[1] == some #[#[1],#[6]]
#guard numbers "1, -2.5 3" == some #[1,-2.5,3]
#guard (transformValue "scale" #[2]).map (fun t => (t.a,t.d)) == some (2,2)
#guard (transformValue "translate" #[3]).map (fun t => (t.e,t.f)) == some (3,0)

end L4Factoidal.Rendering.SmilTests
