/-
L4Factoidal.Unicode.LineBreak — the Unicode Line Breaking Algorithm, UAX #14
revision 57, Unicode 18.0.0, section 6 (rules LB1 to LB31; no pair table)
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

LB1 resolves AI, SG, XX to AL, SA to CM (Mn or Mc) or AL, CJ to NS.
LB9 and LB10 are applied first, when the text is cut into units: a unit is a
base character with the CM and ZWJ characters that follow it (LB9), or a lone
CM or ZWJ, which is AL with East_Asian_Width Na (LB10). The rules LB4 to LB31
then run, in the order of the specification, on each pair of adjacent units
in one forward pass; the look-behind over SP* and over NU (SY | IS)* and RI
runs is kept in a few counters, so the pass is a loop over the units with no
recursion and no backward scan. `breaks cs` lists the positions, as numbers
of code points before the break, where a break is allowed or mandatory;
the end of the text (LB3) is always listed and position 0 (LB2) never.
-/
import L4Factoidal.Unicode.LineBreakData

namespace L4Factoidal.Unicode.LineBreak
open LineBreakData

/-- One unit of LB9: the properties of its base character. -/
structure LBUnit where
  cls : UInt8
  ea : Bool       -- East_Asian_Width in {F, W, H}
  pi : Bool       -- class QU and General_Category Pi
  pf : Bool       -- class QU and General_Category Pf
  epCn : Bool     -- Extended_Pictographic and General_Category Cn
  zwj : Bool      -- the last character of the unit is ZWJ
  dc : Bool       -- the base is U+25CC DOTTED CIRCLE
  start : Nat     -- index of the first character
  deriving Inhabited

/-- Classes that a following CM or ZWJ does not attach to (LB9). -/
@[inline] def noAttach (k : UInt8) : Bool :=
  k == cBK || k == cCR || k == cLF || k == cNL || k == cSP || k == cZW

/-- The class of a character after LB1. -/
@[inline] def resolve (raw : UInt8) (gc : UInt8) : UInt8 :=
  if raw == cAI || raw == cSG || raw == cXX then cAL
  else if raw == cSA then (if gc == 2 then cCM else cAL)
  else if raw == cCJ then cNS
  else raw

/-- Cut the text into units (LB1, LB9, LB10). A character that attaches to the
previous unit gets no break before it. -/
def units (cs : Array Char) : Array LBUnit := Id.run do
  let mut us : Array LBUnit := Array.mkEmpty cs.size
  for i in [0:cs.size] do
    let c := cs[i]!
    let v := lbTable.get c.val
    let gc := gcTable.get c.val
    let k := resolve (v &&& 63) gc
    if (k == cCM || k == cZWJ) && us.size > 0 && !noAttach (us[us.size - 1]!).cls then
      us := us.modify (us.size - 1) fun u => { u with zwj := k == cZWJ }
    else if k == cCM || k == cZWJ then
      -- LB10: a lone CM or ZWJ is U+0041 (AL, Na, Lu, not Extended_Pictographic)
      us := us.push { cls := cAL, ea := false, pi := false, pf := false, epCn := false,
                      zwj := k == cZWJ, dc := false, start := i }
    else
      us := us.push { cls := k, ea := v &&& 0x40 != 0, pi := k == cQU && gc == 3,
                      pf := k == cQU && gc == 4, epCn := v &&& 0x80 != 0 && gc == 1,
                      zwj := false, dc := c.val == 0x25CC, start := i }
  return us

private def sot : UInt8 := 255   -- no unit (start of text); also eot

@[inline] private def isHyph (k : UInt8) : Bool := k == cHY || k == cHH
@[inline] private def isALHL (k : UInt8) : Bool := k == cAL || k == cHL
@[inline] private def isJamo (k : UInt8) : Bool :=
  k == cJL || k == cJV || k == cJT || k == cH2 || k == cH3
@[inline] private def isAkAs (u : LBUnit) : Bool := u.cls == cAK || u.cls == cAS || (u.cls == cAL && u.dc)
@[inline] private def isAkDc (u : LBUnit) : Bool := u.cls == cAK || (u.cls == cAL && u.dc)

/-- Break flags, one per character: `true` at index `i` when a break is
allowed between character `i - 1` and character `i`. -/
def breakFlags (cs : Array Char) : Array Bool := Id.run do
  let us := units cs
  let m := us.size
  let mut flags : Array Bool := Array.replicate cs.size false
  -- state after the previous unit
  let mut ns : UInt8 := sot        -- class of the last unit that is not SP
  let mut nsPre : UInt8 := sot     -- class of the unit before that one
  let mut nsPi : Bool := false     -- that unit is QU with Pi
  let mut nuRun : Bool := false    -- the units end in NU (SY | IS)*
  let mut nuClose : Bool := false  -- the units end in NU (SY | IS)* (CL | CP)
  let mut riCount : Nat := 0       -- length of the run of RI units
  for u in [0:m] do
    let c := us[u]!
    if u > 0 then
      let p := us[u - 1]!
      let pc := p.cls
      let cc := c.cls
      let n1 := if u + 1 < m then us[u + 1]! else default
      let n1c := if u + 1 < m then n1.cls else sot
      let n2c := if u + 2 < m then (us[u + 2]!).cls else sot
      let pp := if u ≥ 2 then (us[u - 2]!) else default
      let ppc := if u ≥ 2 then pp.cls else sot
      -- true: break allowed; the first rule that applies decides
      let brk : Bool :=
        if pc == cBK then true                                                     -- LB4
        else if pc == cCR && cc == cLF then false                                  -- LB5
        else if pc == cCR || pc == cLF || pc == cNL then true                      -- LB5
        else if cc == cBK || cc == cCR || cc == cLF || cc == cNL then false        -- LB6
        else if cc == cSP || cc == cZW then false                                  -- LB7
        else if ns == cZW then true                                                -- LB8
        else if p.zwj then false                                                   -- LB8a
        else if cc == cWJ || pc == cWJ then false                                  -- LB11
        else if pc == cGL then false                                               -- LB12
        else if cc == cGL && !(pc == cSP || isHyph pc) then false                  -- LB12a
        else if cc == cCL || cc == cCP || cc == cEX || cc == cSY then false        -- LB13
        else if ns == cOP then false                                               -- LB14
        else if nsPi && (nsPre == sot || nsPre == cBK || nsPre == cCR || nsPre == cLF
                  || nsPre == cNL || nsPre == cOP || nsPre == cQU || nsPre == cGL
                  || nsPre == cSP || nsPre == cZW) then false                      -- LB15a
        else if c.pf && (n1c == sot || n1c == cSP || n1c == cGL || n1c == cWJ || n1c == cCL
                  || n1c == cQU || n1c == cCP || n1c == cEX || n1c == cIS || n1c == cSY
                  || n1c == cBK || n1c == cCR || n1c == cLF || n1c == cNL
                  || n1c == cZW) then false                                        -- LB15b
        else if pc == cSP && cc == cIS && n1c == cNU then true                     -- LB15c
        else if cc == cIS then false                                               -- LB15d
        else if (ns == cCL || ns == cCP) && cc == cNS then false                   -- LB16
        else if ns == cB2 && cc == cB2 then false                                  -- LB17
        else if pc == cSP then true                                                -- LB18
        else if cc == cQU && !c.pi then false                                      -- LB19
        else if pc == cQU && !p.pf then false                                      -- LB19
        else if cc == cQU && !p.ea then false                                      -- LB19a
        else if cc == cQU && (n1c == sot || !n1.ea) then false                     -- LB19a
        else if pc == cQU && !c.ea then false                                      -- LB19a
        else if pc == cQU && (u == 1 || !pp.ea) then false                         -- LB19a
        else if cc == cCB || pc == cCB then true                                   -- LB20
        else if isHyph pc && isALHL cc
                && (ppc == sot || ppc == cBK || ppc == cCR || ppc == cLF || ppc == cNL
                    || ppc == cSP || ppc == cZW || ppc == cCB || ppc == cGL) then false  -- LB20a
        else if cc == cBA || cc == cHH || cc == cHY || cc == cNS then false         -- LB21
        else if pc == cBB then false                                               -- LB21
        else if ppc == cHL && isHyph pc && cc != cHL then false                    -- LB21a
        else if pc == cSY && cc == cHL then false                                  -- LB21b
        else if cc == cIN then false                                               -- LB22
        else if isALHL pc && cc == cNU then false                                  -- LB23
        else if pc == cNU && isALHL cc then false                                  -- LB23
        else if pc == cPR && (cc == cID || cc == cEB || cc == cEM) then false      -- LB23a
        else if (pc == cID || pc == cEB || pc == cEM) && cc == cPO then false      -- LB23a
        else if (pc == cPR || pc == cPO) && isALHL cc then false                   -- LB24
        else if isALHL pc && (cc == cPR || cc == cPO) then false                   -- LB24
        else if nuClose && (cc == cPO || cc == cPR) then false                     -- LB25
        else if nuRun && (cc == cPO || cc == cPR) then false                       -- LB25
        else if pc == cPO && cc == cOP && (n1c == cNU || (n1c == cIS && n2c == cNU)) then false
        else if pc == cPO && cc == cNU then false                                  -- LB25
        else if pc == cPR && cc == cOP && (n1c == cNU || (n1c == cIS && n2c == cNU)) then false
        else if pc == cPR && cc == cNU then false                                  -- LB25
        else if pc == cHY && cc == cNU then false                                  -- LB25
        else if pc == cIS && cc == cNU then false                                  -- LB25
        else if nuRun && cc == cNU then false                                      -- LB25
        else if pc == cJL && (cc == cJL || cc == cJV || cc == cH2 || cc == cH3) then false  -- LB26
        else if (pc == cJV || pc == cH2) && (cc == cJV || cc == cJT) then false    -- LB26
        else if (pc == cJT || pc == cH3) && cc == cJT then false                   -- LB26
        else if isJamo pc && cc == cPO then false                                  -- LB27
        else if pc == cPR && isJamo cc then false                                  -- LB27
        else if isALHL pc && isALHL cc then false                                  -- LB28
        else if pc == cAP && (cc == cAK || cc == cAS || (cc == cAL && c.dc)) then false  -- LB28a
        else if isAkAs p && (cc == cVF || cc == cVI) then false                    -- LB28a
        else if pc == cVI && isAkAs pp && (cc == cAK || (cc == cAL && c.dc)) then false  -- LB28a
        else if isAkAs p && isAkAs c && n1c == cVF then false                      -- LB28a
        else if pc == cIS && isALHL cc then false                                  -- LB29
        else if (isALHL pc || pc == cNU) && cc == cOP && !c.ea then false          -- LB30
        else if pc == cCP && !p.ea && (isALHL cc || cc == cNU) then false          -- LB30
        else if pc == cRI && cc == cRI && riCount % 2 == 1 then false              -- LB30a
        else if pc == cEB && cc == cEM then false                                  -- LB30b
        else if p.epCn && cc == cEM then false                                     -- LB30b
        else true                                                                  -- LB31
      flags := flags.set! c.start brk
    -- update the state with unit c
    let cc := c.cls
    let prevCls := if u > 0 then (us[u - 1]!).cls else sot
    nuClose := (cc == cCL || cc == cCP) && nuRun
    nuRun := cc == cNU || (nuRun && (cc == cSY || cc == cIS))
    riCount := if cc == cRI then riCount + 1 else 0
    if cc != cSP then
      nsPre := prevCls
      ns := cc
      nsPi := c.pi
  return flags

/-- Positions (counts of code points before the break) where a line break is
allowed or mandatory, increasing; the end of the text is always listed (LB3)
and position 0 never (LB2). Empty text has no position. -/
def breaks (cs : Array Char) : Array Nat :=
  if cs.size = 0 then #[]
  else
    let fl := breakFlags cs
    ((Array.range cs.size).filter fun i => 0 < i && fl.getD i false).push cs.size

#guard breaks #[] == #[]
#guard breaks #['a'] == #[1]
#guard breaks #['a', ' ', 'b'] == #[2, 3]
#guard breaks #['a', 'b'] == #[2]
#guard breaks #['\n', 'a'] == #[1, 2]
#guard breaks #['\r', '\n'] == #[2]
#guard breaks #['1', ',', '2'] == #[3]
#guard breaks #['a', '̈', ' ', 'b'] == #[3, 4]
#guard breaks #['​', ' ', 'a'] == #[2, 3]

end L4Factoidal.Unicode.LineBreak
