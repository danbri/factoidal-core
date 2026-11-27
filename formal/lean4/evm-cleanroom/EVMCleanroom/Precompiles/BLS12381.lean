import EVMCleanroom.Precompiles.Pairing

/-!
# BLS12-381 operations (precompiles 0x0b–0x11, EIP-2537)

G1 addition, G1 multi-scalar multiplication, G2 addition, G2 multi-scalar
multiplication, pairing check, and the two map-to-curve operations.

Curve `y² = x³ + 4` over the 381-bit prime `p`; `G2` on the M-type twist
`y² = x³ + 4(1 + u)` over `Fp2 = Fp[u]/(u² + 1)`; the groups have prime order
`r`; the curve parameter is `x = −0xd201000000010000`.

Encoding (EIP-2537). A field element is 64 big-endian bytes whose top 16 bytes
are zero and whose value is below `p`. An `Fp2` element is `c0 ‖ c1`. A `G1`
point is `x ‖ y` (128 bytes), a `G2` point 256 bytes; all zero bytes encode the
point at infinity. Scalars are 32 bytes and are not reduced. Every operation
has an exact or per-item input length and an empty variable-length input is an
error. Additions check only that points are on the curve; multi-scalar
multiplication and pairing also require the order-`r` subgroup.

Map to curve (RFC 9380): simplified SWU on the isogenous curve, the 11-isogeny
(G1) or 3-isogeny (G2) to the curve, then multiplication by the effective
cofactor. The isogeny coefficients and discount tables below were generated
from the published RFC and EIP texts.

Prices: 375 (G1 add), 600 (G2 add), `k · 12000 · discount(k) / 1000` and
`k · 22500 · discount(k) / 1000` for the multi-scalar operations,
`37700 + 32600 k` for the pairing check, 5500 and 23800 for the maps.

Proved: input-length rules, gas accounting, output lengths, the number of
loop iterations per priced item. Not proved: group laws, bilinearity, or that
the map is the RFC's (guards below and the published vectors).
-/

namespace EVMCleanroom.Precompiles.BLS12381

def p : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
def r : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
/-- Absolute value of the (negative) curve parameter. -/
def parameter : Nat := 0xd201000000010000

def field : FieldOps Nat := Fp.ops p
def field2 : FieldOps Fp2 := Fp2.ops p
def tower : Tower := Tower.make p ⟨1, 1⟩
def twistB : Fp2 := ⟨4, 4⟩

def curve : PairingCurve :=
  { tower, r, twist := .multiply, loop := parameter, frobeniusSteps := false, negative := true,
    hardDigits := hardDigitsOf p r }

def g1Generator : Nat × Nat :=
  (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

def g2Generator : Fp2 × Fp2 :=
  (⟨0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
    0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e⟩,
   ⟨0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
    0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be⟩)

/-- EIP-2537 MSM discount table for G1, for `k = 1 … 128` pairs. -/
def g1Discounts : Array Nat := #[
  1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677,
  673, 669, 665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627,
  625, 623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598,
  596, 595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576,
  575, 574, 573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
  558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548, 547, 547, 546, 545, 544,
  543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532, 532, 531,
  530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519]

/-- EIP-2537 MSM discount table for G2, for `k = 1 … 128` pairs. -/
def g2Discounts : Array Nat := #[
  1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
  711, 704, 699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
  643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
  606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
  580, 579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
  561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
  546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
  534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524]

/-! ### Isogeny constants (RFC 9380, appendices E.2 and E.3), lowest degree first -/

def iso1XNum : Array Nat := #[
  0x11a05f2b1e833340b809101dd99815856b303e88a2d7005ff2627b56cdb4e2c85610c2d5f2e62d6eaeac1662734649b7,
  0x17294ed3e943ab2f0588bab22147a81c7c17e75b2f6a8417f565e33c70d1e86b4838f2a6f318c356e834eef1b3cb83bb,
  0xd54005db97678ec1d1048c5d10a9a1bce032473295983e56878e501ec68e25c958c3e3d2a09729fe0179f9dac9edcb0,
  0x1778e7166fcc6db74e0609d307e55412d7f5e4656a8dbf25f1b33289f1b330835336e25ce3107193c5b388641d9b6861,
  0xe99726a3199f4436642b4b3e4118e5499db995a1257fb3f086eeb65982fac18985a286f301e77c451154ce9ac8895d9,
  0x1630c3250d7313ff01d1201bf7a74ab5db3cb17dd952799b9ed3ab9097e68f90a0870d2dcae73d19cd13c1c66f652983,
  0xd6ed6553fe44d296a3726c38ae652bfb11586264f0f8ce19008e218f9c86b2a8da25128c1052ecaddd7f225a139ed84,
  0x17b81e7701abdbe2e8743884d1117e53356de5ab275b4db1a682c62ef0f2753339b7c8f8c8f475af9ccb5618e3f0c88e,
  0x80d3cf1f9a78fc47b90b33563be990dc43b756ce79f5574a2c596c928c5d1de4fa295f296b74e956d71986a8497e317,
  0x169b1f8e1bcfa7c42e0c37515d138f22dd2ecb803a0c5c99676314baf4bb1b7fa3190b2edc0327797f241067be390c9e,
  0x10321da079ce07e272d8ec09d2565b0dfa7dccdde6787f96d50af36003b14866f69b771f8c285decca67df3f1605fb7b,
  0x6e08c248e260e70bd1e962381edee3d31d79d7e22c837bc23c0bf1bc24c6b68c24b1b80b64d391fa9c8ba2e8ba2d229]

def iso1XDen : Array Nat := #[
  0x8ca8d548cff19ae18b2e62f4bd3fa6f01d5ef4ba35b48ba9c9588617fc8ac62b558d681be343df8993cf9fa40d21b1c,
  0x12561a5deb559c4348b4711298e536367041e8ca0cf0800c0126c2588c48bf5713daa8846cb026e9e5c8276ec82b3bff,
  0xb2962fe57a3225e8137e629bff2991f6f89416f5a718cd1fca64e00b11aceacd6a3d0967c94fedcfcc239ba5cb83e19,
  0x3425581a58ae2fec83aafef7c40eb545b08243f16b1655154cca8abc28d6fd04976d5243eecf5c4130de8938dc62cd8,
  0x13a8e162022914a80a6f1d5f43e7a07dffdfc759a12062bb8d6b44e833b306da9bd29ba81f35781d539d395b3532a21e,
  0xe7355f8e4e667b955390f7f0506c6e9395735e9ce9cad4d0a43bcef24b8982f7400d24bc4228f11c02df9a29f6304a5,
  0x772caacf16936190f3e0c63e0596721570f5799af53a1894e2e073062aede9cea73b3538f0de06cec2574496ee84a3a,
  0x14a7ac2a9d64a8b230b3f5b074cf01996e7f63c21bca68a81996e1cdf9822c580fa5b9489d11e2d311f7d99bbdcc5a5e,
  0xa10ecf6ada54f825e920b3dafc7a3cce07f8d1d7161366b74100da67f39883503826692abba43704776ec3a79a1d641,
  0x95fc13ab9e92ad4476d6e3eb3a56680f682b4ee96f7d03776df533978f31c1593174e4b4b7865002d6384d168ecdd0a]

def iso1YNum : Array Nat := #[
  0x90d97c81ba24ee0259d1f094980dcfa11ad138e48a869522b52af6c956543d3cd0c7aee9b3ba3c2be9845719707bb33,
  0x134996a104ee5811d51036d776fb46831223e96c254f383d0f906343eb67ad34d6c56711962fa8bfe097e75a2e41c696,
  0xcc786baa966e66f4a384c86a3b49942552e2d658a31ce2c344be4b91400da7d26d521628b00523b8dfe240c72de1f6,
  0x1f86376e8981c217898751ad8746757d42aa7b90eeb791c09e4a3ec03251cf9de405aba9ec61deca6355c77b0e5f4cb,
  0x8cc03fdefe0ff135caf4fe2a21529c4195536fbe3ce50b879833fd221351adc2ee7f8dc099040a841b6daecf2e8fedb,
  0x16603fca40634b6a2211e11db8f0a6a074a7d0d4afadb7bd76505c3d3ad5544e203f6326c95a807299b23ab13633a5f0,
  0x4ab0b9bcfac1bbcb2c977d027796b3ce75bb8ca2be184cb5231413c4d634f3747a87ac2460f415ec961f8855fe9d6f2,
  0x987c8d5333ab86fde9926bd2ca6c674170a05bfe3bdd81ffd038da6c26c842642f64550fedfe935a15e4ca31870fb29,
  0x9fc4018bd96684be88c9e221e4da1bb8f3abd16679dc26c1e8b6e6a1f20cabe69d65201c78607a360370e577bdba587,
  0xe1bba7a1186bdb5223abde7ada14a23c42a0ca7915af6fe06985e7ed1e4d43b9b3f7055dd4eba6f2bafaaebca731c30,
  0x19713e47937cd1be0dfd0b8f1d43fb93cd2fcbcb6caf493fd1183e416389e61031bf3a5cce3fbafce813711ad011c132,
  0x18b46a908f36f6deb918c143fed2edcc523559b8aaf0c2462e6bfe7f911f643249d9cdf41b44d606ce07c8a4d0074d8e,
  0xb182cac101b9399d155096004f53f447aa7b12a3426b08ec02710e807b4633f06c851c1919211f20d4c04f00b971ef8,
  0x245a394ad1eca9b72fc00ae7be315dc757b3b080d4c158013e6632d3c40659cc6cf90ad1c232a6442d9d3f5db980133,
  0x5c129645e44cf1102a159f748c4a3fc5e673d81d7e86568d9ab0f5d396a7ce46ba1049b6579afb7866b1e715475224b,
  0x15e6be4e990f03ce4ea50b3b42df2eb5cb181d8f84965a3957add4fa95af01b2b665027efec01c7704b456be69c8b604]

def iso1YDen : Array Nat := #[
  0x16112c4c3a9c98b252181140fad0eae9601a6de578980be6eec3232b5be72e7a07f3688ef60c206d01479253b03663c1,
  0x1962d75c2381201e1a0cbd6c43c348b885c84ff731c4d59ca4a10356f453e01f78a4260763529e3532f6102c2e49a03d,
  0x58df3306640da276faaae7d6e8eb15778c4855551ae7f310c35a5dd279cd2eca6757cd636f96f891e2538b53dbf67f2,
  0x16b7d288798e5395f20d23bf89edb4d1d115c5dbddbcd30e123da489e726af41727364f2c28297ada8d26d98445f5416,
  0xbe0e079545f43e4b00cc912f8228ddcc6d19c9f0f69bbb0542eda0fc9dec916a20b15dc0fd2ededda39142311a5001d,
  0x8d9e5297186db2d9fb266eaac783182b70152c65550d881c5ecd87b6f0f5a6449f38db9dfa9cce202c6477faaf9b7ac,
  0x166007c08a99db2fc3ba8734ace9824b5eecfdfa8d0cf8ef5dd365bc400a0051d5fa9c01a58b1fb93d1a1399126a775c,
  0x16a3ef08be3ea7ea03bcddfabba6ff6ee5a4375efa1f4fd7feb34fd206357132b920f5b00801dee460ee415a15812ed9,
  0x1866c8ed336c61231a1be54fd1d74cc4f9fb0ce4c6af5920abc5750c4bf39b4852cfe2f7bb9248836b233d9d55535d4a,
  0x167a55cda70a6e1cea820597d94a84903216f763e13d87bb5308592e7ea7d4fbc7385ea3d529b35e346ef48bb8913f55,
  0x4d2f259eea405bd48f010a01ad2911d9c6dd039bb61a6290e591b36e636a5c871a5c29f4f83060400f8b49cba8f6aa8,
  0xaccbb67481d033ff5852c1e48c50c477f94ff8aefce42d28c0f9a88cea7913516f968986f7ebbea9684b529e2561092,
  0xad6b9514c767fe3c3613144b45f1496543346d98adf02267d5ceef9a00d9b8693000763e3b90ac11e99b138573345cc,
  0x2660400eb2e4f3b628bdd0d53cd76f2bf565b94e72927c1cb748df27942480e420517bd8714cc80d1fadc1326ed06f7,
  0xe0fa1d816ddc03e6b24255e0d7819c171c40f65e273b853324efcd6356caa205ca2f570f13497804415473a1d634b8f]

def iso2XNum : Array Fp2 := #[
  ⟨0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6,
   0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6⟩,
  ⟨0x0,
   0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a⟩,
  ⟨0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e,
   0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d⟩,
  ⟨0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1,
   0x0⟩]

def iso2XDen : Array Fp2 := #[
  ⟨0x0,
   0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63⟩,
  ⟨0xc,
   0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f⟩]

def iso2YNum : Array Fp2 := #[
  ⟨0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706,
   0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706⟩,
  ⟨0x0,
   0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be⟩,
  ⟨0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c,
   0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f⟩,
  ⟨0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10,
   0x0⟩]

def iso2YDen : Array Fp2 := #[
  ⟨0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb,
   0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb⟩,
  ⟨0x0,
   0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3⟩,
  ⟨0x12,
   0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99⟩]

/-! ### Square roots -/

/-- A checked square root in `Fp2` (`p ≡ 3 mod 4`, `u² = −1`), `none` for a non-square.
    For `a = a0 + a1 u` with `a1 ≠ 0`: with `s² = a0² + a1²`, one of `(a0 ± s)/2` is a
    square `x0²`, and `x1 = a1 / (2 x0)`. The result is verified by squaring. -/
def sqrt2? (a : Fp2) : Option Fp2 :=
  let candidate : Option Fp2 :=
    if a.c1 = 0 then
      match Fp.sqrt? p a.c0 with
      | some root => some ⟨root, 0⟩
      | none => (Fp.sqrt? p (Fp.neg p a.c0)).map fun root => ⟨0, root⟩
    else
      match Fp.sqrt? p ((a.c0 * a.c0 + a.c1 * a.c1) % p) with
      | none => none
      | some s =>
        let half := Fp.inv p 2
        let pick (t : Nat) : Option Fp2 :=
          (Fp.sqrt? p t).map fun x0 => ⟨x0, Fp.mul p a.c1 (Fp.inv p (2 * x0 % p))⟩
        match pick (Fp.mul p (Fp.add p a.c0 s) half) with
        | some root => some root
        | none => pick (Fp.mul p (Fp.sub p a.c0 s) half)
  match candidate with
  | some root => if Fp2.sqr p root == a then some root else none
  | none => none

/-! ### Decoding and encoding -/

/-- A 64-byte field element: top 16 bytes zero, value below `p`. -/
def decodeFp (data : ByteArray) (off : Nat) : Option Nat :=
  if !allZero data off 16 then none
  else
    let value := beNat data (off + 16) 48
    if value < p then some value else none

def decodeFp2 (data : ByteArray) (off : Nat) : Option Fp2 :=
  match decodeFp data off, decodeFp data (off + 64) with
  | some c0, some c1 => some ⟨c0, c1⟩
  | _, _ => none

def inSubgroup1 (x y : Nat) : Bool :=
  Curve.isInfinity field (Curve.mul field r (Curve.ofAffine field x y))

def inSubgroup2 (x y : Fp2) : Bool :=
  Curve.isInfinity field2 (Curve.mul field2 r (Curve.ofAffine field2 x y))

/-- Decode a `G1` point; the outer `none` is invalid input, the inner `none` infinity. -/
def decodeG1 (data : ByteArray) (off : Nat) (subgroup : Bool) : Option (Option (Nat × Nat)) :=
  match decodeFp data off, decodeFp data (off + 64) with
  | some x, some y =>
    if x = 0 ∧ y = 0 then some none
    else if !Curve.onCurve field 4 x y then none
    else if subgroup && !inSubgroup1 x y then none
    else some (some (x, y))
  | _, _ => none

def decodeG2 (data : ByteArray) (off : Nat) (subgroup : Bool) : Option (Option (Fp2 × Fp2)) :=
  match decodeFp2 data off, decodeFp2 data (off + 128) with
  | some x, some y =>
    if Fp2.isZero x ∧ Fp2.isZero y then some none
    else if !Curve.onCurve field2 twistB x y then none
    else if subgroup && !inSubgroup2 x y then none
    else some (some (x, y))
  | _, _ => none

def jacobian1 : Option (Nat × Nat) → JPoint Nat
  | none => Curve.infinity field
  | some (x, y) => Curve.ofAffine field x y

def jacobian2 : Option (Fp2 × Fp2) → JPoint Fp2
  | none => Curve.infinity field2
  | some (x, y) => Curve.ofAffine field2 x y

def encodeG1 (point : JPoint Nat) : ByteArray :=
  match Curve.toAffine field point with
  | none => natToBE 128 0
  | some (x, y) => natToBE 64 x ++ natToBE 64 y

def encodeG2 (point : JPoint Fp2) : ByteArray :=
  match Curve.toAffine field2 point with
  | none => natToBE 256 0
  | some (x, y) => natToBE 64 x.c0 ++ natToBE 64 x.c1 ++ natToBE 64 y.c0 ++ natToBE 64 y.c1

theorem encodeG1_size (point : JPoint Nat) : (encodeG1 point).size = 128 := by
  unfold encodeG1
  split
  · exact natToBE_size _ _
  · simp [ByteArray.size_append, natToBE_size]

theorem encodeG2_size (point : JPoint Fp2) : (encodeG2 point).size = 256 := by
  unfold encodeG2
  split
  · exact natToBE_size _ _
  · simp [ByteArray.size_append, natToBE_size]

/-! ### Addition and multi-scalar multiplication -/

def g1AddBody (data : ByteArray) : Body :=
  match decodeG1 data 0 false, decodeG1 data 128 false with
  | some a, some b => .output (encodeG1 (Curve.add field (jacobian1 a) (jacobian1 b)))
  | _, _ => .invalid

def g2AddBody (data : ByteArray) : Body :=
  match decodeG2 data 0 false, decodeG2 data 256 false with
  | some a, some b => .output (encodeG2 (Curve.add field2 (jacobian2 a) (jacobian2 b)))
  | _, _ => .invalid

/-- Precompile 0x0b. -/
def runG1Add (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 256 then .failure else charge gas 375 fun _ => g1AddBody input

/-- Precompile 0x0d. -/
def runG2Add (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 512 then .failure else charge gas 600 fun _ => g2AddBody input

def discount (table : Array Nat) (cap k : Nat) : Nat :=
  if k = 0 then 0 else if k ≤ 128 then table[k - 1]! else cap

def msmGas (table : Array Nat) (cap perItem itemBytes size : Nat) : Nat :=
  let k := size / itemBytes
  k * perItem * discount table cap k / 1000

/-- Sum of `[scalarᵢ] Pᵢ` over `count` items of 160 bytes; one scalar multiplication per item. -/
def g1MsmLoop (data : ByteArray) : Nat → Nat → JPoint Nat → Option (JPoint Nat)
  | 0, _, acc => some acc
  | count+1, off, acc =>
    match decodeG1 data off true with
    | none => none
    | some point =>
      g1MsmLoop data count (off + 160)
        (Curve.add field acc (Curve.mul field (beNat data (off + 128) 32) (jacobian1 point)))

def g2MsmLoop (data : ByteArray) : Nat → Nat → JPoint Fp2 → Option (JPoint Fp2)
  | 0, _, acc => some acc
  | count+1, off, acc =>
    match decodeG2 data off true with
    | none => none
    | some point =>
      g2MsmLoop data count (off + 288)
        (Curve.add field2 acc (Curve.mul field2 (beNat data (off + 256) 32) (jacobian2 point)))

def g1MsmBody (input : ByteArray) : Body :=
  match g1MsmLoop input (input.size / 160) 0 (Curve.infinity field) with
  | some sum => .output (encodeG1 sum)
  | none => .invalid

def g2MsmBody (input : ByteArray) : Body :=
  match g2MsmLoop input (input.size / 288) 0 (Curve.infinity field2) with
  | some sum => .output (encodeG2 sum)
  | none => .invalid

/-- Precompile 0x0c. -/
def runG1Msm (gas : Nat) (input : ByteArray) : Result :=
  if input.size = 0 ∨ input.size % 160 ≠ 0 then .failure
  else charge gas (msmGas g1Discounts 519 12000 160 input.size) fun _ => g1MsmBody input

/-- Precompile 0x0e. -/
def runG2Msm (gas : Nat) (input : ByteArray) : Result :=
  if input.size = 0 ∨ input.size % 288 ≠ 0 then .failure
  else charge gas (msmGas g2Discounts 524 22500 288 input.size) fun _ => g2MsmBody input

/-! ### Pairing check -/

def pairingGas (size : Nat) : Nat := 37700 + 32600 * (size / 384)

def decodePairs (data : ByteArray) :
    Nat → Nat → List (Pairing.G1 × Pairing.G2) → Option (List (Pairing.G1 × Pairing.G2))
  | 0, _, acc => some acc
  | count+1, off, acc =>
    match decodeG1 data off true, decodeG2 data (off + 128) true with
    | some a, some b =>
      match a, b with
      | some a, some b => decodePairs data count (off + 384) ((a, b) :: acc)
      | _, _ => decodePairs data count (off + 384) acc
    | _, _ => none

def pairingBody (input : ByteArray) : Body :=
  match decodePairs input (input.size / 384) 0 [] with
  | none => .invalid
  | some pairs => .output (natToBE 32 (if Pairing.productIsOne curve pairs then 1 else 0))

/-- Precompile 0x0f. -/
def runPairing (gas : Nat) (input : ByteArray) : Result :=
  if input.size = 0 ∨ input.size % 384 ≠ 0 then .failure
  else charge gas (pairingGas input.size) fun _ => pairingBody input

/-! ### Map to curve -/

/-- Horner evaluation; `coefficients` are lowest degree first. -/
def horner {F : Type} (O : FieldOps F) (coefficients : Array F) (x : F) : F :=
  coefficients.foldr (fun c acc => O.add (O.mul acc x) c) O.zero

/-- Simplified SWU (RFC 9380, section 6.6.2) onto `y² = x³ + A x + B`. -/
def swu {F : Type} (O : FieldOps F) (sqrt? : F → Option F) (sgn0 : F → Nat) (A B Z u : F) : F × F :=
  let zu2 := O.mul Z (O.sqr u)
  let tv1 := O.inv (O.add (O.sqr zu2) zu2)
  let x1 :=
    if O.isZero tv1 then O.mul B (O.inv (O.mul Z A))
    else O.mul (O.mul (O.neg B) (O.inv A)) (O.add O.one tv1)
  let g (x : F) : F := O.add (O.add (O.mul (O.sqr x) x) (O.mul A x)) B
  let (x, y) :=
    match sqrt? (g x1) with
    | some y => (x1, y)
    | none =>
      let x2 := O.mul zu2 x1
      (x2, (sqrt? (g x2)).getD O.zero)
  (x, if sgn0 u != sgn0 y then O.neg y else y)

/-- Apply an isogeny given by four polynomials; a zero denominator maps to infinity. -/
def isogeny {F : Type} (O : FieldOps F) (xNum xDen yNum yDen : Array F) (point : F × F) : JPoint F :=
  let xd := horner O (xDen.push O.one) point.1
  let yd := horner O (yDen.push O.one) point.1
  if O.isZero xd || O.isZero yd then Curve.infinity O
  else
    Curve.ofAffine O (O.mul (horner O xNum point.1) (O.inv xd))
      (O.mul point.2 (O.mul (horner O yNum point.1) (O.inv yd)))

def sgn0 (a : Nat) : Nat := a % 2
def sgn02 (a : Fp2) : Nat := if a.c0 % 2 = 1 ∨ (a.c0 = 0 ∧ a.c1 % 2 = 1) then 1 else 0

def swuA1 : Nat :=
  0x144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d
def swuB1 : Nat :=
  0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0
def cofactor1 : Nat := 0xd201000000010001
def cofactor2 : Nat :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551

def mapToG1 (u : Nat) : JPoint Nat :=
  Curve.mul field cofactor1
    (isogeny field iso1XNum iso1XDen iso1YNum iso1YDen (swu field (Fp.sqrt? p) sgn0 swuA1 swuB1 11 u))

def mapToG2 (u : Fp2) : JPoint Fp2 :=
  Curve.mul field2 cofactor2
    (isogeny field2 iso2XNum iso2XDen iso2YNum iso2YDen
      (swu field2 sqrt2? sgn02 ⟨0, 240⟩ ⟨1012, 1012⟩ (Fp2.neg p ⟨2, 1⟩) u))

def mapG1Body (input : ByteArray) : Body :=
  match decodeFp input 0 with
  | some u => .output (encodeG1 (mapToG1 u))
  | none => .invalid

def mapG2Body (input : ByteArray) : Body :=
  match decodeFp2 input 0 with
  | some u => .output (encodeG2 (mapToG2 u))
  | none => .invalid

/-- Precompile 0x10. -/
def runMapG1 (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 64 then .failure else charge gas 5500 fun _ => mapG1Body input

/-- Precompile 0x11. -/
def runMapG2 (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 128 then .failure else charge gas 23800 fun _ => mapG2Body input

/-! ### Contracts -/

/-- Shared shape of the fixed-length operations: wrong length fails; success has the
    exact price. -/
private theorem fixed_success (size price gas : Nat) (input out : ByteArray) (left : Nat)
    (body : ByteArray → Body)
    (h : (if input.size ≠ size then Result.failure else charge gas price fun _ => body input) =
      .success out left) :
    input.size = size ∧ body input = .output out ∧ left + price = gas := by
  split at h
  · cases h
  · rename_i hSize
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    exact ⟨by omega, hBody, hGas⟩

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful G1 addition had exactly 256 input bytes, cost exactly 375 gas and
    returned exactly 128 bytes.
    Does not say: the bytes encode the group sum (vectors, not proved). -/
theorem runG1Add_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG1Add gas input = .success out left) :
    input.size = 256 ∧ out.size = 128 ∧ left + 375 = gas := by
  have ⟨hSize, hBody, hGas⟩ := fixed_success 256 375 gas input out left g1AddBody h
  refine ⟨hSize, ?_, hGas⟩
  simp only [g1AddBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG1_size _
  · exact Body.noConfusion hBody

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful G2 addition had exactly 512 input bytes, cost exactly 600 gas and
    returned exactly 256 bytes.
    Does not say: the bytes encode the group sum (vectors, not proved). -/
theorem runG2Add_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG2Add gas input = .success out left) :
    input.size = 512 ∧ out.size = 256 ∧ left + 600 = gas := by
  have ⟨hSize, hBody, hGas⟩ := fixed_success 512 600 gas input out left g2AddBody h
  refine ⟨hSize, ?_, hGas⟩
  simp only [g2AddBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG2_size _
  · exact Body.noConfusion hBody

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful map of a field element to G1 had exactly 64 input bytes, cost 5500
    gas and returned 128 bytes; the map to G2 had 128 input bytes, cost 23800 and
    returned 256 bytes.
    Does not say: the point is the RFC 9380 image (vectors, not proved). -/
theorem runMap_success (gas : Nat) (input out : ByteArray) (left : Nat) :
    (runMapG1 gas input = .success out left → input.size = 64 ∧ out.size = 128 ∧ left + 5500 = gas) ∧
    (runMapG2 gas input = .success out left → input.size = 128 ∧ out.size = 256 ∧ left + 23800 = gas) := by
  constructor
  · intro h
    have ⟨hSize, hBody, hGas⟩ := fixed_success 64 5500 gas input out left mapG1Body h
    refine ⟨hSize, ?_, hGas⟩
    simp only [mapG1Body] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG1_size _
    · exact Body.noConfusion hBody
  · intro h
    have ⟨hSize, hBody, hGas⟩ := fixed_success 128 23800 gas input out left mapG2Body h
    refine ⟨hSize, ?_, hGas⟩
    simp only [mapG2Body] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG2_size _
    · exact Body.noConfusion hBody

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful G1 multi-scalar multiplication had a non-empty input of whole
    160-byte items, cost exactly the discounted price for that many items, and returned
    128 bytes. The loop ran once per item (`g1MsmLoop` recurses on the item count).
    Does not say: the bytes encode the group sum (vectors, not proved). -/
theorem runG1Msm_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG1Msm gas input = .success out left) :
    input.size ≠ 0 ∧ input.size % 160 = 0 ∧ out.size = 128 ∧
      left + msmGas g1Discounts 519 12000 160 input.size = gas := by
  unfold runG1Msm at h
  split at h
  · cases h
  · rename_i hLen
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨by omega, by omega, ?_, hGas⟩
    simp only [g1MsmBody] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG1_size _
    · exact Body.noConfusion hBody

theorem runG2Msm_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG2Msm gas input = .success out left) :
    input.size ≠ 0 ∧ input.size % 288 = 0 ∧ out.size = 256 ∧
      left + msmGas g2Discounts 524 22500 288 input.size = gas := by
  unfold runG2Msm at h
  split at h
  · cases h
  · rename_i hLen
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨by omega, by omega, ?_, hGas⟩
    simp only [g2MsmBody] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG2_size _
    · exact Body.noConfusion hBody

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful pairing check had a non-empty input of whole 384-byte pairs, cost
    exactly 37700 + 32600 per pair and returned exactly 32 bytes.
    Does not say: the verdict is correct (vectors, not proved). -/
theorem runPairing_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runPairing gas input = .success out left) :
    input.size ≠ 0 ∧ input.size % 384 = 0 ∧ out.size = 32 ∧ left + pairingGas input.size = gas := by
  unfold runPairing at h
  split at h
  · cases h
  · rename_i hLen
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨by omega, by omega, ?_, hGas⟩
    simp only [pairingBody] at hBody
    split at hBody
    · exact Body.noConfusion hBody
    · exact Body.output.inj hBody ▸ natToBE_size _ _

/-- Kind: input-length rule.
    Says: an empty input fails for every variable-length operation, at any gas.
    Does not say: anything about non-empty input. -/
theorem empty_input_fails (gas : Nat) (input : ByteArray) (h : input.size = 0) :
    runG1Msm gas input = .failure ∧ runG2Msm gas input = .failure ∧ runPairing gas input = .failure := by
  simp [runG1Msm, runG2Msm, runPairing, h]

private def g1 : JPoint Nat := Curve.ofAffine field g1Generator.1 g1Generator.2
private def g2 : JPoint Fp2 := Curve.ofAffine field2 g2Generator.1 g2Generator.2
private def affine1 (k : Nat) : Nat × Nat := (Curve.toAffine field (Curve.mul field k g1)).getD (0, 0)
private def affine2 (k : Nat) : Fp2 × Fp2 :=
  (Curve.toAffine field2 (Curve.mul field2 k g2)).getD (Fp2.zero, Fp2.zero)

-- The BLS12 polynomials at the parameter give r and p (x is negative, so odd powers flip sign).
#guard r == parameter ^ 4 - parameter ^ 2 + 1
#guard 3 * p == (parameter + 1) ^ 2 * r + 3 * 0 - 3 * parameter || p == ((parameter + 1) ^ 2 * r) / 3 - parameter
#guard (p ^ 4 - p ^ 2 + 1) % r == 0 && (p - 1) % 6 == 0 && p % 4 == 3
#guard g1Discounts.size == 128 && g2Discounts.size == 128
-- Discounts lie between the cap and 1000 and never increase with the item count.
#guard g1Discounts.all (fun d => 519 ≤ d && d ≤ 1000) && g2Discounts.all (fun d => 524 ≤ d && d ≤ 1000)
#guard (List.range 127).all fun k => g1Discounts[k + 1]! ≤ g1Discounts[k]! && g2Discounts[k + 1]! ≤ g2Discounts[k]!
#guard iso1XNum.size == 12 && iso1XDen.size == 10 && iso1YNum.size == 16 && iso1YDen.size == 15
#guard iso2XNum.size == 4 && iso2XDen.size == 2 && iso2YNum.size == 4 && iso2YDen.size == 3
#guard Curve.onCurve field 4 g1Generator.1 g1Generator.2
#guard Curve.onCurve field2 twistB g2Generator.1 g2Generator.2
#guard inSubgroup1 g1Generator.1 g1Generator.2 && inSubgroup2 g2Generator.1 g2Generator.2
#guard sqrt2? (Fp2.sqr p ⟨5, 7⟩) |>.map (Fp2.sqr p) |> (· == some (Fp2.sqr p ⟨5, 7⟩))
#guard (sqrt2? (Fp2.sqr p ⟨0, 7⟩)).isSome && (sqrt2? (Fp2.sqr p ⟨9, 0⟩)).isSome
-- Tower algebra and the pairing: inverse, Frobenius, order, non-degeneracy, bilinearity.
private def sample : Fp12 := Pairing.miller curve g1Generator g2Generator
#guard Fp12.mul tower sample (Fp12.inv tower sample) == Fp12.one
#guard Fp12.frobenius tower sample == Fp12.pow tower sample p
#guard Pairing.hardPart curve sample == Fp12.pow tower sample ((p ^ 4 - p ^ 2 + 1) / r)
private def e11 : Fp12 := Pairing.pairing curve g1Generator g2Generator
#guard e11 != Fp12.one
#guard Fp12.pow tower e11 r == Fp12.one
#guard Pairing.pairing curve (affine1 5) g2Generator == Fp12.pow tower e11 5
#guard Pairing.pairing curve g1Generator (affine2 7) == Fp12.pow tower e11 7
#guard Pairing.productIsOne curve
  [(g1Generator, g2Generator), ((g1Generator.1, p - g1Generator.2), g2Generator)]
#guard !Pairing.productIsOne curve [(g1Generator, g2Generator)]
-- The maps land in the prime-order subgroups.
#guard (Curve.toAffine field (mapToG1 1)).all fun (x, y) => Curve.onCurve field 4 x y && inSubgroup1 x y
#guard (Curve.toAffine field2 (mapToG2 ⟨1, 2⟩)).all fun (x, y) =>
  Curve.onCurve field2 twistB x y && inSubgroup2 x y
#guard discount g1Discounts 519 1 == 1000 && discount g1Discounts 519 128 == 519 &&
  discount g1Discounts 519 129 == 519 && discount g2Discounts 524 2 == 1000
#guard msmGas g1Discounts 519 12000 160 160 == 12000 && msmGas g1Discounts 519 12000 160 320 == 22776
#guard msmGas g2Discounts 524 22500 288 288 == 22500 && pairingGas 384 == 70300

#print axioms encodeG1_size
#print axioms encodeG2_size
#print axioms fixed_success
#print axioms runG1Add_success
#print axioms runG2Add_success
#print axioms runMap_success
#print axioms runG1Msm_success
#print axioms runG2Msm_success
#print axioms runPairing_success
#print axioms empty_input_fails

end EVMCleanroom.Precompiles.BLS12381
